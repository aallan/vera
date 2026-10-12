"""scripts/render_lists.py, which writes the lists that have one source.

Two lists are rendered between `render_lists` markers: the built-in effect
names, from the registry `vera effects --json` publishes, into the editor
grammars and the two extension READMEs; and the limitation tables, from
`limitations.json`, into KNOWN_ISSUES.md and the documents that repeat
them.  Each renderer is checked on a synthetic tree whose names and orders
cannot coincide with the shipped ones: a fixture renders to the expected
block, `--check` is red on a stale block and green after `--write`, a
second `--write` changes nothing, and one more entry in a source changes
exactly the blocks that source feeds.  The regex grammars are held to the
property their rendering order exists for: no effect name is shadowed by
its prefix.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import plistlib
import re
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parent.parent
_SCRIPT = ROOT / "scripts" / "render_lists.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("render_lists_under_test", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RL = _load()

VSCODE = "editors/vscode/syntaxes/vera.tmLanguage.json"
TEXTMATE = "editors/textmate/Vera.tmbundle/Syntaxes/Vera.tmLanguage"
VIM = "editors/vim-veralang/syntax/veralang.vim"
VSCODE_README = "editors/vscode/README.md"
TEXTMATE_README = "editors/textmate/README.md"

# Not the files' stale names, not in sorted order, and with a shared
# prefix, so a renderer that kept the old list, sorted it for itself, or
# let `Http` shadow `HttpServer` gives a different answer.
EFFECTS = ["Beta", "Http", "Alpha", "HttpServer"]


# ---------------------------------------------------------------------------
# A synthetic tree
# ---------------------------------------------------------------------------

_PLIST_HEAD = (
    '<?xml version="1.0" encoding="UTF-8"?>\n'
    '<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"'
    ' "http://www.apple.com/DTDs/PropertyList-1.0.dtd">\n'
    '<plist version="1.0">\n'
)

_EFFECT_FILES = {
    VSCODE: (
        "{\n"
        '\t"patterns": [\n'
        "\t\t{\n"
        '\t\t\t"comment": "render_lists:effects",\n'
        '\t\t\t"name": "entity.name.type.effect.vera",\n'
        '\t\t\t"match": "\\\\b(Stale|Old)\\\\b"\n'
        "\t\t},\n"
        "\t\t{\n"
        '\t\t\t"name": "keyword.other.vera",\n'
        '\t\t\t"match": "\\\\b(fn)\\\\b"\n'
        "\t\t}\n"
        "\t]\n"
        "}\n"
    ),
    TEXTMATE: (
        _PLIST_HEAD
        + "<dict>\n"
        "\t<key>patterns</key>\n"
        "\t<array>\n"
        "\t\t<!-- Built-in effects -->\n"
        "\t\t<!-- render_lists:begin effects -->\n"
        "\t\t<dict>\n"
        "\t\t\t<key>name</key>\n"
        "\t\t\t<string>entity.name.type.effect.vera</string>\n"
        "\t\t\t<key>match</key>\n"
        "\t\t\t<string>\\b(Stale|Old)\\b</string>\n"
        "\t\t</dict>\n"
        "\t\t<!-- render_lists:end effects -->\n"
        "\t</array>\n"
        "</dict>\n"
        "</plist>\n"
    ),
    VIM: (
        '" Built-in effects\n'
        '" render_lists:begin effects\n'
        "syntax keyword veraEffectType Stale Old\n"
        '" render_lists:end effects\n'
        "syntax match veraTypeRef '\\<[A-Z][A-Za-z0-9_]*\\>'\n"
    ),
    VSCODE_README: (
        "**Syntax highlighting**:\n\n"
        "- **Slots** — highlighted.\n"
        "  <!-- render_lists:begin effects -->\n"
        "- **Effects** — built-in effects (`Stale`, `Old`) and calls"
        " (`IO.print`, `Exn.throw`) are highlighted.\n"
        "  <!-- render_lists:end effects -->\n"
        "- **Holes** — highlighted.\n"
    ),
    TEXTMATE_README: (
        "## What gets highlighted\n\n"
        "<!-- render_lists:begin effects -->\n"
        "**Effects** — built-in effects (`Stale`, `Old`) are recognised.\n"
        "<!-- render_lists:end effects -->\n\n"
        "**Other features.**\n"
    ),
}

_LINK = "[#{n}](https://github.com/aallan/vera/issues/{n})"

_DATA: dict[str, Any] = {
    "about": "A fixture.",
    "tables": [
        {
            "table": "DOC.md#limitations",
            "header": "| Limitation | Issue |",
            "rule": "|---|---|",
            "issue_column": 1,
            "rows": ["10", "none"],
        },
        {
            "table": "sub/OTHER.md#limitations",
            "header": "| Limitation | Issue | Notes |",
            "rule": "|--|--|--|",
            "issue_column": 1,
            "rows": ["pair", "10"],
        },
    ],
    "limitations": [
        {
            "id": "10",
            "issues": [10],
            "rows": {
                "DOC.md#limitations": ["Ten, at length."],
                "sub/OTHER.md#limitations": ["Ten", "a note on ten"],
            },
        },
        {
            "id": "none",
            "issues": [],
            "rows": {"DOC.md#limitations": ["Deliberate behaviour, `a \\| b`."]},
        },
        {
            "id": "pair",
            "issues": [21, 22],
            "rows": {"sub/OTHER.md#limitations": ["Two at once", "both"]},
        },
    ],
}

_DOCS = {
    "DOC.md": (
        "# Doc\n\n"
        "## Limitations\n\n"
        "Prose before the table.\n\n"
        "<!-- render_lists:begin limitations -->\n"
        "| stale |\n"
        "<!-- render_lists:end limitations -->\n\n"
        "## After\n"
    ),
    "sub/OTHER.md": (
        "## Other\n\n"
        "<!-- render_lists:begin limitations -->\n"
        "<!-- render_lists:end limitations -->\n"
    ),
}

_DOC_BLOCK = (
    "| Limitation | Issue |\n"
    "|---|---|\n"
    f"| Ten, at length. | {_LINK.format(n=10)} |\n"
    "| Deliberate behaviour, `a \\| b`. | — |\n"
)
_OTHER_BLOCK = (
    "| Limitation | Issue | Notes |\n"
    "|--|--|--|\n"
    f"| Two at once | {_LINK.format(n=21)}, {_LINK.format(n=22)} | both |\n"
    f"| Ten | {_LINK.format(n=10)} | a note on ten |\n"
)

_ALL_FILES = {**_EFFECT_FILES, **_DOCS}


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _tree(root: Path, data: dict[str, Any] | None = None) -> Path:
    for rel, text in _ALL_FILES.items():
        _write(root / rel, text)
    _write(root / "limitations.json", json.dumps(data or _DATA, indent=2) + "\n")
    return root


def _snapshot(root: Path) -> dict[str, bytes]:
    return {
        p.relative_to(root).as_posix(): p.read_bytes()
        for p in sorted(root.rglob("*")) if p.is_file()
    }


def _rendered(blocks: list[Any]) -> dict[tuple[str, str], str]:
    return {(b.path, b.name): b.new for b in blocks}


def _effect_rules(node: Any) -> list[str]:
    """Every `match` of a rule scoped `entity.name.type.effect.vera`."""
    found: list[str] = []
    if isinstance(node, dict):
        if node.get("name") == "entity.name.type.effect.vera" and "match" in node:
            found.append(str(node["match"]))
        for value in node.values():
            found += _effect_rules(value)
    elif isinstance(node, list):
        for value in node:
            found += _effect_rules(value)
    return found


def _effect_regex(path: str, text: str) -> str:
    """The effect rule's pattern, read the way the editor reads the file:
    as JSON, or as a property list (which the markers must leave valid)."""
    if path.endswith(".json"):
        tree = json.loads(text)
    else:
        tree = plistlib.loads(text.encode("utf-8"))
    (pattern,) = _effect_rules(tree)
    return pattern


def _assert_unshadowed(pattern: str, names: list[str]) -> None:
    """Each name matches as itself: through the whole pattern, and through
    its alternation alone, without the word boundaries around it, so the
    order is what keeps `Http` from taking the start of `HttpServer`."""
    group = re.fullmatch(r"\\b\((.*)\)\\b", pattern)
    assert group is not None, pattern
    bare = re.compile(f"(?:{group.group(1)})")
    for name in names:
        assert re.findall(pattern, name) == [name], (pattern, name)
        found = bare.match(name)
        assert found is not None and found.group(0) == name, (group.group(1), name)


# ---------------------------------------------------------------------------
# Markers
# ---------------------------------------------------------------------------


class TestMarkers:
    def test_a_block_is_the_lines_between_its_markers(self) -> None:
        text = "a\n<!-- render_lists:begin x -->\nb\nc\n<!-- render_lists:end x -->\nd\n"
        spans = RL.read_blocks(text, "f.md")
        assert isinstance(spans, dict)
        start, end = spans["x"]
        assert text[start:end] == "b\nc\n"

    def test_a_vim_block_uses_vim_comments(self) -> None:
        text = '" render_lists:begin x\nsyntax keyword K A\n" render_lists:end x\n'
        spans = RL.read_blocks(text, "f.vim")
        assert isinstance(spans, dict)
        start, end = spans["x"]
        assert text[start:end] == "syntax keyword K A\n"

    def test_the_json_anchor_block_is_the_rest_of_its_object(self) -> None:
        """JSON has no comments, so the marker is a TextMate `comment` key
        and the block runs from the key to the end of its rule."""
        text = _EFFECT_FILES[VSCODE]
        spans = RL.read_blocks(text, "g.json")
        assert isinstance(spans, dict)
        start, end = spans["effects"]
        assert text[start:end] == (
            '\t\t\t"name": "entity.name.type.effect.vera",\n'
            '\t\t\t"match": "\\\\b(Stale|Old)\\\\b"\n'
        )

    @pytest.mark.parametrize(
        ("text", "reason"),
        [
            ("<!-- render_lists:end x -->\n", "begin marker is missing"),
            ("<!-- render_lists:begin x -->\n", "end marker is missing"),
            (
                "<!-- render_lists:begin x -->\n<!-- render_lists:begin x -->\n"
                "<!-- render_lists:end x -->\n",
                "appears twice",
            ),
            ("<!-- render_lists:end x -->\n<!-- render_lists:begin x -->\n", "before"),
            ("prose naming render_lists:begin x inline\n", "line of its own"),
        ],
    )
    def test_markers_it_cannot_read_are_refused(self, text: str, reason: str) -> None:
        spans = RL.read_blocks(text, "f.md")
        assert isinstance(spans, str)
        assert reason in spans

    def test_a_block_the_renderer_does_not_know_is_refused(self, tmp_path: Path) -> None:
        """A misspelt or leftover block in a target file is an error, not a
        block nothing renders."""
        root = _tree(tmp_path)
        doc = root / "DOC.md"
        doc.write_text(
            doc.read_text(encoding="utf-8")
            + "<!-- render_lists:begin limitation -->\n"
            "<!-- render_lists:end limitation -->\n",
            encoding="utf-8",
        )
        _blocks, errors = RL.plan(root, effects=EFFECTS)
        assert any("`limitation`" in e and "DOC.md" in e for e in errors), errors


# ---------------------------------------------------------------------------
# The effect list
# ---------------------------------------------------------------------------


class TestEffects:
    def test_each_target_renders_the_registry(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        blocks, errors = RL.effect_blocks(root, EFFECTS)
        assert errors == []
        assert _rendered(blocks) == {
            (VSCODE, "effects"): (
                '\t\t\t"name": "entity.name.type.effect.vera",\n'
                '\t\t\t"match": "\\\\b(Beta|HttpServer|Http|Alpha)\\\\b"\n'
            ),
            (TEXTMATE, "effects"): (
                "\t\t<dict>\n"
                "\t\t\t<key>name</key>\n"
                "\t\t\t<string>entity.name.type.effect.vera</string>\n"
                "\t\t\t<key>match</key>\n"
                "\t\t\t<string>\\b(Beta|HttpServer|Http|Alpha)\\b</string>\n"
                "\t\t</dict>\n"
            ),
            (VIM, "effects"): "syntax keyword veraEffectType Beta Http Alpha HttpServer\n",
            (VSCODE_README, "effects"): (
                "- **Effects** — built-in effects (`Beta`, `Http`, `Alpha`,"
                " `HttpServer`) and calls (`IO.print`, `Exn.throw`) are"
                " highlighted.\n"
            ),
            (TEXTMATE_README, "effects"): (
                "**Effects** — built-in effects (`Beta`, `Http`, `Alpha`,"
                " `HttpServer`) are recognised.\n"
            ),
        }

    @pytest.mark.parametrize(
        ("names", "order"),
        [
            (["Http", "HttpServer"], ["HttpServer", "Http"]),
            (["HttpServer", "Http"], ["HttpServer", "Http"]),
            (["A", "AB", "ABC", "B"], ["ABC", "AB", "A", "B"]),
            (["B", "A", "AB"], ["B", "AB", "A"]),
            (["Zed", "Alpha"], ["Zed", "Alpha"]),
        ],
    )
    def test_a_longer_name_comes_before_its_prefix(
        self, names: list[str], order: list[str]
    ) -> None:
        """And nothing else moves: the registry's order stands wherever no
        name is another's prefix."""
        assert RL.alternation_order(names) == order

    @pytest.mark.parametrize("path", [VSCODE, TEXTMATE])
    def test_no_name_is_shadowed_in_a_rendered_regex(self, path: str, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        _files, errors = RL.write(root, effects=EFFECTS)
        assert errors == []
        pattern = _effect_regex(path, (root / path).read_text(encoding="utf-8"))
        _assert_unshadowed(pattern, EFFECTS)
        assert re.findall(pattern, "HttpServer.serve") == ["HttpServer"]
        assert re.findall(pattern, "Http.get") == ["Http"]

    @pytest.mark.parametrize("path", [VSCODE, TEXTMATE])
    def test_no_name_is_shadowed_in_a_shipped_grammar(self, path: str) -> None:
        """`Http` does not match inside `HttpServer`, `HttpServer` does not
        swallow `Http`, and every name the shipped grammar lists matches as
        itself.  The names are the grammar's own: whether they are the
        registry's is the release's freshness check, not this one's."""
        pattern = _effect_regex(path, (ROOT / path).read_text(encoding="utf-8"))
        group = re.fullmatch(r"\\b\((.*)\)\\b", pattern)
        assert group is not None, pattern
        names = group.group(1).split("|")
        assert {"Http", "HttpServer"} <= set(names)
        _assert_unshadowed(pattern, names)
        assert re.findall(pattern, "HttpServer") == ["HttpServer"]
        assert re.findall(pattern, "Http") == ["Http"]
        assert re.findall(pattern, "Https") == []

    @pytest.mark.parametrize(
        ("path", "old", "new"),
        [
            (VSCODE_README, "(`Stale`, `Old`)", "Stale and Old"),
            (TEXTMATE_README, "(`Stale`, `Old`)", "(`Stale`, `Old`) or (`Stale`)"),
            (VIM, "syntax keyword veraEffectType Stale Old", "syntax keyword veraOther Stale"),
            (TEXTMATE, "<string>\\b(Stale|Old)\\b</string>", "<string>Stale</string>"),
            (VSCODE, '"match": "\\\\b(Stale|Old)\\\\b"', '"match": "Stale"'),
        ],
    )
    def test_a_block_without_one_effect_list_is_refused(
        self, path: str, old: str, new: str, tmp_path: Path
    ) -> None:
        root = _tree(tmp_path)
        target = root / path
        text = target.read_text(encoding="utf-8")
        assert old in text
        target.write_text(text.replace(old, new), encoding="utf-8")
        _blocks, errors = RL.effect_blocks(root, EFFECTS)
        assert any(path in e and "effect list" in e for e in errors), errors

    def test_one_more_effect_changes_each_effect_block_by_that_name(
        self, tmp_path: Path
    ) -> None:
        """The registry feeds five blocks: one more effect changes each of
        them, by that name and nothing else, and no limitation table."""
        root = _tree(tmp_path)
        before, errors = RL.plan(root, effects=EFFECTS)
        assert errors == []
        after, errors = RL.plan(root, effects=[*EFFECTS, "Gamma"])
        assert errors == []
        old, new = _rendered(before), _rendered(after)
        changed = {key for key in old if old[key] != new[key]}
        assert changed == {(p, "effects") for p in _EFFECT_FILES}
        for key in changed:
            assert "Gamma" in new[key]
            assert re.sub(r"\|Gamma|, `Gamma`| Gamma", "", new[key]) == old[key], key

    @pytest.mark.parametrize(
        "rel",
        [
            "editors/helix/syntax/vera.toml",
            "editors/emacs/vera-mode.el",
            "editors/zed/queries/highlights.scm",
            "editors/sublime/Vera.sublime-syntax",
            "editors/zed/vera.tmLanguage.json",
        ],
    )
    def test_an_unlisted_grammar_is_refused(self, rel: str, tmp_path: Path) -> None:
        """A new grammar nobody added to the targets would carry a list
        nothing renders, so it fails rather than shipping unrendered."""
        root = _tree(tmp_path)
        assert RL.effect_blocks(root, EFFECTS)[1] == []
        _write(root / rel, "no effect names here\n")
        _blocks, errors = RL.effect_blocks(root, EFFECTS)
        assert any(rel in e for e in errors), errors

    def test_discovery_finds_exactly_the_shipped_grammars(self) -> None:
        """Discovery must not flag every file under editors/ (the Vim
        ftplugin and ftdetect files, the READMEs, the extension's code)."""
        assert sorted(RL.discovered_grammars(ROOT)) == sorted(RL.GRAMMARS)

    def test_every_effect_target_is_in_the_tree(self) -> None:
        for rel in RL.EFFECT_TARGETS:
            assert (ROOT / rel).is_file(), rel

    def test_the_registry_is_read_from_the_tree_being_rendered(
        self, tmp_path: Path
    ) -> None:
        """`scripts/` is not a package, so a bare `import vera` resolves
        through site-packages, which from a worktree is another checkout.
        Run as a script inside a tree whose `vera` lists `Gamma`, the
        renderer must render `Gamma`.  In-process `vera` is already
        imported, so only a subprocess can show it."""
        root = _tree(tmp_path)
        _write(root / "scripts" / "render_lists.py", _SCRIPT.read_text(encoding="utf-8"))
        _write(root / "vera" / "__init__.py", "")
        _write(
            root / "vera" / "introspect.py",
            "def effects_payload():\n"
            f"    names = {[*EFFECTS, 'Gamma']!r}\n"
            '    return {"items": [{"name": n, "kind": "effect"} for n in names]\n'
            '            + [{"name": "Eq", "kind": "ability"}]}\n',
        )
        env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
        env["PYTHONIOENCODING"] = "utf-8"

        def run(flag: str) -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [sys.executable, str(root / "scripts" / "render_lists.py"), flag],
                capture_output=True, text=True, encoding="utf-8", env=env,
                cwd=root, timeout=120, check=False,
            )

        stale = run("--check")
        assert stale.returncode == 1, stale.stdout + stale.stderr
        assert VSCODE in stale.stderr and "DOC.md" in stale.stderr
        written = run("--write")
        assert written.returncode == 0, written.stdout + written.stderr
        vim = (root / VIM).read_text(encoding="utf-8")
        assert "Gamma" in vim and "Eq" not in vim
        fresh = run("--check")
        assert fresh.returncode == 0, fresh.stdout + fresh.stderr


# ---------------------------------------------------------------------------
# The limitation tables
# ---------------------------------------------------------------------------


def _edit_table(i: int, key: str, value: Any) -> Callable[[dict[str, Any]], None]:
    def edit(data: dict[str, Any]) -> None:
        data["tables"][i][key] = value
    return edit


def _edit_record(i: int, key: str, value: Any) -> Callable[[dict[str, Any]], None]:
    def edit(data: dict[str, Any]) -> None:
        data["limitations"][i][key] = value
    return edit


def _edit_top(key: str, value: Any) -> Callable[[dict[str, Any]], None]:
    def edit(data: dict[str, Any]) -> None:
        data[key] = value
    return edit


# (what is wrong, the edit, a phrase the error names)
_INVALID = [
    ("an unknown top-level key", _edit_top("extra", 1), "extra"),
    ("a row naming no record", _edit_table(0, "rows", ["10", "none", "ghost"]), "ghost"),
    ("a row listed twice", _edit_table(0, "rows", ["10", "10", "none"]), "twice"),
    ("a record a table does not list", _edit_table(1, "rows", ["pair"]), "does not list"),
    ("a table with no rows", _edit_table(0, "rows", []), "no rows"),
    ("a table id without a block", _edit_table(0, "table", "DOC.md"), "DOC.md"),
    ("an issue column off the table", _edit_table(0, "issue_column", 2), "issue_column"),
    ("a rule of the wrong width", _edit_table(0, "rule", "|---|"), "rule"),
    ("a header that is not a row", _edit_table(0, "header", "Limitation, Issue"), "header"),
    ("too few cells", _edit_record(1, "rows", {"DOC.md#limitations": []}), "cells"),
    ("an unescaped pipe in a cell", _edit_record(1, "rows", {"DOC.md#limitations": ["a | b"]}), "pipe"),
    (
        "cells for a table that does not exist",
        _edit_record(2, "rows", {"NOPE.md#limitations": ["x", "y"]}),
        "NOPE.md",
    ),
    ("an issue that is not a number", _edit_record(0, "issues", ["10"]), "issues"),
    ("an issue below one", _edit_record(0, "issues", [0]), "issues"),
    ("an issue twice", _edit_record(2, "issues", [21, 21]), "issues"),
    ("a record nothing carries", _edit_record(2, "rows", {}), "pair"),
    ("an id twice", _edit_record(1, "id", "10"), "twice"),
]


class TestLimitations:
    def test_each_table_renders_its_rows_in_its_own_order(self, tmp_path: Path) -> None:
        """A record two tables carry shows each its own cells, at each
        table's own position; no issue is a dash; two are joined."""
        root = _tree(tmp_path)
        blocks, errors = RL.limitation_blocks(root)
        assert errors == []
        assert _rendered(blocks) == {
            ("DOC.md", "limitations"): _DOC_BLOCK,
            ("sub/OTHER.md", "limitations"): _OTHER_BLOCK,
        }

    def test_one_more_record_changes_exactly_one_block(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        before = _rendered(RL.limitation_blocks(root)[0])
        data = copy.deepcopy(_DATA)
        data["limitations"].append(
            {"id": "30", "issues": [30], "rows": {"sub/OTHER.md#limitations": ["Thirty", "new"]}}
        )
        data["tables"][1]["rows"].insert(1, "30")
        _write(root / "limitations.json", json.dumps(data, indent=2) + "\n")
        blocks, errors = RL.limitation_blocks(root)
        assert errors == []
        after = _rendered(blocks)
        assert after[("DOC.md", "limitations")] == before[("DOC.md", "limitations")]
        old = before[("sub/OTHER.md", "limitations")].splitlines()
        new = after[("sub/OTHER.md", "limitations")].splitlines()
        assert new == [*old[:3], f"| Thirty | {_LINK.format(n=30)} | new |", *old[3:]]

    @pytest.mark.parametrize(
        ("edit", "reason"),
        [(edit, reason) for _what, edit, reason in _INVALID],
        ids=[what for what, _edit, _reason in _INVALID],
    )
    def test_the_data_is_validated(
        self, edit: Callable[[dict[str, Any]], None], reason: str, tmp_path: Path
    ) -> None:
        data = copy.deepcopy(_DATA)
        edit(data)
        root = _tree(tmp_path, data)
        blocks, errors = RL.limitation_blocks(root)
        assert blocks == [] and errors, "the edit was accepted"
        assert any(reason in e for e in errors), errors

    def test_an_unreadable_data_file_is_one_error(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        (root / "limitations.json").write_text("{ not json", encoding="utf-8")
        blocks, errors = RL.limitation_blocks(root)
        assert blocks == []
        assert len(errors) == 1 and "limitations.json" in errors[0]

    def test_a_table_whose_markers_are_missing_is_refused(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        (root / "sub" / "OTHER.md").write_text("## Other\n", encoding="utf-8")
        _blocks, errors = RL.limitation_blocks(root)
        assert any("sub/OTHER.md" in e and "begin marker is missing" in e for e in errors), errors

    def test_a_table_whose_document_is_missing_is_refused(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        (root / "sub" / "OTHER.md").rename(root / "sub" / "MOVED.md")
        _blocks, errors = RL.limitation_blocks(root)
        assert any("sub/OTHER.md" in e and "no such file" in e for e in errors), errors

    def test_the_shipped_data_names_only_tables_that_exist(self) -> None:
        """Every table the shipped file names is a block in its document,
        and every record is readable.  Whether a block is current is the
        release's question, not this one's."""
        blocks, errors = RL.limitation_blocks(ROOT)
        assert errors == []
        assert {b.path for b in blocks} == {
            "KNOWN_ISSUES.md", "vera/README.md", "spec/08-modules.md",
            "spec/09-standard-library.md", "spec/12-runtime.md", "SKILL.md",
            "LSP_SERVER.md",
        }


# ---------------------------------------------------------------------------
# --check and --write
# ---------------------------------------------------------------------------


class TestCheckAndWrite:
    def test_check_is_red_on_a_stale_tree_and_green_after_write(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        stale = RL.stale_blocks(root, effects=EFFECTS)
        assert len(stale) == len(_ALL_FILES), stale
        assert any(VSCODE in s for s in stale) and any("sub/OTHER.md" in s for s in stale)
        files, errors = RL.write(root, effects=EFFECTS)
        assert errors == [] and sorted(files) == sorted(_ALL_FILES)
        assert RL.stale_blocks(root, effects=EFFECTS) == []

    def test_one_stale_block_is_the_one_reported(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        RL.write(root, effects=EFFECTS)
        doc = root / "DOC.md"
        doc.write_text(
            doc.read_text(encoding="utf-8").replace("Ten, at length.", "Ten, edited by hand."),
            encoding="utf-8",
        )
        (stale,) = RL.stale_blocks(root, effects=EFFECTS)
        assert "DOC.md" in stale and "`limitations`" in stale
        assert "Ten, edited by hand." in stale

    def test_a_second_write_changes_nothing(self, tmp_path: Path) -> None:
        root = _tree(tmp_path)
        RL.write(root, effects=EFFECTS)
        once = _snapshot(root)
        assert RL.write(root, effects=EFFECTS) == ([], [])
        assert _snapshot(root) == once
        for rel in _ALL_FILES:
            assert "render_lists:" in (root / rel).read_text(encoding="utf-8"), rel

    def test_only_the_blocks_change(self, tmp_path: Path) -> None:
        """Every line outside a block survives a write byte for byte."""
        root = _tree(tmp_path)
        blocks, errors = RL.plan(root, effects=EFFECTS)
        assert errors == [] and len(blocks) == len(_ALL_FILES)
        RL.write(root, effects=EFFECTS)
        for block in blocks:
            original = _ALL_FILES[block.path]
            start, end = RL.read_blocks(original, block.path)[block.name]
            assert original[start:end] == block.current
            text = (root / block.path).read_text(encoding="utf-8")
            assert text == original[:start] + block.new + original[end:]

    def test_a_refused_block_writes_nothing(self, tmp_path: Path) -> None:
        """One error anywhere and no file is written, so a half-rendered
        tree never reaches a commit."""
        root = _tree(tmp_path)
        (root / VIM).write_text("no markers\n", encoding="utf-8")
        before = _snapshot(root)
        files, errors = RL.write(root, effects=EFFECTS)
        assert files == [] and errors
        assert _snapshot(root) == before

    def test_the_shipped_tree_is_readable(self) -> None:
        """Every target in the tree is found and rendered without an error,
        against the live registry."""
        blocks, errors = RL.plan(ROOT)
        assert errors == []
        assert len({(b.path, b.name) for b in blocks}) == len(blocks) == 12
