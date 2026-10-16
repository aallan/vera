#!/usr/bin/env python
"""Write the lists that have one source into the files that show them.

A list has one source and is rendered, never copied.  Four lists are
rendered here, each between a pair of `render_lists` markers in the file
that shows it:

- ``effects``: the built-in effect names, from the registry ``vera effects
  --json`` publishes, into the editor grammars under ``editors/`` (the
  vscode and TextMate grammars' effect rule, the Vim ``veraEffectType``
  keywords) and the two extension READMEs that name them.  They are in the
  registry's order, except that in a regex alternation a name comes before
  any name that is its prefix, so ``Http`` cannot shadow ``HttpServer``.
  Within an effect block only the list is rewritten; the words around it
  are the file's own.
- ``limitations``: the limitation tables, from ``limitations.json``, into
  KNOWN_ISSUES.md and the documents that repeat it.  Each record in that
  file is one limitation: the issues it cites, and the cells each table
  that carries it shows, the Issue column apart.  Each table names its
  records in the order it shows them, and the Issue column is written from
  the record's issues.  KNOWN_ISSUES.md's Bugs table and SKILL.md's bug
  workarounds are hand-kept, and are not in the file.
- ``host-imports``: the host imports a module can declare, from the built-in
  registry's ``HOST_IMPORTS`` (``vera/builtins.py``), into the browser
  runtime's roster (``vera/browser/runtime.mjs``), which its import object
  holds every module's imports to.
- ``signatures-*``: the signature tables of spec chapter 9, from the
  registry's records and the effects' operations (``vera effects``).  Within
  a table only each row's Signature cell is written; its name and its
  description are the spec's own.

A marker is a whole line in the file's own comment syntax:
``<!-- render_lists:begin NAME -->`` and ``<!-- render_lists:end NAME -->``
in Markdown and XML, ``" render_lists:begin NAME`` in Vim script,
``// render_lists:begin NAME`` in JavaScript.  JSON has
no comments, so the vscode grammar's marker is its effect rule's TextMate
``comment`` key, ``"comment": "render_lists:NAME"``, and the block is the
rest of that rule.

``--write`` renders every block, and writes nothing at all when any block
cannot be rendered.  ``--check`` writes nothing and exits 1 naming each
block that is not what ``--write`` would write.  ``check_doc_counts.py
--release`` runs the check, so a release cannot ship a stale block; between
releases nothing compares a block with its source.

Everything but the registries is read with the standard library, so
``check_limitations_sync.py`` can load the data file through this module on
a bare Python.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import sys
from collections.abc import Sequence
from pathlib import Path
from typing import Any, NamedTuple

ROOT = Path(__file__).resolve().parent.parent
DATA = "limitations.json"
ISSUES_URL = "https://github.com/aallan/vera/issues/"


class Rendered(NamedTuple):
    """One block: where it is, what it holds now, and what it should hold."""

    path: str
    name: str
    current: str
    new: str


# ---------------------------------------------------------------------------
# Markers
# ---------------------------------------------------------------------------

_BLOCK_NAME = r"[a-z][a-z0-9-]*"
_MARKERS = {
    "html": re.compile(rf"<!--\s*render_lists:(begin|end)\s+({_BLOCK_NAME})\s*-->"),
    "vim": re.compile(rf'"\s*render_lists:(begin|end)\s+({_BLOCK_NAME})'),
    "json": re.compile(rf'"comment":\s*"render_lists:({_BLOCK_NAME})",?'),
    "js": re.compile(rf"//\s*render_lists:(begin|end)\s+({_BLOCK_NAME})"),
}


def _syntax(path: str) -> str:
    if path.endswith(".json"):
        return "json"
    if path.endswith(".vim"):
        return "vim"
    if path.endswith((".mjs", ".js")):
        return "js"
    return "html"


def _times(count: int) -> str:
    return {0: "is missing", 2: "appears twice"}.get(count, f"appears {count} times")


def read_blocks(text: str, path: str) -> dict[str, tuple[int, int]] | str:
    """Every block in `text`, by name: the offsets of its content, from the
    line after its begin marker to the start of its end marker; or why the
    markers cannot be read.

    Any line that names ``render_lists:`` must be a marker on a line of its
    own, and each block has one begin and one end marker, begin first.  A
    JSON block has its ``comment`` key for a begin marker and runs to the
    line that closes its rule.
    """
    syntax = _syntax(path)
    marker = _MARKERS[syntax]
    lines = text.splitlines(keepends=True)
    offsets = list(itertools.accumulate((len(line) for line in lines), initial=0))
    begins: dict[str, list[int]] = {}
    ends: dict[str, list[int]] = {}
    for index, line in enumerate(lines):
        if "render_lists:" not in line:
            continue
        found = marker.fullmatch(line.strip())
        if found is None:
            return (
                f"line {index + 1} names `render_lists:` but is not a marker on a"
                f" line of its own: {line.strip()[:100]!r}"
            )
        if syntax == "json":
            begins.setdefault(found.group(1), []).append(index)
        else:
            kind, name = found.groups()
            (begins if kind == "begin" else ends).setdefault(name, []).append(index)
    spans: dict[str, tuple[int, int]] = {}
    for name in sorted(set(begins) | set(ends)):
        opened = begins.get(name, [])
        if len(opened) != 1:
            return f"the `{name}` block's begin marker {_times(len(opened))}"
        begin = opened[0]
        if syntax == "json":
            end = next(
                (i for i in range(begin + 1, len(lines)) if lines[i].strip().startswith("}")),
                None,
            )
            if end is None:
                return f"the `{name}` block's rule never closes"
            if any("{" in line for line in lines[begin + 1 : end]):
                return f"the `{name}` block's rule holds a nested object"
        else:
            closed = ends.get(name, [])
            if len(closed) != 1:
                return f"the `{name}` block's end marker {_times(len(closed))}"
            end = closed[0]
            if end < begin:
                return f"the `{name}` block's end marker comes before its begin marker"
        spans[name] = (offsets[begin + 1], offsets[end])
    return spans


def _begin_example(path: str, name: str) -> str:
    return {
        "html": f"<!-- render_lists:begin {name} -->",
        "vim": f'" render_lists:begin {name}',
        "json": f'"comment": "render_lists:{name}"',
        "js": f"// render_lists:begin {name}",
    }[_syntax(path)]


def _read(root: Path, path: str, names: set[str]) -> tuple[str, dict[str, tuple[int, int]]] | str:
    """A target file's text and blocks, or why it cannot be rendered: it is
    missing, its markers cannot be read, or a block it must hold is not
    there."""
    file = root / path
    if not file.is_file():
        return f"{path}: no such file"
    text = file.read_text(encoding="utf-8")
    spans = read_blocks(text, path)
    if isinstance(spans, str):
        return f"{path}: {spans}"
    for name in sorted(names - set(spans)):
        return (
            f"{path}: the `{name}` block's begin marker is missing; the block"
            f" opens with `{_begin_example(path, name)}`"
        )
    return text, spans


# ---------------------------------------------------------------------------
# The effect list
# ---------------------------------------------------------------------------

# Each file that names the effects, and how it spells the list.
EFFECT_TARGETS = {
    "editors/vscode/syntaxes/vera.tmLanguage.json": "json-regex",
    "editors/textmate/Vera.tmbundle/Syntaxes/Vera.tmLanguage": "plist-regex",
    "editors/vim-veralang/syntax/veralang.vim": "vim-keywords",
    "editors/vscode/README.md": "prose",
    "editors/textmate/README.md": "prose",
}
GRAMMARS = tuple(path for path, style in EFFECT_TARGETS.items() if style != "prose")

_NAME = r"[A-Z][A-Za-z0-9_]*"
# Where the list stands inside a block.  Exactly one match per block.
_LISTS = {
    "json-regex": re.compile(
        rf'(?<="match": "\\\\b\()({_NAME}(?:\|{_NAME})*)(?=\)\\\\b")'
    ),
    "plist-regex": re.compile(
        rf"(?<=<string>\\b\()({_NAME}(?:\|{_NAME})*)(?=\)\\b</string>)"
    ),
    "vim-keywords": re.compile(
        rf"(?<=^syntax keyword veraEffectType )({_NAME}(?: {_NAME})*)$", re.M
    ),
    "prose": re.compile(rf"(?<=\()(`{_NAME}`(?:, `{_NAME}`)*)(?=\))"),
}

# A grammar under `editors/` that is not a target would carry a list
# nothing renders.  A file qualifies if it sits in a `syntax`/`syntaxes`
# directory, where all three grammars live, or carries a grammar
# extension; `.tmlanguage.json` is listed beside `.tmlanguage` because the
# match is on the whole name, and `.scm` catches the tree-sitter editors,
# whose highlight queries live in `queries/`.
_GRAMMAR_DIRS = frozenset({"syntax", "syntaxes"})
_GRAMMAR_SUFFIXES = (".tmlanguage", ".tmlanguage.json", ".sublime-syntax", ".el", ".scm")


def effect_names() -> list[str]:
    """The built-in effects, abilities excluded, in the order `vera effects
    --json` lists them.  The caller puts the tree's root first on
    `sys.path`, so these are the tree's own effects."""
    from vera.introspect import effects_payload

    items = effects_payload()["items"]
    assert isinstance(items, list)
    return [str(item["name"]) for item in items if item["kind"] == "effect"]


def alternation_order(names: Sequence[str]) -> list[str]:
    """`names` with each name moved before the first name that is its proper
    prefix, and nothing else moved, so that no alternative in a regex
    alternation can match the start of a longer one."""
    placed: list[str] = []
    for name in names:
        at = next(
            (i for i, other in enumerate(placed) if other != name and name.startswith(other)),
            None,
        )
        if at is None:
            placed.append(name)
        else:
            placed.insert(at, name)
    return placed


def _effect_list(style: str, names: Sequence[str]) -> str:
    if style in ("json-regex", "plist-regex"):
        return "|".join(alternation_order(names))
    if style == "vim-keywords":
        return " ".join(names)
    return ", ".join(f"`{name}`" for name in names)


def discovered_grammars(root: Path) -> list[str]:
    """Files under ``editors/`` that look like a syntax grammar, repo-relative."""
    found: list[str] = []
    for path in sorted((root / "editors").rglob("*")):
        if not path.is_file():
            continue
        in_syntax_dir = path.parent.name.lower() in _GRAMMAR_DIRS
        if in_syntax_dir or path.name.lower().endswith(_GRAMMAR_SUFFIXES):
            found.append(path.relative_to(root).as_posix())
    return found


def effect_blocks(root: Path, names: Sequence[str]) -> tuple[list[Rendered], list[str]]:
    """Each effect block as it is and as the registry's `names` render it,
    and every reason a block cannot be rendered."""
    errors: list[str] = []
    if not names:
        errors.append("the effect registry lists no effect")
    errors += [
        f"the effect registry lists `{name}`, which is not an effect name"
        for name in names if not re.fullmatch(_NAME, name)
    ]
    errors += [
        f"the effect registry lists `{name}` twice"
        for name in sorted({n for n in names if list(names).count(n) > 1})
    ]
    blocks: list[Rendered] = []
    for path, style in EFFECT_TARGETS.items():
        read = _read(root, path, {"effects"})
        if isinstance(read, str):
            errors.append(read)
            continue
        text, spans = read
        start, end = spans["effects"]
        content = text[start:end]
        found = list(_LISTS[style].finditer(content))
        if len(found) != 1:
            errors.append(
                f"{path}: the `effects` block holds {len(found)} effect lists where"
                " it should hold one"
            )
            continue
        span = found[0]
        new = content[: span.start()] + _effect_list(style, names) + content[span.end() :]
        blocks.append(Rendered(path, "effects", content, new))
    errors += [
        f"{rel}: a grammar render_lists.py does not render, so its effect names"
        " would go stale; add it to EFFECT_TARGETS, or move it out of the syntax"
        " directory if it is not a grammar"
        for rel in discovered_grammars(root) if rel not in GRAMMARS
    ]
    return blocks, errors


# ---------------------------------------------------------------------------
# The limitation tables
# ---------------------------------------------------------------------------


class Table(NamedTuple):
    """One rendered table: the block it fills, and how it is laid out."""

    id: str
    path: str
    name: str
    header: str
    rule: str
    issue_column: int
    columns: int
    rows: tuple[str, ...]


class Limitation(NamedTuple):
    """One limitation: the issues it cites, and each table's cells for it,
    the Issue column apart."""

    id: str
    issues: tuple[int, ...]
    rows: dict[str, tuple[str, ...]]


class Limitations(NamedTuple):
    tables: tuple[Table, ...]
    records: dict[str, Limitation]


_TOP_KEYS = frozenset({"about", "tables", "limitations"})
_TABLE_KEYS = frozenset({"table", "header", "rule", "issue_column", "rows"})
_RECORD_KEYS = frozenset({"id", "issues", "rows"})
_TABLE_ID = re.compile(rf"([^#\s]+)#({_BLOCK_NAME})")
_UNESCAPED_PIPE = re.compile(r"(?<!\\)\|")


def _row_cells(row: str) -> list[str] | None:
    """The cells of a table row written as `| a | b |`, or ``None``.  A
    pipe with a space before it cannot be an escaped one."""
    if not (row.startswith("| ") and row.endswith(" |")) or "\n" in row:
        return None
    return row[2:-2].split(" | ")


def _is_count(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _tables(raw_tables: Any, errors: list[str]) -> list[Table]:
    if not isinstance(raw_tables, list):
        errors.append(f"{DATA}: `tables` is not a list")
        return []
    tables: list[Table] = []
    for index, raw in enumerate(raw_tables):
        where = f"{DATA}: tables[{index}]"
        if not isinstance(raw, dict) or set(raw) != _TABLE_KEYS:
            errors.append(f"{where}: a table has exactly the keys {', '.join(sorted(_TABLE_KEYS))}")
            continue
        named = _TABLE_ID.fullmatch(raw["table"]) if isinstance(raw["table"], str) else None
        if named is None:
            errors.append(f"{where}: `table` is `path#block`, not {raw['table']!r}")
            continue
        where = f"{DATA}: {raw['table']}"
        columns = _row_cells(raw["header"]) if isinstance(raw["header"], str) else None
        if columns is None:
            errors.append(f"{where}: the header {raw['header']!r} is not a table row")
            continue
        rule = raw["rule"]
        if not (
            isinstance(rule, str)
            and re.fullmatch(r"\|(?::?-+:?\|)+", rule)
            and rule.count("|") - 1 == len(columns)
        ):
            errors.append(
                f"{where}: the rule {rule!r} is not a delimiter row of"
                f" {len(columns)} columns"
            )
        column = raw["issue_column"]
        if not (_is_count(column) and 0 <= column < len(columns)):
            errors.append(
                f"{where}: issue_column {column!r} is not one of its {len(columns)}"
                " columns"
            )
            column = 0
        rows = raw["rows"]
        if not (isinstance(rows, list) and all(isinstance(r, str) for r in rows)):
            errors.append(f"{where}: `rows` is not a list of record ids")
            continue
        if not rows:
            errors.append(f"{where}: the table has no rows")
        errors += [
            f"{where}: the table lists `{rid}` twice"
            for rid in sorted({r for r in rows if rows.count(r) > 1})
        ]
        tables.append(Table(
            id=raw["table"], path=named.group(1), name=named.group(2),
            header=raw["header"], rule=str(rule), issue_column=column,
            columns=len(columns), rows=tuple(rows),
        ))
    for table_id in sorted({t.id for t in tables if [u.id for u in tables].count(t.id) > 1}):
        errors.append(f"{DATA}: the table {table_id} is named twice")
    return tables


def _records(
    raw_records: Any, tables: dict[str, Table], errors: list[str]
) -> dict[str, Limitation]:
    if not isinstance(raw_records, list):
        errors.append(f"{DATA}: `limitations` is not a list")
        return {}
    records: dict[str, Limitation] = {}
    for index, raw in enumerate(raw_records):
        where = f"{DATA}: limitations[{index}]"
        if not isinstance(raw, dict) or set(raw) != _RECORD_KEYS:
            errors.append(f"{where}: a record has exactly the keys {', '.join(sorted(_RECORD_KEYS))}")
            continue
        rid = raw["id"]
        if not (isinstance(rid, str) and rid):
            errors.append(f"{where}: `id` is not a name")
            continue
        if rid in records:
            errors.append(f"{where}: the id `{rid}` is used twice")
            continue
        where = f"{DATA}: `{rid}`"
        issues = raw["issues"]
        if not (
            isinstance(issues, list)
            and all(_is_count(n) and n >= 1 for n in issues)
            and len(set(issues)) == len(issues)
        ):
            errors.append(f"{where}: issues is a list of distinct issue numbers, not {issues!r}")
            issues = []
        rows = raw["rows"]
        if not isinstance(rows, dict):
            errors.append(f"{where}: `rows` is not an object of table ids")
            continue
        if not rows:
            errors.append(f"{where}: no table carries the record `{rid}`")
        cells_by_table: dict[str, tuple[str, ...]] = {}
        for table_id, cells in rows.items():
            table = tables.get(table_id)
            if table is None:
                errors.append(f"{where}: cells for {table_id}, which is not a table in {DATA}")
                continue
            wanted = table.columns - 1
            if not (
                isinstance(cells, list)
                and all(isinstance(c, str) for c in cells)
                and len(cells) == wanted
            ):
                errors.append(
                    f"{where}: {table_id} takes {wanted} cells besides its Issue"
                    f" column, not {cells!r}"
                )
                continue
            for cell in cells:
                if "\n" in cell:
                    errors.append(f"{where}: a cell for {table_id} holds a line break")
                elif _UNESCAPED_PIPE.search(cell):
                    errors.append(
                        f"{where}: a cell for {table_id} holds an unescaped pipe,"
                        f" which ends the cell; write it `\\|`: {cell[:80]!r}"
                    )
            cells_by_table[table_id] = tuple(cells)
        records[rid] = Limitation(rid, tuple(issues), cells_by_table)
    return records


def load_limitations(root: Path) -> Limitations | list[str]:
    """`limitations.json` under `root`, every reference in it checked, or
    every reason it cannot be rendered."""
    try:
        data = json.loads((root / DATA).read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        return [f"{DATA}: cannot be read: {exc}"]
    if not isinstance(data, dict):
        return [f"{DATA}: the file is not a JSON object"]
    errors = [f"{DATA}: an unknown key `{key}`" for key in sorted(set(data) - _TOP_KEYS)]
    errors += [f"{DATA}: no `{key}`" for key in sorted(_TOP_KEYS - set(data))]
    if errors:
        return errors
    if not isinstance(data["about"], str):
        errors.append(f"{DATA}: `about` is not a string")
    tables = _tables(data["tables"], errors)
    by_id = {table.id: table for table in tables}
    records = _records(data["limitations"], by_id, errors)
    if errors:
        return errors
    for table in tables:
        for rid in table.rows:
            record = records.get(rid)
            if record is None:
                errors.append(f"{DATA}: {table.id} lists `{rid}`, which no record has")
            elif table.id not in record.rows:
                errors.append(f"{DATA}: {table.id} lists `{rid}`, which has no cells for it")
    for record in records.values():
        for table_id in record.rows:
            if record.id not in by_id[table_id].rows:
                errors.append(
                    f"{DATA}: `{record.id}` has cells for {table_id}, which does not"
                    " list it"
                )
    if errors:
        return errors
    return Limitations(tuple(tables), records)


def _issue_cell(issues: Sequence[int]) -> str:
    if not issues:
        return "—"
    return ", ".join(f"[#{n}]({ISSUES_URL}{n})" for n in issues)


def render_table(table: Table, records: dict[str, Limitation]) -> str:
    """The table, header to last row, as it belongs between its markers."""
    lines = [table.header, table.rule]
    for rid in table.rows:
        record = records[rid]
        cells = list(record.rows[table.id])
        cells.insert(table.issue_column, _issue_cell(record.issues))
        lines.append("| " + " | ".join(cells) + " |")
    return "".join(f"{line}\n" for line in lines)


def limitation_blocks(root: Path) -> tuple[list[Rendered], list[str]]:
    """Each limitation table as it is and as the data file renders it, and
    every reason one cannot be rendered.  A data file with an error renders
    no table at all."""
    data = load_limitations(root)
    if isinstance(data, list):
        return [], data
    blocks: list[Rendered] = []
    errors: list[str] = []
    for table in data.tables:
        read = _read(root, table.path, {table.name})
        if isinstance(read, str):
            errors.append(read)
            continue
        text, spans = read
        start, end = spans[table.name]
        blocks.append(
            Rendered(table.path, table.name, text[start:end], render_table(table, data.records))
        )
    return blocks, errors


# ---------------------------------------------------------------------------
# The host-import roster
# ---------------------------------------------------------------------------

#: The file whose roster lists the registry's host imports.
ROSTER = "vera/browser/runtime.mjs"


def host_import_rows() -> list[tuple[str, str, str]]:
    """Every row of the registry's ``HOST_IMPORTS``, in its order: its name,
    its family, and how a declared import names an instance of it.  The
    caller puts the tree's root first on `sys.path`."""
    from vera.builtins import HOST_IMPORTS

    return [(row.name, row.family, row.instance) for row in HOST_IMPORTS]


def render_roster(rows: Sequence[tuple[str, str, str]]) -> str:
    """The roster, as it belongs between its markers."""
    lines = [
        "// The host imports a module can declare: one row of HOST_IMPORTS in",
        "// vera/builtins.py each, its name, its family, and how a declared",
        "// import names an instance of it (\"\" for none; \"k\", \"v\", \"kv\" or",
        "// \"e\" for a Map or Set row named by its key, value or element tag, as",
        "// `map_insert$ks_vi`; \"cell\" for a State row named by its cell, as",
        "// `state_get_Int`).  scripts/render_lists.py writes this block.",
        "const HOST_IMPORT_ROWS = new Map([",
    ]
    lines += [f'  ["{name}", "{family}", "{instance}"],' for name, family, instance in rows]
    lines.append("].map(([name, family, instance]) => [name, { name, family, instance }]));")
    return "".join(f"{line}\n" for line in lines)


def roster_blocks(
    root: Path, rows: Sequence[tuple[str, str, str]]
) -> tuple[list[Rendered], list[str]]:
    """The roster as it is and as the registry's `rows` render it, and every
    reason it cannot be rendered."""
    if not rows:
        return [], ["the built-in registry lists no host import"]
    read = _read(root, ROSTER, {"host-imports"})
    if isinstance(read, str):
        return [], [read]
    text, spans = read
    start, end = spans["host-imports"]
    return [Rendered(ROSTER, "host-imports", text[start:end], render_roster(rows))], []


# ---------------------------------------------------------------------------
# The signature tables
# ---------------------------------------------------------------------------

#: The chapter whose signature tables are rendered.
SPEC = "spec/09-standard-library.md"

#: Each signature table's block, and what its rows name: built-in
#: functions (``None``) or the operations of an effect.
SIGNATURE_BLOCKS: dict[str, str | None] = {
    "signatures-option": None,
    "signatures-result": None,
    "signatures-set": None,
    "signatures-map": None,
    "signatures-io": "IO",
    "signatures-state": "State",
    "signatures-http": "Http",
    "signatures-inference": "Inference",
    "signatures-math": None,
    "signatures-json-parse": None,
    "signatures-json-object": None,
    "signatures-json-array": None,
    "signatures-json-type": None,
    "signatures-decimal-construct": None,
    "signatures-decimal-arithmetic": None,
    "signatures-decimal-comparison": None,
}

_ROW_NAME = re.compile(r"`(?:[A-Z][A-Za-z]*\.)?([a-z_][a-z0-9_]*)")


def signature_text(params: Sequence[str], ret: str, forall: Sequence[str] = ()) -> str:
    """A signature as the tables write it: the parameter types, or ``()``,
    an ASCII arrow and the result type, after a ``forall`` when generic."""
    body = (", ".join(params) if params else "()") + f" -> {ret}"
    return f"forall<{', '.join(forall)}> {body}" if forall else body


def signatures() -> dict[str | None, dict[str, str]]:
    """Every signature a table can show: the built-in functions' under
    ``None``, each effect's operations under its name.  The caller puts the
    tree's root first on `sys.path`."""
    from vera.builtins import BUILTINS
    from vera.environment import TypeEnv
    from vera.types import FunctionType, pretty_type

    def written(ty: Any) -> str:
        if isinstance(ty, FunctionType):
            params = ", ".join(written(p) for p in ty.params)
            return f"fn({params} -> {written(ty.return_type)})"
        return pretty_type(ty)

    out: dict[str | None, dict[str, str]] = {None: {}}
    for name, spec in BUILTINS.items():
        sig = spec.signature
        out[None][name] = signature_text(
            [written(p) for p in sig.params], written(sig.ret), sig.forall or ())
    env = TypeEnv()
    for effect in sorted({e for e in SIGNATURE_BLOCKS.values() if e is not None}):
        ops = env.effects[effect].operations
        out[effect] = {
            op: signature_text([written(p) for p in info.param_types], written(info.return_type))
            for op, info in ops.items()
        }
    return out


def render_signature_table(
    content: str, kind: str | None, known: dict[str, str], block: str
) -> tuple[str, list[str]]:
    """The table with each row's Signature cell written from `known`, and
    every reason a row cannot be rendered."""
    errors: list[str] = []
    lines = content.splitlines(keepends=True)
    rows = [i for i, line in enumerate(lines) if line.startswith("|")]
    if len(rows) < 3:
        return content, [f"{SPEC}: the `{block}` block holds no table"]
    header = _row_cells(lines[rows[0]].rstrip("\n"))
    if header is None or len(header) < 2 or header[1] != "Signature":
        return content, [f"{SPEC}: the `{block}` block's table has no Signature column"]
    out = list(lines)
    for i in rows[2:]:
        line = lines[i].rstrip("\n")
        cells = _row_cells(line)
        named = _ROW_NAME.match(cells[0]) if cells else None
        if cells is None or named is None:
            errors.append(f"{SPEC}: a row of the `{block}` block names no function: {line[:80]!r}")
            continue
        name = named.group(1)
        if name not in known:
            what = "built-in" if kind is None else f"operation of {kind}"
            errors.append(f"{SPEC}: the `{block}` block lists `{name}`, which is no {what}")
            continue
        cells[1] = f"`{known[name]}`"
        out[i] = "| " + " | ".join(cells) + " |\n"
    return "".join(out), errors


def signature_blocks(
    root: Path, known: dict[str | None, dict[str, str]]
) -> tuple[list[Rendered], list[str]]:
    """Each signature table as it is and as the registries render it, and
    every reason one cannot be rendered."""
    read = _read(root, SPEC, set(SIGNATURE_BLOCKS))
    if isinstance(read, str):
        return [], [read]
    text, spans = read
    blocks: list[Rendered] = []
    errors: list[str] = []
    for block, kind in SIGNATURE_BLOCKS.items():
        start, end = spans[block]
        new, problems = render_signature_table(text[start:end], kind, known.get(kind, {}), block)
        errors += problems
        blocks.append(Rendered(SPEC, block, text[start:end], new))
    return blocks, errors


# ---------------------------------------------------------------------------
# The whole tree
# ---------------------------------------------------------------------------


def _targets(root: Path) -> dict[str, set[str]]:
    targets: dict[str, set[str]] = {path: {"effects"} for path in EFFECT_TARGETS}
    targets.setdefault(ROSTER, set()).add("host-imports")
    targets.setdefault(SPEC, set()).update(SIGNATURE_BLOCKS)
    data = load_limitations(root)
    if not isinstance(data, list):
        for table in data.tables:
            targets.setdefault(table.path, set()).add(table.name)
    return targets


def plan(
    root: Path, *, effects: Sequence[str] | None = None,
    host_rows: Sequence[tuple[str, str, str]] | None = None,
    known_signatures: dict[str | None, dict[str, str]] | None = None,
) -> tuple[list[Rendered], list[str]]:
    """Every block in the tree, as it is and as its source renders it, and
    every reason a block cannot be rendered.  `effects`, `host_rows` and
    `known_signatures` stand in for the registries; by default the tree's
    own are read."""
    names = list(effects) if effects is not None else effect_names()
    blocks, errors = effect_blocks(root, names)
    for more, more_errors in (
        limitation_blocks(root),
        roster_blocks(root, host_rows if host_rows is not None else host_import_rows()),
        signature_blocks(
            root, known_signatures if known_signatures is not None else signatures()),
    ):
        blocks += more
        errors += more_errors
    for path, names_here in sorted(_targets(root).items()):
        file = root / path
        if not file.is_file():
            continue
        spans = read_blocks(file.read_text(encoding="utf-8"), path)
        if isinstance(spans, str):
            continue
        errors += [
            f"{path}: the `{name}` block is not one render_lists.py writes"
            for name in sorted(set(spans) - names_here)
        ]
    return blocks, errors


def _first_difference(current: str, new: str) -> tuple[str, str]:
    pairs = itertools.zip_longest(current.splitlines(), new.splitlines(), fillvalue="(nothing)")
    return next(((a, b) for a, b in pairs if a != b), ("", ""))


def stale_blocks(root: Path, **sources: Any) -> list[str]:
    """Why the tree's rendered blocks are not what `--write` would write:
    one line per stale block, or every reason a block cannot be rendered;
    ``[]`` when every block is current.  `sources` stand in for the
    registries, as `plan` takes them."""
    blocks, errors = plan(root, **sources)
    return errors or _stale(blocks)


def _stale(blocks: Sequence[Rendered]) -> list[str]:
    stale: list[str] = []
    for block in blocks:
        if block.current == block.new:
            continue
        file_has, source_gives = _first_difference(block.current, block.new)
        stale.append(
            f"{block.path}: the `{block.name}` block is not what"
            " scripts/render_lists.py writes; run `python scripts/render_lists.py"
            " --write` and commit the result.  First difference: the file has"
            f" {file_has[:160]!r}, the source gives {source_gives[:160]!r}"
        )
    return stale


def write(root: Path, **sources: Any) -> tuple[list[str], list[str]]:
    """Render every block into its file: the files rewritten, and, when any
    block cannot be rendered, every reason, with no file written.  `sources`
    stand in for the registries, as `plan` takes them."""
    blocks, errors = plan(root, **sources)
    if errors:
        return [], errors
    by_path: dict[str, list[Rendered]] = {}
    for block in blocks:
        by_path.setdefault(block.path, []).append(block)
    written: list[str] = []
    for path, here in by_path.items():
        if all(block.current == block.new for block in here):
            continue
        file = root / path
        text = file.read_text(encoding="utf-8")
        spans = read_blocks(text, path)
        assert isinstance(spans, dict), spans
        out = text
        for block in sorted(here, key=lambda b: -spans[b.name][0]):
            start, end = spans[block.name]
            out = out[:start] + block.new + out[end:]
        file.write_text(out, encoding="utf-8")
        written.append(path)
    return written, []


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="render every block into its file")
    mode.add_argument(
        "--check", action="store_true",
        help="write nothing; exit 1 naming each block that is not what --write writes",
    )
    args = parser.parse_args(argv)
    # The registries are `vera`'s: this checkout's, whatever editable
    # install the interpreter would find first.
    sys.path.insert(0, str(ROOT))
    if args.check:
        blocks, errors = plan(ROOT)
        if errors:
            print(f"ERROR: {len(errors)} rendered block(s) cannot be rendered:", file=sys.stderr)
            for error in errors:
                print(f"  {error}", file=sys.stderr)
            return 1
        stale = _stale(blocks)
        if stale:
            print(f"ERROR: {len(stale)} rendered block(s) are not current:", file=sys.stderr)
            for line in stale:
                print(f"  {line}", file=sys.stderr)
            return 1
        print(f"Every rendered list is current: {len(blocks)} blocks.")
        return 0
    written, errors = write(ROOT)
    if errors:
        print(
            f"ERROR: {len(errors)} rendered block(s) cannot be rendered, so nothing"
            " was written:",
            file=sys.stderr,
        )
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    if written:
        print(f"Rewrote {', '.join(written)}.")
    else:
        print("Every rendered list was already current.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
