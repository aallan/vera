"""A diagnostic's location and the source it quotes are built in one place
(#1636, with #1632 and #1860 folded in).

Spec §0.5.1 requires every diagnostic to name its file, line and column,
"with the offending source line quoted and the error position indicated".
Each stage built its location and cut its quote by hand, and each gap was a
stage that did one without the other:

- the transform held neither the file nor the source, so E009 and E040 named
  no file, quoted no line and drew no caret, in text and in ``--json``, and
  an E013 about a module's transform error quoted it without its file;
- a position inside a string literal was computed as if the literal sat on
  one line, so a segment after a newline in the literal was reported on the
  line the literal opens (#1632), and an invalid escape at the literal's
  opening quote rather than at its backslash;
- code generation's E614 (a typed hole) named its line and quoted none;
- E501's ``Precondition:`` line quoted every physical line its clause spans,
  whole, so a clause sharing its line was quoted with its neighbours
  (#1860);
- a refusal with no position printed ``line 0, column 0``.

Every location is now built by ``vera.errors.locate`` / ``locate_at``, the
transform's at its boundary from the file and source ``parse`` carries on
the tree, and every position in a literal through one offset mapping
(``vera.transform._Literal.point``).  A message quoting an expression, a
type or a declaration renders it from the node as ``vera fmt`` writes it
(#1573); a fix that splices text keeps the one source slice,
``vera.errors.span_bounds``.  ``scripts/check_diagnostic_fields.py``'s
placement pass refuses a location or a quote built anywhere else.

The matrix: every code raisable before the checker, by text and ``--json``,
asserting the file, the source line the location names and the caret;
every diagnostic that quotes a second location (E501's clause, local and
imported; E136's alias), by a clause alone on its line, sharing it, and
spanning lines; a segment after a newline in a literal, for each
transform-stage code a segment raises; an invalid escape at three positions
in a literal and after a segment; and the refusals with no position.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from collections.abc import Mapping
from typing import Any

import pytest

from tests import pipeline
from vera.errors import ERROR_CODES

pytestmark = pytest.mark.matrix(decides=[
    "vera/errors.py", "vera/transform.py", "vera/parser.py",
    "vera/verifier.py", "vera/checker/resolution.py", "vera/formatter.py",
])

_FIELDS = ("severity", "description", "location", "source_line",
           "rationale", "fix", "spec_ref", "error_code")

_H = "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
_INT = "public fn f(@Int -> @Int)\n" + _H
_STR = "public fn f(@Int -> @String)\n" + _H


def _run(tmp_path: Path, files: Mapping[str, str | bytes], *args: str,
         command: str = "check") -> tuple[Path, str, dict[str, Any]]:
    """Write *files*, run `vera <command>` on main.vera by text and by
    `--json`: the entry's path, the text output and the first diagnostic."""
    for name, text in files.items():
        target = tmp_path / name
        if isinstance(text, bytes):
            target.write_bytes(text)
        else:
            target.write_text(text, encoding="utf-8")
    entry = tmp_path / "main.vera"
    ran = pipeline.cli(command, *args, entry)
    envelope = pipeline.cli(command, "--json", *args, entry).json()
    diags = envelope["diagnostics"]
    assert diags, envelope
    return entry, ran.stdout + ran.stderr, diags[0]


def _line(text: str, n: int) -> str:
    return text.split("\n")[n - 1]


def _assert_placed(entry: Path, text: str, diag: dict[str, Any],
                   source: str, code: str) -> None:
    """The documented fields, a file, the line the location names, and the
    caret under its column in the text form."""
    assert diag["error_code"] == code, diag
    loc = diag["location"]
    assert loc["file"] == str(entry), loc
    assert loc["line"] > 0, loc
    for name in _FIELDS:
        assert name in diag, (name, diag)
    quoted = _line(source, loc["line"])
    assert diag["source_line"] == quoted, diag
    head = f"[{code}] Error at {entry}, line {loc['line']}, column {loc['column']}:"
    assert head in text, text
    block = text.split(head, 1)[1].splitlines()
    assert block[2] == f"    {quoted.rstrip()}", block
    assert block[3] == " " * (loc["column"] - 1 + 4) + "^", block


# =====================================================================
# The reported instances, red first
# =====================================================================


def test_repro_1636_e009_names_its_file_and_quotes_its_line(
        tmp_path: Path) -> None:
    source = _STR + '  "bad \\q escape"\n}\n'
    entry, text, diag = _run(tmp_path, {"main.vera": source})
    _assert_placed(entry, text, diag, source, "E009")
    assert (diag["location"]["line"], diag["location"]["column"]) == (6, 8)


def test_repro_1636_e040_names_its_file_and_quotes_its_line(
        tmp_path: Path) -> None:
    source = _INT + "  @Int.0 |> 1\n}\n"
    entry, text, diag = _run(tmp_path, {"main.vera": source})
    _assert_placed(entry, text, diag, source, "E040")


def test_repro_1636_e013_names_the_module_of_its_transform_error(
        tmp_path: Path) -> None:
    module = _STR.replace("fn f", "fn g") + '  "bad \\q"\n}\n'
    _, _, diag = _run(tmp_path, {
        "main.vera": "import a;\n" + _INT + "  @Int.0\n}\n",
        "a.vera": module})
    assert diag["error_code"] == "E013"
    assert f"[E009] Error at {tmp_path / 'a.vera'}, line 6, column 8:" in (
        diag["description"]), diag["description"]


def test_repro_1632_a_segment_after_a_newline_is_on_its_own_line(
        tmp_path: Path) -> None:
    source = _STR + '  "prefix\n\\(@Bool.5)"\n}\n'
    entry, text, diag = _run(tmp_path, {"main.vera": source})
    _assert_placed(entry, text, diag, source, "E130")
    assert (diag["location"]["line"], diag["location"]["column"]) == (7, 3)


def test_repro_1860_e501_quotes_the_clause_alone(tmp_path: Path) -> None:
    source = ("private fn h(@Int -> @Int) requires(@Int.0 > 0) ensures(true) "
              "effects(pure) { @Int.0 }\n\npublic fn caller(@Int -> @Int)\n"
              + _H + "  h(0)\n}\n")
    _, text, _ = _run(tmp_path, {"main.vera": source}, command="verify")
    assert "    Precondition: requires(@Int.0 > 0)\n" in text, text


def test_repro_e614_quotes_its_line(tmp_path: Path) -> None:
    source = _INT + "  ?\n}\n"
    entry, text, diag = _run(tmp_path, {"main.vera": source},
                             command="compile")
    _assert_placed(entry, text, diag, source, "E614")


_BOOM = "fn boom(@Int -> @Int)\n" + _H + "  @Int.0 / 0\n}\n"


def test_repro_e800_quotes_the_line_of_the_function_that_trapped(
        tmp_path: Path) -> None:
    # The trap is placed at the declaration of the first function of the
    # program's own its backtrace names: line 9 here, not the file's first.
    source = ("public fn main(@Unit -> @Int)\n" + _H + "  boom(7)\n}\n\n"
              "private " + _BOOM)
    entry, text, diag = _run(tmp_path, {"main.vera": source}, command="run")
    _assert_placed(entry, text, diag, source, "E800")
    assert diag["location"]["line"] == 9, diag
    assert diag["source_line"] == "private fn boom(@Int -> @Int)", diag


def test_repro_e800_in_an_imported_module_quotes_the_module_line(
        tmp_path: Path) -> None:
    lib = "module lib;\n\npublic " + _BOOM
    main = "import lib(boom);\n\npublic fn main(@Unit -> @Int)\n" + _H + (
        "  boom(7)\n}\n")
    _entry, text, diag = _run(
        tmp_path, {"lib.vera": lib, "main.vera": main}, command="run")
    loc = diag["location"]
    assert diag["error_code"] == "E800", diag
    assert Path(loc["file"]).resolve() == (tmp_path / "lib.vera").resolve()
    assert (loc["line"], loc["column"]) == (3, 1), loc
    assert diag["source_line"] == "public fn boom(@Int -> @Int)", diag
    block = text.split("line 3, column 1:", 1)[1].splitlines()
    assert block[2:4] == ["    public fn boom(@Int -> @Int)", "    ^"], block


def test_repro_a_refusal_with_no_position_names_the_file_alone(
        tmp_path: Path) -> None:
    missing = tmp_path / "main.vera"
    ran = pipeline.cli("check", missing)
    assert ran.stderr.startswith(f"[E900] Error at {missing}:\n"), ran.stderr
    assert "line 0" not in ran.stderr
    envelope = pipeline.cli("check", "--json", missing).json()
    assert envelope["diagnostics"][0]["location"] == {
        "line": 0, "column": 0, "file": str(missing)}


def test_repro_a_refusal_with_no_position_and_no_file_names_neither(
        tmp_path: Path) -> None:
    entry = tmp_path / "main.vera"
    entry.write_text(_INT + "  @Int.0\n}\n", encoding="utf-8")
    ran = pipeline.cli("compile", "--no-reconcile", entry)
    assert ran.stderr.startswith("[E901] Error:\n"), ran.stderr


# =====================================================================
# The matrix: every code raisable before the checker
# =====================================================================

#: Each pre-checker code, by a program that raises it.
PRE_CHECKER: dict[str, tuple[str, dict[str, str | bytes]]] = {
    "E001": ("E001", {"main.vera": "public fn f(@Int -> @Int)\n{\n  @Int.0\n}\n"}),
    "E002": ("E002", {"main.vera": "public fn f(@Int -> @Int)\n  requires(true)\n"
                      "  ensures(true)\n  invariant(true)\n{\n  @Int.0\n}\n"}),
    "E005": ("E005", {"main.vera": _INT + "  @Int.0 +\n}\n"}),
    "E006": ("E006", {"main.vera": _INT + "  @Int.0 $ 1\n}\n"}),
    "E008": ("E008", {"main.vera": _INT + "  m.g(@Int.0)\n}\n"}),
    "E009_escape": ("E009", {"main.vera": _STR + '  "bad \\q escape"\n}\n'}),
    "E009_surrogate": ("E009", {"main.vera": _STR + '  "a \\u{D800} b"\n}\n'}),
    "E009_unicode_brace": ("E009", {"main.vera": _STR + '  "a \\u0041"\n}\n'}),
    "E009_interp_empty": ("E009", {"main.vera": _STR + '  "a \\() b"\n}\n'}),
    "E009_interp_unclosed": ("E009", {"main.vera": _STR + '  "a \\(@Int.0 b"\n}\n'}),
    "E009_interp_invalid": ("E009", {"main.vera": _STR + '  "a \\(1 +) b"\n}\n'}),
    "E009_interp_statement": ("E009", {
        "main.vera": _STR + '  "a \\(let @Int = 1; @Int.0) b"\n}\n'}),
    "E011": ("E011", {"main.vera": "import a;\n" + _INT + "  @Int.0\n}\n",
                      "a.vera": "import main;\n" + _INT.replace("fn f", "fn g")
                      + "  @Int.0\n}\n"}),
    "E012": ("E012", {"main.vera": "import nothere;\n" + _INT + "  @Int.0\n}\n"}),
    "E013_parse": ("E013", {"main.vera": "import a;\n" + _INT + "  @Int.0\n}\n",
                            "a.vera": _INT.replace("fn f", "fn g") + "  @Int.0 +\n}\n"}),
    "E013_transform": ("E013", {"main.vera": "import a;\n" + _INT + "  @Int.0\n}\n",
                                "a.vera": _STR.replace("fn f", "fn g")
                                + '  "bad \\q"\n}\n'}),
    "E020": ("E020", {"main.vera": _INT + "  @Int.0 {- open\n}\n"}),
    "E021": ("E021", {"main.vera": "public fn f(@Int /* open -> @Int)\n" + _H
                      + "  @Int.0\n}\n"}),
    "E023": ("E023", {"main.vera": "public fn f(@Int /* a /* b */ */ -> @Int)\n"
                      + _H + "  @Int.0\n}\n"}),
    "E024": ("E024", {"main.vera": (_INT + "  -- \xff\n  @Int.0\n}\n").encode(
        "latin-1")}),
    "E030": ("E030", {"main.vera": "public fn f(@Int -> @Int)\n  requires(true)\n"
                      "  ensures(old(@Int.0) == 1)\n  effects(pure)\n{\n  @Int.0\n}\n"}),
    "E031": ("E031", {"main.vera": "public fn f(@Int -> @Int)\n  requires(true)\n"
                      "  ensures(new(@Int.0) == 1)\n  effects(pure)\n{\n  @Int.0\n}\n"}),
    "E032": ("E032", {"main.vera": "public fn f(@Int -> @Int)\n  requires(true)\n"
                      "  effects(pure)\n  ensures(true)\n{\n  @Int.0\n}\n"}),
    "E040": ("E040", {"main.vera": _INT + "  @Int.0 |> 1\n}\n"}),
    "E040_segment": ("E040", {"main.vera": _STR + '  "a \\(@Int.0 |> 1) b"\n}\n'}),
}

#: The pre-checker codes no program raises, and why.
NOT_RAISED = {
    "E007": "an unrecognised Lark exception: a parser bug, no source raises it",
    "E010": "a grammar rule the transformer misses: a compiler bug, no "
            "source raises it",
}


def test_the_matrix_covers_every_pre_checker_code() -> None:
    """Every code of the parse range (E001-E040) is a cell or is named as
    raised by no program."""
    pre = {c for c in ERROR_CODES if re.fullmatch(r"E0[0-4]\d", c)}
    covered = {code for code, _ in PRE_CHECKER.values()}
    assert covered | set(NOT_RAISED) == pre
    assert not covered & set(NOT_RAISED)


@pytest.mark.parametrize("cell", sorted(PRE_CHECKER))
def test_a_pre_checker_diagnostic_is_placed(cell: str, tmp_path: Path) -> None:
    code, files = PRE_CHECKER[cell]
    entry, text, diag = _run(tmp_path, files)
    main = files["main.vera"]
    source = (main.decode("latin-1") if isinstance(main, bytes) else main)
    if code == "E024":
        # Its quote is read from the bytes, with the undecodable byte shown
        # as the replacement character.
        source = source.replace("\xff", "\ufffd")
    if code == "E011":
        # A cycle is reported in the file that closes it, by its full path.
        entry = entry.resolve()
    _assert_placed(entry, text, diag, source, code)


# =====================================================================
# Positions inside a literal: one mapping
# =====================================================================

#: (program body line(s), the code, the (line, column) it is placed at).
#: The body starts on line 6.
LITERAL_POSITIONS: dict[str, tuple[str, str, tuple[int, int]]] = {
    "escape_at_start": ('  "\\q tail"', "E009", (6, 4)),
    "escape_in_middle": ('  "head \\q tail"', "E009", (6, 9)),
    "escape_after_newline": ('  "head\n  x \\q"', "E009", (7, 5)),
    "escape_after_segment": ('  "\\(@Int.0) \\q"', "E009", (6, 14)),
    "escape_after_segment_and_newline": ('  "\\(@Int.0)\n\\q"', "E009", (7, 1)),
    "segment_after_newline_E130": ('  "prefix\n\\(@Bool.5)"', "E130", (7, 3)),
    "segment_after_newline_E040": ('  "prefix\n\\(@Int.0 |> 1)"', "E040", (7, 13)),
    "segment_after_newline_empty": ('  "prefix\n\\()"', "E009", (7, 1)),
    "segment_after_newline_unclosed": ('  "prefix\n  \\(@Int.0"', "E009", (7, 3)),
    "segment_after_newline_invalid": ('  "prefix\n\\(1 +)"', "E009", (7, 1)),
    "segment_two_lines_down_E130": ('  "a\nb\n  c \\(@Bool.5)"', "E130", (8, 7)),
    "segment_on_one_line_E130": ('  "prefix \\(@Bool.5)"', "E130", (6, 13)),
}


@pytest.mark.parametrize("cell", sorted(LITERAL_POSITIONS))
def test_a_position_in_a_literal_is_its_own(cell: str, tmp_path: Path) -> None:
    body, code, (line, column) = LITERAL_POSITIONS[cell]
    source = _STR + body + "\n}\n"
    entry, text, diag = _run(tmp_path, {"main.vera": source})
    _assert_placed(entry, text, diag, source, code)
    assert (diag["location"]["line"], diag["location"]["column"]) == (
        line, column)


# =====================================================================
# A quote of a second location: the clause or declaration alone
# =====================================================================

_CALLER = ("\npublic fn caller(@Int -> @Int)\n" + _H + "  h(0)\n}\n")

#: How the callee's `requires` is laid out.
CLAUSE_LAYOUTS: dict[str, str] = {
    "alone": ("private fn h(@Int -> @Int)\n  requires(@Int.0 > 0)\n"
              "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    "sharing_its_line": ("private fn h(@Int -> @Int) requires(@Int.0 > 0) "
                         "ensures(true) effects(pure) { @Int.0 }\n"),
    "spanning_lines": ("private fn h(@Int -> @Int)\n  requires(@Int.0 >\n    0)\n"
                       "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    "spanning_and_sharing": ("private fn h(@Int -> @Int) requires(@Int.0 >\n"
                             "    0) ensures(true)\n  effects(pure)\n{\n"
                             "  @Int.0\n}\n"),
    "beside_another_clause": ("private fn h(@Int -> @Int)\n"
                              "  requires(@Int.0 > 0) requires(@Int.0 < 9)\n"
                              "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    "with_a_comment": ("private fn h(@Int -> @Int)\n  requires(@Int.0 > -- c\n"
                       "    0)\n  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n"),
}


@pytest.mark.parametrize("imported", [False, True], ids=["local", "imported"])
@pytest.mark.parametrize("layout", sorted(CLAUSE_LAYOUTS))
def test_e501_quotes_the_clause_alone(layout: str, imported: bool,
                                      tmp_path: Path) -> None:
    callee = CLAUSE_LAYOUTS[layout]
    if imported:
        files = {"main.vera": "import m(h);\n" + _CALLER,
                 "m.vera": callee.replace("private fn h", "public fn h")}
    else:
        files = {"main.vera": callee + _CALLER}
    _, text, diag = _run(tmp_path, files, command="verify")
    assert diag["error_code"] == "E501", diag
    quoted = [line.strip() for line in diag["description"].splitlines()
              if line.strip().startswith("Precondition:")]
    assert quoted == ["Precondition: requires(@Int.0 > 0)"], diag["description"]
    assert "    Precondition: requires(@Int.0 > 0)\n" in text


_ALIAS_USE = ("import m;\n\npublic fn f(@Pos -> @Int)\n" + _H + "  0\n}\n")

#: How a module's alias is laid out; E136 quotes it as `vera fmt` writes it.
ALIAS_LAYOUTS: dict[str, str] = {
    "alone": "type Pos = { @Int | @Int.0 > 0 };\n",
    "sharing_its_line": ("type Pos = { @Int | @Int.0 > 0 }; "
                         "type Neg = { @Int | @Int.0 < 0 };\n"),
    "spanning_lines": "type Pos = { @Int |\n  @Int.0 > 0 };\n",
    "with_a_comment": "type Pos = { @Int | -- c\n  @Int.0 > 0 };\n",
    "unspaced": "type Pos={@Int|@Int.0>0};\n",
}


@pytest.mark.parametrize("layout", sorted(ALIAS_LAYOUTS))
def test_e136_quotes_the_declaration_as_vera_fmt_writes_it(
        layout: str, tmp_path: Path) -> None:
    _, _, diag = _run(tmp_path, {"main.vera": _ALIAS_USE,
                                 "m.vera": ALIAS_LAYOUTS[layout]})
    assert diag["error_code"] == "E136", diag
    assert "'type Pos = { @Int | @Int.0 > 0 };'" in diag["fix"], diag["fix"]


# =====================================================================
# The gate's placement pass
# =====================================================================


def _gate() -> Any:
    """`scripts/check_diagnostic_fields.py`, loaded once as a module."""
    import importlib.util
    import sys

    name = "_check_diagnostic_fields_1636"
    if name in sys.modules:
        return sys.modules[name]
    path = Path(__file__).resolve().parent.parent / "scripts" / (
        "check_diagnostic_fields.py")
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _placement(source: str) -> list[str]:
    return [v.missing[0] for v in _gate().placement_violations_in_source(
        source, "vera/example.py")]


#: Each shape the pass refuses, and its nearest accepted neighbour.
GATE_SHAPES: dict[str, tuple[str, str]] = {
    "a SourceLocation": ("loc = SourceLocation(file=f)\n",
                         "loc = locate(f, s)['location']\n"),
    "a source_line keyword": ("Diagnostic(description=d, source_line=q)\n",
                              "Diagnostic(description=d, **locate(f, s))\n"),
    "source_lines": ("lines = source_lines(s)\n", "lines = s.split()\n"),
    "a location's line": ("loc.line = 3\n", "span.line = 3\n"),
    "a location's column, by tuple": ("loc.line, loc.column = a, b\n",
                                      "x.line, x.column = a, b\n"),
    "a diagnostic's location's line": ("d.location.line = 3\n",
                                       "d.where.line = 3\n"),
    "a replaced location": ("replace(d.location, line=1)\n",
                            "replace(d, **locate(f, s, 1))\n"),
    "a slice at a column": ("t = text[span.column - 1:]\n",
                            "t = text[span.line - 1:]\n"),
    "a slice at an end column": ("t = text[:span.end_column - 1]\n",
                                 "t = text[:n]\n"),
}


@pytest.mark.parametrize("shape", sorted(GATE_SHAPES))
def test_the_gate_refuses_a_placement_by_hand(shape: str) -> None:
    refused, accepted = GATE_SHAPES[shape]
    assert len(_placement(refused)) == 1, refused
    assert _placement(accepted) == [], accepted


def test_the_gate_reads_nothing_in_the_constructors_module() -> None:
    shape = "loc = SourceLocation(file=f)\n"
    assert _gate().placement_violations_in_source(shape, "vera/errors.py") == []
    assert _gate().placement_violations_in_source(shape, "vera/x.py")


def test_the_tree_places_every_diagnostic_through_locate() -> None:
    root = Path(__file__).resolve().parent.parent
    gate = _gate()
    assert gate.placement_violations(gate.iter_vera_files(root / "vera")) == []


def test_an_exception_that_names_no_site_is_refused(tmp_path: Path) -> None:
    """The allowance only shrinks: an entry whose site places nothing by
    hand is itself a violation."""
    gate = _gate()
    clean = gate.ROOT / "vera" / "lexical.py"
    saved = dict(gate.PLACEMENT_EXCEPTIONS)
    try:
        gate.PLACEMENT_EXCEPTIONS[("vera/lexical.py", "scan_comments")] = "x"
        found = gate.placement_violations([clean])
    finally:
        gate.PLACEMENT_EXCEPTIONS.clear()
        gate.PLACEMENT_EXCEPTIONS.update(saved)
    assert [v.line for v in found] == [0], found


def test_the_json_location_of_a_placed_diagnostic_is_documented(
        tmp_path: Path) -> None:
    """The `location` keys CLAUDE.md § JSON diagnostics documents."""
    source = _STR + '  "bad \\q"\n}\n'
    _, _, diag = _run(tmp_path, {"main.vera": source})
    assert set(diag["location"]) == {"file", "line", "column"}
    assert json.dumps(diag)


#: A clause that names a function, a constructor or a helper: the quote is
#: rendered from the node, so it must name each as the program writes it,
#: not by the link name the typed program gives it (`mod$m$f`).
_NAMED_CALLEE = {
    "m.vera": ("public data Color { Red, Green }\n\n"
               "public fn is_pos(@Int -> @Bool)\n" + _H + "  @Int.0 > 0\n}\n\n"
               "public fn h(@Color, @Int -> @Int)\n"
               "  requires(@Color.0 == Red && is_pos(@Int.0))\n"
               "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n"),
    "g.vera": ("public fn is_pos(@Int -> @Bool)\n" + _H + "  @Int.0 > 0\n}\n\n"
               "public forall<T> fn h(@T, @Int -> @Int)\n"
               "  requires(is_pos(@Int.0))\n  ensures(true)\n  effects(pure)\n"
               "{\n  @Int.0\n}\n"),
}
NAMED_CLAUSES: dict[str, tuple[dict[str, str], str]] = {
    "imported_constructor_and_function": (
        {"main.vera": "import m(h, Color, Green);\n\npublic fn caller(@Int -> @Int)\n"
         + _H + "  h(Green, 0)\n}\n", "m.vera": _NAMED_CALLEE["m.vera"]},
        "requires(@Color.0 == Red && is_pos(@Int.0))"),
    "imported_generic": (
        {"main.vera": "import g(h);\n\npublic fn caller(@Int -> @Int)\n" + _H
         + "  h(true, 0)\n}\n", "g.vera": _NAMED_CALLEE["g.vera"]},
        "requires(is_pos(@Int.0))"),
    "where_helper": (
        {"main.vera": "public fn outer(@Int -> @Int)\n" + _H + "  inner(0)\n}\n"
         "where {\n  fn ok(@Int -> @Bool)\n    requires(true)\n    ensures(true)\n"
         "    effects(pure)\n  {\n    @Int.0 > 0\n  }\n"
         "  fn inner(@Int -> @Int)\n    requires(ok(@Int.0))\n    ensures(true)\n"
         "    effects(pure)\n  {\n    @Int.0\n  }\n}\n"},
        "requires(ok(@Int.0))"),
}


@pytest.mark.parametrize("cell", sorted(NAMED_CLAUSES))
def test_e501_names_what_the_clause_calls_as_written(
        cell: str, tmp_path: Path) -> None:
    files, clause = NAMED_CLAUSES[cell]
    _, _, diag = _run(tmp_path, files, command="verify")
    assert diag["error_code"] == "E501", diag
    assert f"  Precondition: {clause}\n" in diag["description"] + "\n", (
        diag["description"])
    assert "$" not in diag["description"]


#: A message that quotes a call out of the TYPED program (E533, E139) keeps
#: the source's text: the typed program's call carries its link name, which
#: the canonical form would print.
_PROBES = Path(__file__).resolve().parent / "probes" / "state_handlers" / (
    "checker_gates")


@pytest.mark.parametrize(("probe", "call"), [
    ("e533_import.vera", "'sneak(@Int.0)'"),
    ("e533_where.vera", "'ghelper(@Int.0)'"),
])
def test_a_typed_program_call_is_quoted_as_written(probe: str,
                                                   call: str) -> None:
    envelope = pipeline.cli("check", "--json", _PROBES / probe).json()
    (diag,) = [d for d in envelope["diagnostics"] if d["error_code"] == "E533"]
    assert f"The call {call} instantiates" in diag["description"], diag
    assert "$" not in diag["description"]


def test_a_growing_call_in_a_module_is_quoted_as_written(
        tmp_path: Path) -> None:
    """E139's call, in a module, where its link name is `mod$m$grow`."""
    module = ("public forall<T> fn grow(@T, @Nat -> @Nat)\n  requires(true)\n"
              "  ensures(true)\n  decreases(@Nat.0)\n  effects(pure)\n{\n"
              "  if @Nat.0 == 0 then {\n    0\n  } else {\n"
              "    grow(Some(@T.0), @Nat.0 - 1)\n  }\n}\n")
    main = ("import m(grow);\n\npublic fn f(@Nat -> @Nat)\n" + _H
            + "  grow(1, @Nat.0)\n}\n")
    _, _, diag = _run(tmp_path, {"main.vera": main, "m.vera": module})
    assert diag["error_code"] == "E139", diag
    assert diag["description"].startswith(
        "The call 'grow(Some(@T.0), @Nat.0 - 1)' in 'grow' instantiates"), diag
    assert "$" not in diag["description"]


# =====================================================================
# Every registered code can be raised
# =====================================================================

#: (module text, whether E999 is raisable from it).
RAISE_SHAPES: dict[str, tuple[str, bool]] = {
    "a function no code names": (
        "def make():\n    return 'E999'\n", False),
    "a function only itself names": (
        "def make(n):\n    return make(n - 1) if n else 'E999'\n", False),
    "a function only a dead function names": (
        "def make():\n    return 'E999'\n\ndef outer():\n    return make()\n",
        False),
    "a function live code names": (
        "def make():\n    return 'E999'\n\nX = make\n", True),
    "a module-level table": ("CODES = {'k': 'E999'}\n", True),
    "a method": (
        "class C:\n    def m(self):\n        return 'E999'\n", True),
    "no site at all": ("X = 1\n", False),
    "two functions that only call each other": (
        "def a():\n    return b() or 'E999'\n\ndef b():\n    return a()\n",
        False),
    "a cycle live code reaches": (
        "def a():\n    return b() or 'E999'\n\ndef b():\n    return a()\n"
        "\nX = a\n", True),
}
# What Python evaluates when a `def` runs, whether or not the function is
# ever called: each row's answer is what running the module shows (`make`
# runs at import, or it does not), on every Python the project supports.
_MAKE = "def make(*a):\n    return 'E999'\n\n"
RAISE_SHAPES.update({
    "a positional default": (
        _MAKE + "def unused(code=make()):\n    pass\n", True),
    "a positional-only default": (
        _MAKE + "def unused(code=make(), /):\n    pass\n", True),
    "a keyword-only default": (
        _MAKE + "def unused(*, code=make()):\n    pass\n", True),
    "an async function's default": (
        _MAKE + "async def unused(code=make()):\n    pass\n", True),
    "a decorator": (_MAKE + "@make\ndef unused():\n    pass\n", True),
    "a decorator's argument": (
        _MAKE + "def reg(x):\n    return lambda f: f\n\n"
        "@reg(make())\ndef unused():\n    pass\n", True),
    "a parameter's annotation": (
        _MAKE + "def unused(code: make()):\n    pass\n", True),
    "a keyword-only parameter's annotation": (
        _MAKE + "def unused(*, code: make()):\n    pass\n", True),
    "a return annotation": (
        _MAKE + "def unused() -> make():\n    pass\n", True),
    "a *args and a **kwargs annotation": (
        _MAKE + "def unused(*a: make(), **k: make()):\n    pass\n", True),
    "an annotation the future import defers": (
        "from __future__ import annotations\n" + _MAKE
        + "def unused(code: make()):\n    pass\n", False),
    "a default naming the code itself": (
        "def unused(code='E999'):\n    pass\n", True),
    "the body of a function with a default": (
        _MAKE + "def unused(code=1):\n    return make()\n", False),
    "a default of a function nested in a dead one": (
        _MAKE + "def outer():\n    def inner(code=make()):\n        pass\n",
        False),
    "a decorator inside a dead function": (
        _MAKE + "def outer():\n    @make\n    class K:\n        pass\n", False),
})
if sys.version_info >= (3, 12):
    RAISE_SHAPES["a type parameter's bound, evaluated lazily"] = (
        _MAKE + "def unused[T: make()]():\n    pass\n", False)


@pytest.mark.parametrize("shape", sorted(RAISE_SHAPES))
def test_the_gate_refuses_a_code_nothing_can_raise(
        shape: str, tmp_path: Path) -> None:
    text, raisable = RAISE_SHAPES[shape]
    module = tmp_path / "m.py"
    module.write_text(text, encoding="utf-8")
    found = _gate().unraised_code_violations([module], {"E999"})
    assert (found == []) == raisable, (shape, found)


#: A name bound to a function under another file's or another name's
#: binding, one row per binding form the language reference gives that can
#: hold a function (an import, with and without `as`, of a module or of a
#: name; an assignment, plain, annotated and `:=`; a `for` target): the
#: modules, by file, and whether E999, which `a.py`'s `emit` returns, is
#: raisable.  The scan resolves each name to the definitions it is bound to
#: before it walks what names them.
_EMIT = {"a.py": "def emit():\n    return 'E999'\n"}
BINDING_SHAPES: dict[str, tuple[dict[str, str], bool]] = {
    "from a import emit, then emit()": (
        {**_EMIT, "b.py": "from a import emit\n\nX = emit()\n"}, True),
    "from a import emit as report, then report()": (
        {**_EMIT, "b.py": "from a import emit as report\n\nX = report()\n"},
        True),
    "from a import emit as report, never used": (
        {**_EMIT, "b.py": "from a import emit as report\n"}, False),
    "from a import emit as report, used only by a dead function": (
        {**_EMIT, "b.py": "from a import emit as report\n\n"
                          "def dead():\n    return report()\n"}, False),
    "from a import emit as report inside a live function": (
        {**_EMIT, "b.py": "def go():\n    from a import emit as report\n"
                          "    return report()\n\nX = go()\n"}, True),
    "a renamed import of a renamed import": (
        {**_EMIT, "b.py": "from a import emit as r1\n",
         "c.py": "from b import r1 as r2\n\nX = r2()\n"}, True),
    "two imports that rename each other, and no definition": (
        {"a.py": "from b import g as f\n", "b.py": "from a import f as g\n"
         "\nX = g()\n\nY = 'E999'.lower\n"}, True),
    "import a as n, then n.emit()": (
        {**_EMIT, "b.py": "import a as n\n\nX = n.emit()\n"}, True),
    "import a, then a.emit()": (
        {**_EMIT, "b.py": "import a\n\nX = a.emit()\n"}, True),
    "from a import *, then emit()": (
        {**_EMIT, "b.py": "from a import *\n\nX = emit()\n"}, True),
    "report = emit at module scope": (
        {**_EMIT, "b.py": "from a import emit\n\nreport = emit\n"}, True),
    "report: object = emit at module scope": (
        {**_EMIT, "b.py": "from a import emit\n\nreport: object = emit\n"},
        True),
    "(report := emit) at module scope": (
        {**_EMIT, "b.py": "from a import emit\n\nX = (report := emit)\n"},
        True),
    "for report in (emit,) at module scope": (
        {**_EMIT, "b.py": "from a import emit\n\n"
                          "for report in (emit,):\n    report()\n"}, True),
    "report = emit inside a dead function": (
        {**_EMIT, "b.py": "from a import emit\n\n"
                          "def dead():\n    report = emit\n    return report()\n"},
        False),
    "report = emit inside a live function": (
        {**_EMIT, "b.py": "from a import emit\n\n"
                          "def go():\n    report = emit\n    return report()\n"
                          "\nX = go()\n"}, True),
    # A binding belongs to the scope that makes it: an import in a function
    # binds its name only while that function runs.
    "a renamed import in a dead function, the name live at module scope": (
        {**_EMIT, "b.py": "report = 0\n\n"
                          "def dead():\n    from a import emit as report\n"
                          "    return report()\n"}, False),
    "a renamed import in a live function, the name live at module scope": (
        {**_EMIT, "b.py": "report = 0\n\n"
                          "def go():\n    from a import emit as report\n"
                          "    return report()\n\nX = go()\n"}, True),
    "a renamed import in a dead function, the name bound nowhere else": (
        {**_EMIT, "b.py": "def dead():\n    from a import emit as report\n"
                          "    return report()\n"}, False),
    # KNOWN LIMIT, the one way the scan errs toward accepting: it matches a
    # function by its name across vera/, so a live use of the same name
    # (another function, an attribute, a variable) keeps a dead function
    # live.  The row pins what the scan does, not what Python does.
    "KNOWN LIMIT: a live use of the same name elsewhere keeps it": (
        {**_EMIT, "b.py": "class C:\n    emit = 1\n\nX = C().emit\n"}, True),
}


@pytest.mark.parametrize("shape", sorted(BINDING_SHAPES))
def test_the_raise_rule_follows_a_name_to_its_definition(
        shape: str, tmp_path: Path) -> None:
    files, raisable = BINDING_SHAPES[shape]
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    found = _gate().unraised_code_violations(
        [tmp_path / name for name in sorted(files)], {"E999"})
    assert (found == []) == raisable, (shape, found)


def test_the_raise_rule_reports_a_name_it_cannot_see() -> None:
    """The scan's stated limit: a function reached only through a name no
    code writes (`getattr` with a string here; a string, a table built at
    run time) is dead to it, so its code IS reported, and the report says
    how to make the site visible."""
    import tempfile

    with tempfile.TemporaryDirectory() as tmp:
        a, b = Path(tmp) / "a.py", Path(tmp) / "b.py"
        a.write_text(_EMIT["a.py"], encoding="utf-8")
        b.write_text("import a\n\nX = getattr(a, 'em' + 'it')()\n",
                     encoding="utf-8")
        (found,) = _gate().unraised_code_violations([a, b], {"E999"})
    assert found.missing == [
        "E999 is registered in ERROR_CODES, but no live site in vera/ can "
        "raise it: remove its entry (and vera/_since.py's), or raise it.  "
        "A site the scan cannot see (a function reached only through "
        "getattr, a string, or a table built at run time) is reported too: "
        "name that function from module-level code or a method"]


def test_every_registered_code_can_be_raised() -> None:
    root = Path(__file__).resolve().parent.parent
    gate = _gate()
    registry = gate._load_error_codes(root / "vera" / "errors.py")
    assert gate.unraised_code_violations(
        gate.iter_vera_files(root / "vera"), registry) == []
    assert "E003" not in ERROR_CODES and "E004" not in ERROR_CODES
