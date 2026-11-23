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
    "E003": "registered, but no site in vera/ raises it: a malformed slot "
            "is E005",
    "E004": "registered, but no site in vera/ raises it: a missing brace is "
            "E005",
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
