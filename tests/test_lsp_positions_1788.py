"""Every place the language server turns a compiler location into a
protocol position (#1788, #1637).

A compiler location is (file, 1-based line, 1-based code-point column),
with lines cut wherever the CLI's reader (`vera.parser.read_source`) cuts
them.  A protocol position is (document, 0-based line, 0-based UTF-16 code
unit), with lines cut at ``\\n``, ``\\r\\n`` and a lone ``\\r`` (LSP 3.17,
"Position" and "Text Documents").  The class is every published position
or range, by:

* the surface: a diagnostic of the document, a diagnostic of the
  transform stage (which carries no file), a diagnostic of a module the
  document imports directly or only reaches through another module, the
  E024 of an imported module the resolver could not read, the
  tier hint, hover, go-to-definition, completion, and the two text
  positions the edit methods compute (the whole-document range and the
  splice offsets of `vera/strengthenContract` and `vera/addEffect`);
* the line-end style: LF, CRLF, lone CR, a mixed document, and a mixed
  document with a lone CR inside a string literal (the grammar lets a
  string span lines);
* whether a character outside the Basic Multilingual Plane stands before
  the column on its line;
* whether the buffer begins with a byte-order mark, which the reader drops
  and the buffer counts, with the positions on later lines or, with the
  whole program written on line 0, on the line the mark shifts.

The oracle is independent of the converter: the expected position is
computed here from `vera check --json`'s location for the same file on
disk, by splitting the text at the protocol's line ends and counting
UTF-16 units.  A diagnostic carries a point and no end, so the published
range is the point widened over the identifier token under it (the
characters a slot reference or a name is made of), or one character when
the point is on no such token, or empty at the end of a line; the oracle
widens with its own pattern, so a start that moves without its end, or
the reverse, is a wrong range in every cell.
"""

from __future__ import annotations

import json
import pathlib
import re

import pytest
from lsprotocol import types as lsp

from tests import pipeline
from vera.lsp.documents import Document
from vera.lsp.features import (
    analyze,
    completion_at,
    definition_at,
    hover_at,
    to_lsp_diagnostics,
)
from vera.lsp.workflows import (
    effect_row_rewrite,
    full_document_range,
    splice_contract,
)
from vera.obligations.session import VerificationSession

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of its parametrised cells, and all of them when it changes this file or a
# module that decides a published position: the converters, the analysis
# that hands the compiler its text and places each diagnostic, the edit
# methods' text positions, and the reader whose line-end rule the server
# shares.
pytestmark = pytest.mark.matrix(decides=[
    "vera/lsp/convert.py",
    "vera/lsp/features.py",
    "vera/lsp/workflows.py",
    "vera/lsp/extensions.py",
    "vera/parser.py",
])

ASTRAL = "\U0001F389"

#: The line-end styles.  `MIXED` cycles LF, CRLF and a lone CR line by
#: line; `MIXED_STR` does the same and also puts a lone CR inside a string
#: literal on the line under test, so the column is counted on the
#: protocol line after it.
STYLES = ("LF", "CRLF", "CR", "MIXED", "MIXED_STR")

HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def lsp_lines(text: str) -> list[str]:
    """*text*'s lines as the protocol cuts them."""
    return re.split(r"\r\n|\r|\n", text)


def utf16(s: str) -> int:
    return sum(2 if ord(c) > 0xFFFF else 1 for c in s)


def with_ends(text: str, style: str) -> str:
    """*text* (written with ``\\n``) with *style*'s line ends."""
    if style == "LF":
        return text
    if style == "CRLF":
        return text.replace("\n", "\r\n")
    if style == "CR":
        return text.replace("\n", "\r")
    cycle = ("\n", "\r\n", "\r")
    pieces = text.split("\n")
    out = []
    for i, piece in enumerate(pieces[:-1]):
        out.append(piece + cycle[i % 3])
    out.append(pieces[-1])
    return "".join(out)


def prefix(astral: bool, style: str) -> str:
    """An Int-typed term and `+`, put before the column under test."""
    inner = (ASTRAL if astral else "a") + ("\rb" if style == "MIXED_STR" else "")
    return f'string_length("{inner}") + '


def offset_to_pos(text: str, offset: int) -> tuple[int, int]:
    """The protocol position of code-point *offset* in *text*."""
    line, start = 0, 0
    for m in re.finditer(r"\r\n|\r|\n", text):
        if m.end() > offset:
            break
        line, start = line + 1, m.end()
    return line, utf16(text[start:offset])


def widened(text: str, line1: int, col1: int) -> tuple[int, int, int, int]:
    """The range the oracle expects for a point diagnostic at the
    compiler's (*line1*, *col1*): its own token pattern, not the
    converter's."""
    lines = lsp_lines(text)
    line = lines[line1 - 1]
    lead = 0
    if line1 == 1 and text.startswith("\ufeff"):
        # The compiler reads the text without the mark; the buffer counts it.
        line, lead = line[1:], 1
    start = max(0, col1 - 1)
    m = re.compile(r"[A-Za-z0-9_@.À-￿]*").match(line, start)
    assert m is not None
    end = m.end()
    if end == start and start < len(line):
        end = start + 1
    return (line1 - 1, lead + utf16(line[:start]),
            line1 - 1, lead + utf16(line[:end]))


def rng(r: lsp.Range) -> tuple[int, int, int, int]:
    return (r.start.line, r.start.character, r.end.line, r.end.character)


def write(path: pathlib.Path, text: str) -> None:
    """The exact bytes, so the CLI reads the line ends the buffer has."""
    path.write_bytes(text.encode("utf-8"))


def cli(path: pathlib.Path) -> list[dict]:
    """`vera check --json`'s diagnostics for the file at *path*, the CLI
    run through `vera.cli.main` (tests/pipeline.py), reading the file's
    bytes as the command does."""
    return json.loads(pipeline.cli("check", "--json", path).stdout)[
        "diagnostics"]


# --- the programs -----------------------------------------------------

def doc_program(pfx: str) -> str:
    return ("public fn f(@Int -> @Int)\n" + HDR
            + "{\n  " + pfx + "missing(@Int.0)\n}\n")


def transform_program(pfx: str) -> str:
    return ("public fn f(@Int -> @Int)\n" + HDR
            + "{\n  " + pfx + "@Int.0 |> 1\n}\n")


def lib_program(pfx: str) -> str:
    return ("module lib;\n\npublic fn word(@Unit -> @Int)\n" + HDR
            + "{\n  " + pfx + "missing(1)\n}\n")


MAIN = ("import lib(word);\n\npublic fn main(@Unit -> @Int)\n" + HDR
        + "{\n  word(())\n}\n")

MID = ("module mid;\n\nimport lib(word);\n\npublic fn w2(@Unit -> @Int)\n"
       + HDR + "{\n  word(())\n}\n")

MAIN_T = ("import mid(w2);\n\npublic fn main(@Unit -> @Int)\n" + HDR
          + "{\n  w2(())\n}\n")


def ok_program(pfx: str) -> str:
    return ("public fn g(@Int, @Int -> @Int)\n"
            "  requires(@Int.0 > 0)\n  ensures(true)\n  effects(pure)\n"
            "{\n  " + pfx + "@Int.1 + @Int.0\n}\n")


def hole_program(pfx: str) -> str:
    return ("public fn f(@Int -> @Int)\n" + HDR + "{\n  " + pfx + "?\n}\n")


def analysed(path: pathlib.Path, text: str):
    write(path, text)
    return analyze(VerificationSession(), path.as_uri(), text)


# --- the cells --------------------------------------------------------

SURFACES = (
    "diag_document", "diag_transform", "diag_imported", "diag_transitive",
    "diag_unread",
    "hint", "hover", "definition", "completion",
    "full_document_range", "splice_contract", "effect_row",
)


BOM = "\ufeff"

#: Whether the buffer begins with a byte-order mark, and where the position
#: under test sits: `none` and `bom` keep each program's layout (the
#: position on a later line, the import and the signature on line 0);
#: `bom_line0` writes the whole program on line 0, so every position is on
#: the line the mark shifts.
MARKS = ("none", "bom", "bom_line0")


def shape(text: str, style: str, mark: str) -> str:
    """*text* (written with ``\\n``) laid out for *mark* with *style*'s
    line ends."""
    if mark == "bom_line0":
        text = " ".join(text.rstrip("\n").split("\n")) + "\n"
    text = with_ends(text, style)
    return BOM + text if mark != "none" else text


def mark_units(text: str, line0: int) -> int:
    """The UTF-16 units the buffer holds ahead of the compiler's *line0*."""
    return 1 if line0 == 0 and text.startswith(BOM) else 0


@pytest.mark.parametrize("mark", MARKS)
@pytest.mark.parametrize("astral", [False, True], ids=["bmp", "astral"])
@pytest.mark.parametrize("style", STYLES)
@pytest.mark.parametrize("surface", SURFACES)
def test_published_position(
    surface: str, style: str, astral: bool, mark: str,
    tmp_path: pathlib.Path,
) -> None:
    pfx = prefix(astral, style)
    if surface in ("diag_document", "diag_transform"):
        src = shape(
            (doc_program if surface == "diag_document"
             else transform_program)(pfx), style, mark)
        path = tmp_path / "t.vera"
        a = analysed(path, src)
        (want,) = cli(path)
        loc = want["location"]
        got = [rng(d.range) for d in to_lsp_diagnostics(a)
               if d.code == want["error_code"]]
        assert got == [widened(src, loc["line"], loc["column"])], (
            want, got)
        return

    if surface in ("diag_imported", "diag_transitive", "diag_unread"):
        # The module carries the document's mark too, so the related
        # location into it is converted against a marked buffer: with its
        # error on a later line, or (`bom_line0`) on its line 0.
        lib = shape(lib_program(pfx), style, mark)
        if surface == "diag_unread":
            # Not UTF-8: the resolver reads no module, and the E024 is
            # located in the module's file (#1666).
            (tmp_path / "lib.vera").write_bytes(
                lib.replace("missing(1)", "1").encode("utf-8") + b"\xe9")
        else:
            write(tmp_path / "lib.vera", lib)
        if surface == "diag_transitive":
            write(tmp_path / "mid.vera", with_ends(MID, style))
            main, head = shape(MAIN_T, style, mark), "import mid(w2);"
        else:
            main, head = shape(MAIN, style, mark), "import lib(word);"
        code = "E024" if surface == "diag_unread" else "E200"
        path = tmp_path / "main.vera"
        a = analysed(path, main)
        (want,) = [d for d in cli(path) if d["error_code"] == code]
        loc = want["location"]
        assert pathlib.Path(loc["file"]).name == "lib.vera"
        (pub,) = [d for d in to_lsp_diagnostics(a, related_information=True)
                  if d.code == code]
        # Published on the import that brings the module in, whole.
        m = mark_units(main, 0)
        assert rng(pub.range) == (0, m, 0, m + utf16(head)), pub
        # Named the way `vera check` names it.
        assert pub.message.startswith(
            f"In imported module {loc['file']}, line {loc['line']}, "
            f"column {loc['column']}: "), pub.message
        if surface == "diag_unread":
            assert pub.related_information is None  # no text was read
        else:
            # Linked to the module's own line and column, as a buffer of
            # the module counts them, its mark included.
            (rel,) = pub.related_information or []
            assert rel.location.uri == pathlib.Path(loc["file"]).as_uri()
            assert rng(rel.location.range) == widened(
                lib, loc["line"], loc["column"])
        return

    if surface in ("hint", "hover", "definition", "completion"):
        src = shape(
            (hole_program if surface == "completion" else ok_program)(pfx),
            style, mark)
        path = tmp_path / "g.vera"
        a = analysed(path, src)
        if surface == "hint":
            (hint,) = [d for d in to_lsp_diagnostics(a) if d.code == "tier"]
            want_line = next(i for i, ln in enumerate(lsp_lines(src))
                             if "requires(" in ln)
            assert rng(hint.range) == (want_line, 0, want_line, 0)
        elif surface == "hover":
            off = src.rindex("@Int.0")
            line, ch = offset_to_pos(src, off)
            h = hover_at(a, lsp.Position(line=line, character=ch))
            assert h is not None
            assert rng(h.range) == (line, ch, line, ch + 6)
            assert "Int" in h.contents.value
        elif surface == "definition":
            off = src.rindex("@Int.0")
            line, ch = offset_to_pos(src, off)
            df = definition_at(a, lsp.Position(line=line, character=ch))
            # The control: the same program with LF ends and no mark, whose
            # line 0 the line-end style cannot move; the mark moves it one
            # unit right.
            control = analysed(tmp_path / "control.vera", ok_program(pfx))
            off0 = ok_program(pfx).rindex("@Int.0")
            line0, ch0 = offset_to_pos(ok_program(pfx), off0)
            want = definition_at(
                control, lsp.Position(line=line0, character=ch0))
            assert want is not None and df is not None
            m = mark_units(src, 0)
            w = rng(want.range)
            assert rng(df.range) == (w[0], w[1] + m, w[2], w[3] + m)
            assert df.uri == path.as_uri()
        else:
            off = src.rindex("?") + 1
            line, ch = offset_to_pos(src, off)
            c = completion_at(a, lsp.Position(line=line, character=ch))
            assert c is not None
            assert [i.label for i in c.items] == ["@Int.0"]
        return

    src = shape(ok_program(pfx), style, mark)
    if surface == "full_document_range":
        r = full_document_range(Document(uri="file:///x.vera", text=src))
        lines = lsp_lines(src)
        assert rng(r) == (0, 0, len(lines) - 1, utf16(lines[-1]))
        return
    a = analysed(tmp_path / "g.vera", src)
    assert a.program is not None
    if surface == "splice_contract":
        cand = splice_contract(a.program, a.text, "g", "requires",
                               "@Int.0 > 1")
        assert cand == src.replace("requires(@Int.0 > 0)",
                                   "requires(@Int.0 > 1)")
    else:
        (fn,) = [t.decl for t in a.program.declarations]
        start, end, new = effect_row_rewrite(a.text, fn, "IO")
        assert a.text[:start] + new + a.text[end:] == src.replace(
            "effects(pure)", "effects(<IO>)")


# --- the reported instances and the pins (every PR runs these) ---------

def test_repro_1637_range_starts_at_the_cli_column(
    tmp_path: pathlib.Path,
) -> None:
    """The issue's program: `E200` at line 6, column 3, under the `m` of
    `missing`; the range covered `issing`."""
    src = ("public fn f(@Int -> @Int)\n" + HDR
           + "{\n  missing(@Int.0)\n}\n")
    path = tmp_path / "f.vera"
    a = analysed(path, src)
    (want,) = cli(path)
    assert (want["location"]["line"], want["location"]["column"]) == (6, 3)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (5, 2, 5, 9)


def test_repro_1788_an_imported_modules_diagnostic(
    tmp_path: pathlib.Path,
) -> None:
    """The issue's programs: `E121` at `lib.vera` line 8 was published on
    `main.vera` line 8, `  IO.print(word(()));`."""
    (tmp_path / "lib.vera").write_text(
        "module lib;\n\npublic fn word(@Unit -> @String)\n" + HDR
        + "{\n  42\n}\n", encoding="utf-8")
    main = ("import lib(word);\n\npublic fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"
            "{\n  IO.print(word(()));\n  0\n}\n")
    path = tmp_path / "main.vera"
    a = analysed(path, main)
    (want,) = [d for d in cli(path) if d["error_code"] == "E121"]
    loc = want["location"]
    (got,) = [d for d in to_lsp_diagnostics(a, related_information=True)
              if d.code == "E121"]
    assert rng(got.range) == (0, 0, 0, len("import lib(word);"))
    assert got.message.startswith(
        f"In imported module {loc['file']}, line 8, column 3: ")
    (rel,) = got.related_information or []
    assert rel.location.uri == pathlib.Path(loc["file"]).as_uri()
    assert rng(rel.location.range) == (7, 2, 7, 4)


def test_repro_1788_a_lone_cr_document(tmp_path: pathlib.Path) -> None:
    """The checklist line: a document whose line ends are lone carriage
    returns was handed to the parser as one line."""
    src = ("public fn f(@Int -> @Int)\n" + HDR
           + "{\n  missing(@Int.0)\n}\n").replace("\n", "\r")
    a = analysed(tmp_path / "f.vera", src)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (5, 2, 5, 9)


def test_repro_1788_a_lone_cr_whole_document_range() -> None:
    """An applied edit replaced only the first line of a lone-CR buffer:
    its range ended at line 0."""
    text = "a\rb\rcc"
    r = full_document_range(Document(uri="file:///x.vera", text=text))
    assert rng(r) == (0, 0, 2, 2)


def test_repro_1788_a_transitive_modules_diagnostic(
    tmp_path: pathlib.Path,
) -> None:
    """A module the document reaches only through another module is
    published on the import of the module that reaches it."""
    write(tmp_path / "lib.vera", lib_program(""))
    write(tmp_path / "mid.vera", MID)
    a = analysed(tmp_path / "main.vera", MAIN_T)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (0, 0, 0, len("import mid(w2);"))


def test_repro_1788_an_unread_modules_e024(tmp_path: pathlib.Path) -> None:
    """A module that is not UTF-8 is never read, so no resolved module
    names its file: its E024 is published on the import that names it."""
    (tmp_path / "lib.vera").write_bytes(
        lib_program("").replace("missing(1)", "1").encode("utf-8") + b"\xe9")
    a = analysed(tmp_path / "main.vera", "\n\n" + MAIN)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E024"]
    assert rng(got.range) == (2, 0, 2, len("import lib(word);"))


def test_a_lone_cr_diagnostic_quotes_the_text_the_cli_quotes(
    tmp_path: pathlib.Path,
) -> None:
    """A diagnostic that quotes the program (E135's fix writes the type
    out from its span) quotes what `vera check` quotes: the checker is
    handed the text the spans were read from."""
    src = (ok_program("") + "\npublic fn h(@Map<Array<Int>, Int> -> @Int)\n"
           + HDR + "{\n  0\n}\n").replace("\n", "\r")
    path = tmp_path / "h.vera"
    a = analysed(path, src)
    (want,) = [d for d in cli(path) if d["error_code"] == "E135"]
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E135"]
    assert "replace 'Map<Array<Int>, Int>'" in want["fix"]
    assert got.message == (f"{want['description']}\n\n{want['rationale']}"
                           f"\n\nFix: {want['fix']}")
    loc = want["location"]
    assert rng(got.range) == widened(src, loc["line"], loc["column"])


ONE_LINE_OK = ("public fn g(@Int, @Int -> @Int) requires(@Int.0 > 0) "
               "ensures(true) effects(pure) { @Int.1 + @Int.0 }\n")


def test_repro_a_buffer_that_begins_with_a_byte_order_mark(
    tmp_path: pathlib.Path,
) -> None:
    """The find of this change's first report: a buffer beginning with
    U+FEFF was handed to the parser whole and drew `E006` at its start,
    where `vera check` on the same bytes, which drops the mark, is clean."""
    src = BOM + ok_program("")
    path = tmp_path / "g.vera"
    a = analysed(path, src)
    assert cli(path) == []
    codes = [d.code for d in to_lsp_diagnostics(a)]
    assert codes == ["tier"], codes


def test_a_marked_buffers_line_0_diagnostic_is_one_unit_right(
    tmp_path: pathlib.Path,
) -> None:
    """Compiler to client: `E200` at the compiler's line 1, column C is at
    the buffer's character C, one past the compiler's C - 1, because the
    buffer holds the mark."""
    src = BOM + ("public fn f(@Int -> @Int) requires(true) ensures(true) "
                 "effects(pure) { missing(@Int.0) }\n")
    path = tmp_path / "f.vera"
    a = analysed(path, src)
    (want,) = cli(path)
    col = want["location"]["column"]
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (0, col, 0, col + len("missing"))


def test_a_marked_buffers_line_0_hover_reads_one_unit_left(
    tmp_path: pathlib.Path,
) -> None:
    """Client to compiler: the cursor on the buffer's `@` of the last
    `@Int.0` finds the slot, and its range is the buffer's."""
    src = BOM + ONE_LINE_OK
    a = analysed(tmp_path / "g.vera", src)
    ch = src.rindex("@Int.0")
    h = hover_at(a, lsp.Position(line=0, character=ch))
    assert h is not None
    assert rng(h.range) == (0, ch, 0, ch + 6)
    # One unit left of the slot is the space before it: no slot there.
    d = definition_at(a, lsp.Position(line=0, character=ch - 1))
    assert d is None


def test_a_marked_buffers_line_0_splice_keeps_the_mark(
    tmp_path: pathlib.Path,
) -> None:
    """An edit's span on line 0 is one further on in the buffer."""
    src = BOM + ONE_LINE_OK
    a = analysed(tmp_path / "g.vera", src)
    assert a.program is not None
    cand = splice_contract(a.program, a.text, "g", "requires", "@Int.0 > 1")
    assert cand == src.replace("requires(@Int.0 > 0)", "requires(@Int.0 > 1)")


def test_a_marked_one_line_buffers_whole_range_counts_the_mark() -> None:
    r = full_document_range(Document(uri="file:///x.vera", text=BOM + "ab"))
    assert rng(r) == (0, 0, 0, 3)


#: The import orders whose placement a first-match rule gets wrong: two
#: modules whose paths end alike, each order, and a module the document
#: imports directly that another of its imports also imports, each order.
#: Each names the imports in order and the module that fails.
_ORDERS = {
    "lib_then_alib": (("lib", "a.lib"), "a.lib"),
    "alib_then_lib": (("a.lib", "lib"), "lib"),
    "mid_then_lib": (("mid", "lib"), "lib"),
    "lib_then_mid": (("lib", "mid"), "lib"),
}


def _order_tree(tmp_path: pathlib.Path, order: str, failing: str,
                unread: bool) -> tuple[pathlib.Path, str, int]:
    """The program for *order*: its main, its source, and the line of the
    import that names the failing module directly."""
    imports, bad = _ORDERS[order]
    (tmp_path / "a").mkdir(exist_ok=True)
    for name in ("lib", "a.lib"):
        rel = pathlib.Path(*name.split(".")).with_suffix(".vera")
        text = lib_program("").replace("module lib;", f"module {name};")
        if name == bad:
            if unread:
                (tmp_path / rel).write_bytes(
                    text.replace("missing(1)", "1").encode("utf-8")
                    + b"\xe9")
                continue
        else:
            text = text.replace("missing(1)", "1")
        write(tmp_path / rel, text)
    write(tmp_path / "mid.vera", MID.replace("word(())", "1"))
    names = {"lib": "word", "a.lib": "word", "mid": "w2"}
    main = "".join(f"import {m}({names[m]});\n" for m in imports) + (
        "\npublic fn main(@Unit -> @Int)\n" + HDR + "{\n  0\n}\n")
    path = tmp_path / "main.vera"
    return path, main, imports.index(bad)


@pytest.mark.parametrize("unread", [False, True], ids=["checked", "unread"])
@pytest.mark.parametrize("order", list(_ORDERS))
def test_the_import_that_names_a_module_carries_its_diagnostics(
    order: str, unread: bool, tmp_path: pathlib.Path,
) -> None:
    """A module's diagnostic is published on the document's import that
    names it, whatever the import order: by the file the import resolves
    to, not its last name, and the document's own import before one a
    module it imports makes."""
    path, main, line = _order_tree(tmp_path, order, _ORDERS[order][1],
                                   unread)
    a = analysed(path, main)
    code = "E024" if unread else "E200"
    want = [d for d in cli(path) if d["error_code"] == code]
    got = [d for d in to_lsp_diagnostics(a) if d.code == code]
    assert want and len(got) == len(want)
    head = lsp_lines(main)[line]
    assert {rng(d.range) for d in got} == {(line, 0, line, utf16(head))}


def _bound_tree(tmp_path: pathlib.Path, unread: bool) -> tuple[pathlib.Path, str]:
    """`main` imports `a.mid` then `lib`; `a/mid.vera` imports `lib`, which
    resolves beside it to `a/lib.vera`, the module that fails; a root
    `lib.vera` reads.  The resolver binds a path once, so a read
    `a/lib.vera` is what `main`'s `import lib` is bound to; an unread one
    is cached by nobody, and `main`'s `import lib` reads the root file."""
    (tmp_path / "a").mkdir(exist_ok=True)
    write(tmp_path / "lib.vera", lib_program("").replace("missing(1)", "1"))
    bad = lib_program("")
    if unread:
        (tmp_path / "a" / "lib.vera").write_bytes(
            bad.replace("missing(1)", "1").encode("utf-8") + b"\xe9")
    else:
        write(tmp_path / "a" / "lib.vera", bad)
    write(tmp_path / "a" / "mid.vera",
          MID.replace("module mid;", "module a.mid;").replace("word(())", "1"))
    main = ("import a.mid(w2);\nimport lib(word);\n\n"
            "public fn main(@Unit -> @Int)\n" + HDR + "{\n  0\n}\n")
    return tmp_path / "main.vera", main


@pytest.mark.parametrize("unread", [False, True], ids=["checked", "unread"])
def test_a_module_is_placed_by_the_resolvers_binding(
    unread: bool, tmp_path: pathlib.Path,
) -> None:
    """Placement reads what the resolver bound and repeats no lookup: a
    read `a/lib.vera` is `main`'s `import lib` (line 1), and an unread one
    is only `a.mid`'s, by the resolver's record (line 0)."""
    path, main = _bound_tree(tmp_path, unread)
    a = analysed(path, main)
    code = "E024" if unread else "E200"
    (want,) = [d for d in cli(path) if d["error_code"] == code]
    assert pathlib.Path(want["location"]["file"]).parts[-2:] == (
        "a", "lib.vera")
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == code]
    line = 0 if unread else 1
    head = lsp_lines(main)[line]
    assert rng(got.range) == (line, 0, line, utf16(head))


def test_repro_cr4_placement_reads_the_resolvers_binding(
    tmp_path: pathlib.Path,
) -> None:
    """The second review's shape: the compiler binds `main`'s `import lib`
    to `a/lib.vera`; a second lookup resolved it to the root `lib.vera`,
    and `a/lib.vera`'s E200 was published on `import a.mid`."""
    path, main = _bound_tree(tmp_path, unread=False)
    a = analysed(path, main)
    bound = {m.path: m.file_path for m in a.modules}
    assert bound[("lib",)] == (tmp_path / "a" / "lib.vera").resolve()
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (1, 0, 1, len("import lib(word);"))


def test_repro_cr4_an_unread_module_is_placed_by_the_resolvers_record(
    tmp_path: pathlib.Path,
) -> None:
    """The same tree with `a/lib.vera` not UTF-8: only `a.mid`'s import
    failed (the resolver records that importer, path and file), and
    `main`'s `import lib` read the root file, so the E024 is on
    `import a.mid`."""
    path, main = _bound_tree(tmp_path, unread=True)
    a = analysed(path, main)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E024"]
    assert rng(got.range) == (0, 0, 0, len("import a.mid(w2);"))


def _branch_tree(
    tmp_path: pathlib.Path, first: str = "a.mid",
) -> tuple[pathlib.Path, str]:
    """`main` imports *first* then `b.mid`; `b.mid` imports `lib`, which
    resolves beside it to `b/lib.vera`.  With *first* `a.mid`, `a.mid`
    imports `lib` too, beside it, and `a/lib.vera` is not UTF-8; with
    *first* `lib`, the document imports `lib` itself, and the root
    `lib.vera` is not UTF-8.  Either way the resolver records the first
    import as unread and caches nothing; `b/lib.vera` reads, is what the
    path `lib` is bound to, and imports a missing module (E012 in
    `b/lib.vera`) and `c`, beside it, whose body draws E200."""
    for sub in ("a", "b"):
        (tmp_path / sub).mkdir(exist_ok=True)
        write(tmp_path / sub / "mid.vera",
              MID.replace("module mid;", f"module {sub}.mid;")
              .replace("fn w2(", f"fn w{sub}(").replace("word(())", "1"))
    plain = lib_program("").replace("missing(1)", "1")
    unread = tmp_path / ("a/lib.vera" if first == "a.mid" else "lib.vera")
    unread.write_bytes(plain.encode("utf-8") + b"\xe9")
    write(tmp_path / "b" / "lib.vera", plain.replace(
        "module lib;\n", "module lib;\n\nimport nosuch;\nimport c(cf);\n"))
    write(tmp_path / "b" / "c.vera",
          lib_program("").replace("module lib;", "module c;")
          .replace("fn word(", "fn cf("))
    head = "import a.mid(wa);" if first == "a.mid" else "import lib(word);"
    main = (head + "\nimport b.mid(wb);\n\n"
            "public fn main(@Unit -> @Int)\n" + HDR + "{\n  0\n}\n")
    return tmp_path / "main.vera", main


@pytest.mark.parametrize("first", ["a.mid", "lib"])
@pytest.mark.parametrize(("code", "line"), [
    ("E024", 0),  # the unread file: the first import, by the record
    ("E012", 1),  # in b/lib.vera, which only b.mid's import read
    ("E200", 1),  # in b/c.vera, reached through b/lib.vera alone
])
def test_an_unread_import_binds_only_the_file_it_could_not_read(
    code: str, line: int, first: str, tmp_path: pathlib.Path,
) -> None:
    """Two branches import one path, and the first branch's import does
    not read: that import is bound to the file it could not read and to
    nothing else, and the walk does not pass through it into the module
    the path is bound to through the second branch (#1904's one path, two
    files), whether the module or the document made the failed import."""
    path, main = _branch_tree(tmp_path, first)
    a = analysed(path, main)
    want = [d for d in cli(path) if d["error_code"] == code]
    got = [d for d in to_lsp_diagnostics(a) if d.code == code]
    assert want and len(got) == len(want)
    head = lsp_lines(main)[line]
    assert {rng(d.range) for d in got} == {(line, 0, line, utf16(head))}


def test_repro_cr5_an_unread_import_does_not_take_the_paths_binding(
    tmp_path: pathlib.Path,
) -> None:
    """The third review's shape: `b/lib.vera`'s E012 was published on
    `import a.mid`, whose failed import matched the path's binding."""
    path, main = _branch_tree(tmp_path)
    a = analysed(path, main)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E012"]
    assert rng(got.range) == (1, 0, 1, len("import b.mid(wb);"))


def test_repro_cr5_the_walk_stops_at_an_unread_import(
    tmp_path: pathlib.Path,
) -> None:
    """And a module reached through `b/lib.vera` (`b/c.vera`) is not
    reached through `a.mid`'s failed import either."""
    path, main = _branch_tree(tmp_path)
    a = analysed(path, main)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (1, 0, 1, len("import b.mid(wb);"))


def test_the_walk_stops_at_the_documents_own_unread_import(
    tmp_path: pathlib.Path,
) -> None:
    """The document's own import of `lib` does not read, and `b.mid`'s
    does: `b/c.vera`, reached through `b/lib.vera`, is `import b.mid`'s,
    not reached through the document's failed `import lib`."""
    path, main = _branch_tree(tmp_path, "lib")
    a = analysed(path, main)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (1, 0, 1, len("import b.mid(wb);"))


def test_repro_cr1_an_unread_module_is_placed_by_its_file(
    tmp_path: pathlib.Path,
) -> None:
    """`main` imports `lib` before `a.lib`, and `a/lib.vera` is not UTF-8:
    its E024 was published on `import lib`, the first import whose last
    name matched."""
    path, main, line = _order_tree(tmp_path, "lib_then_alib", "a.lib", True)
    a = analysed(path, main)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E024"]
    assert rng(got.range) == (1, 0, 1, len("import a.lib(word);"))


def test_repro_cr2_the_documents_own_import_before_a_modules(
    tmp_path: pathlib.Path,
) -> None:
    """`main` imports `mid` before `lib`, `mid` imports `lib`, and
    `lib.vera` is not UTF-8: its E024 (reported once per importer, as
    `vera check` reports it) was published on `import mid`."""
    path, main, line = _order_tree(tmp_path, "mid_then_lib", "lib", True)
    a = analysed(path, main)
    got = [d for d in to_lsp_diagnostics(a) if d.code == "E024"]
    assert got and {rng(d.range) for d in got} == {
        (1, 0, 1, len("import lib(word);"))}


def test_repro_cr3_a_marked_modules_related_location_counts_its_mark(
    tmp_path: pathlib.Path,
) -> None:
    """A module whose file begins with a byte-order mark: the related
    location on its first line was one UTF-16 unit left, converted against
    the resolver's text, which has the mark dropped."""
    lib = BOM + ("module lib; public fn word(@Unit -> @Int) requires(true) "
                 "ensures(true) effects(pure) { missing(1) }\n")
    write(tmp_path / "lib.vera", lib)
    a = analysed(tmp_path / "main.vera", MAIN)
    (got,) = [d for d in to_lsp_diagnostics(a, related_information=True)
              if d.code == "E200"]
    (rel,) = got.related_information or []
    ch = lib.index("missing")
    assert rng(rel.location.range) == (0, ch, 0, ch + len("missing"))


def test_a_module_three_imports_deep(tmp_path: pathlib.Path) -> None:
    """main imports mid, mid imports low, low imports lib: lib's error is
    published on `import mid`, the walk following every level."""
    write(tmp_path / "lib.vera", lib_program(""))
    write(tmp_path / "low.vera", MID.replace("module mid;", "module low;")
          .replace("fn w2(", "fn w1("))
    write(tmp_path / "mid.vera", MID.replace("import lib(word);",
                                             "import low(w1);")
          .replace("word(())", "w1(())"))
    a = analysed(tmp_path / "main.vera", MAIN_T)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (0, 0, 0, len("import mid(w2);"))


def test_a_resolved_module_is_placed_by_its_file_not_its_name(
    tmp_path: pathlib.Path,
) -> None:
    """Two modules whose paths end alike (`lib` and `a.lib`): the error in
    `a/lib.vera` is published on `import a.lib`, which resolved that file,
    not on the first import whose last name is `lib`."""
    write(tmp_path / "lib.vera",
          "module lib;\n\npublic fn ok(@Unit -> @Int)\n" + HDR
          + "{\n  1\n}\n")
    (tmp_path / "a").mkdir()
    write(tmp_path / "a" / "lib.vera",
          lib_program("").replace("module lib;", "module a.lib;"))
    main = ("import lib(ok);\nimport a.lib(word);\n\n"
            "public fn main(@Unit -> @Int)\n" + HDR
            + "{\n  ok(()) + word(())\n}\n")
    a = analysed(tmp_path / "main.vera", main)
    (got,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert rng(got.range) == (1, 0, 1, len("import a.lib(word);"))


def test_a_lone_cr_splice_keeps_the_buffers_line_ends(
    tmp_path: pathlib.Path,
) -> None:
    """`vera/strengthenContract` splices the client's text by the spans of
    the text the compiler read: a line starts after a lone CR in both."""
    src = ok_program("").replace("\n", "\r")
    a = analysed(tmp_path / "g.vera", src)
    assert a.program is not None
    cand = splice_contract(a.program, a.text, "g", "requires", "@Int.0 > 1")
    assert cand == src.replace("requires(@Int.0 > 0)", "requires(@Int.0 > 1)")


def test_a_lone_cr_speculative_edit_of_its_own_text_changes_nothing(
    tmp_path: pathlib.Path,
) -> None:
    """The speculative run numbers lines as the analysis it is compared
    with does: the document's own text, proposed again, moves nothing."""
    from vera.lsp.extensions import speculative_edit

    src = ok_program("").replace("\n", "\r")
    path = tmp_path / "g.vera"
    write(path, src)
    session = VerificationSession()
    a = analyze(session, path.as_uri(), src)
    assert a.obligations
    out = speculative_edit(session, a.obligations, path.as_uri(), src)
    delta = out["proof_delta"]
    assert delta["removed"] == [] and delta["unchanged"] == len(a.obligations)


def test_the_server_reads_the_related_information_capability() -> None:
    """`analyze_and_publish` sends `relatedInformation` only to a client
    whose `initialize` advertised it."""
    from vera.lsp.server import create_server

    server = create_server()
    assert server.takes_related_information() is False
    for flag in (True, False, None):
        server.protocol.client_capabilities = lsp.ClientCapabilities(
            text_document=lsp.TextDocumentClientCapabilities(
                publish_diagnostics=lsp.PublishDiagnosticsClientCapabilities(
                    related_information=flag)))
        assert server.takes_related_information() is (flag is True)


def test_related_information_follows_the_client_capability(
    tmp_path: pathlib.Path,
) -> None:
    """A client that does not advertise
    `textDocument.publishDiagnostics.relatedInformation` is sent none;
    the message's prefix still names the module's file and line."""
    write(tmp_path / "lib.vera", lib_program(""))
    path = tmp_path / "main.vera"
    a = analysed(path, MAIN)
    (off,) = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    (on,) = [d for d in to_lsp_diagnostics(a, related_information=True)
             if d.code == "E200"]
    assert off.related_information is None
    assert on.related_information is not None
    assert off.message == on.message


def test_every_error_of_a_module_is_published_in_the_compilers_order(
    tmp_path: pathlib.Path,
) -> None:
    """No cap, no collapse: two errors in one module with the same code
    and message, on two lines, both publish on the import, in the order
    `vera check` gives them."""
    lib = ("module lib;\n\npublic fn word(@Unit -> @Int)\n" + HDR
           + "{\n  missing(1) +\n  missing(2) +\n  missing(3)\n}\n")
    write(tmp_path / "lib.vera", lib)
    path = tmp_path / "main.vera"
    a = analysed(path, MAIN)
    want = [d for d in cli(path) if d["error_code"] == "E200"]
    assert len(want) == 3
    got = [d for d in to_lsp_diagnostics(a) if d.code == "E200"]
    assert [d.message.split(": ", 1)[0] for d in got] == [
        f"In imported module {d['location']['file']}, line "
        f"{d['location']['line']}, column {d['location']['column']}"
        for d in want
    ]


def test_the_cli_reads_line_ends_as_it_did(tmp_path: pathlib.Path) -> None:
    """`read_source` (every command's reader) is what it was before the
    server shared its rule: LF, CRLF, lone CR, a mixed text, and a lone CR
    inside a string literal.  The expected texts are written out here, not
    computed by the helper, so a change to the helper's rule is red.
    Unparametrised, so every pull request runs it."""
    from vera.parser import read_source, source_text

    cases = [
        (b"a\nb\n", "a\nb\n"),
        (b"a\r\nb\r\n", "a\nb\n"),
        (b"a\rb\r", "a\nb\n"),
        (b"a\nb\r\nc\rd\r\r\ne\n\r", "a\nb\nc\nd\n\ne\n\n"),
        (b'x "s\rt"\r\n', 'x "s\nt"\n'),
        # The mark at the start is dropped; a second one is a character,
        # and so is one anywhere else.
        (b"\xef\xbb\xbfa\r\nb", "a\nb"),
        (b"\xef\xbb\xbf\xef\xbb\xbfa", "﻿a"),
        (b"a\xef\xbb\xbf\rb", "a﻿\nb"),
    ]
    for i, (raw, read) in enumerate(cases):
        path = tmp_path / f"t{i}.vera"
        path.write_bytes(raw)
        assert read_source(path) == read, raw
        assert source_text(raw.decode("utf-8")) == read, raw


def test_a_document_error_and_a_module_error_at_one_position(
    tmp_path: pathlib.Path,
) -> None:
    """The de-duplication key names the file: the same code and message
    at the same line and column of two files are two diagnostics."""
    from vera.errors import Diagnostic, SourceLocation
    from vera.lsp.features import _diag_key

    def at(file: str) -> Diagnostic:
        return Diagnostic(description="d", error_code="E200",
                          location=SourceLocation(file=file, line=6,
                                                  column=3))

    assert _diag_key(at("/a/main.vera")) != _diag_key(at("/a/lib.vera"))
