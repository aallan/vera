"""A byte-order mark at the start of a source, and characters nobody can see
in one (#1790).

A source file was decoded as `utf-8`, so the byte-order mark an editor writes
(`EF BB BF`) reached the lexer as U+FEFF, and E006 printed a character the
reader cannot see.  Two parts, one class (E006 names a character the reader
cannot see):

* A mark at the very start of a file is dropped by `vera.parser.decode_source`,
  the one reader every command, the module resolver and so the language
  server's imports go through (#1666).  The matrix crosses the command with
  where the bytes are (the entry file, an imported module): each runs as the
  unmarked file runs.  A mark is not canonical form: `vera fmt --check`
  says so, `vera fmt --write` writes the file without it.  A U+FEFF anywhere
  else is a character, and a `str` a caller hands in already decoded
  (`parse`, the language server's document text) is not a file's bytes: its
  leading U+FEFF is not dropped, and is named by E006 as any other.
* E006 quotes a character with a glyph as before and names one without
  (Unicode categories Cc, Cf, and Zs other than the space, Zl, Zp) by its
  code point and name, `U+200B (zero width space)`.  The matrix crosses the
  characters the lexer refuses with the positions (line 1 column 1 after a
  mark, mid-line, end of file); the same characters inside a string literal
  or a comment stay accepted, and the Zs, Zl and Zp characters stay
  whitespace, as at base.
"""

from __future__ import annotations

import json
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline
from vera.errors import VeraError
from vera.parser import decode_source, parse, parse_file

pytestmark = pytest.mark.matrix(decides=[
    "vera/parser.py", "vera/errors.py", "vera/cli.py", "vera/resolver.py",
])

ROOT = Path(__file__).resolve().parent.parent
BOM = b"\xef\xbb\xbf"

_MAIN = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("hi");
  0
}
"""

_LIB = """\
module lib;

public fn word(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  "hi"
}
"""

_IMPORTER = """\
import lib(word);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(word(()));
  0
}
"""

#: Each command, and whether it has `--json`.
COMMANDS = {"check": True, "verify": True, "compile": True, "run": True,
            "test": True, "ast": True, "parse": False, "fmt": False}
_EXTRA = {"compile": ("--wat",)}
ENTRY_ONLY = frozenset({"ast", "parse", "fmt"})


def _vera(*args: str) -> pipeline.CliResult:
    return pipeline.cli(*args)


def _write(root: Path, where: str, marked: bool) -> Path:
    """The entry file under *root*, its entry or its imported module
    marked when *marked*."""
    mark = BOM if marked else b""
    if where == "entry":
        entry = root / "main.vera"
        entry.write_bytes(mark + _MAIN.encode("utf-8"))
    else:
        (root / "lib.vera").write_bytes(mark + _LIB.encode("utf-8"))
        entry = root / "main.vera"
        entry.write_bytes(_IMPORTER.encode("utf-8"))
    return entry


def _argv(command: str, as_json: bool, path: Path) -> list[str]:
    return [command, *_EXTRA.get(command, ()),
            *(("--json",) if as_json else ()), str(path)]


def _cells() -> list[object]:
    return [pytest.param(command, as_json, where,
                         id=f"{command}-{'json' if as_json else 'text'}"
                            f"-{where}")
            for command, has_json in COMMANDS.items()
            for as_json in ((False, True) if has_json else (False,))
            for where in ("entry", "import")
            if not (where == "import" and command in ENTRY_ONLY)
            and not (command == "fmt")]


@pytest.mark.parametrize(("command", "as_json", "where"), _cells())
def test_a_marked_source_runs_as_the_unmarked_one(
    command: str, as_json: bool, where: str, tmp_path: Path,
) -> None:
    """A leading mark in the entry file or an imported module changes
    nothing: the same exit status, stdout and stderr as the unmarked file
    (paths aside)."""
    plain_dir, marked_dir = tmp_path / "plain", tmp_path / "marked"
    plain_dir.mkdir()
    marked_dir.mkdir()
    plain = _vera(*_argv(command, as_json, _write(plain_dir, where, False)))
    marked = _vera(*_argv(command, as_json, _write(marked_dir, where, True)))
    assert plain.returncode == 0, plain
    assert marked.returncode == 0, marked

    def norm(run: pipeline.CliResult, root: Path) -> tuple[str, str]:
        return (run.stdout.replace(str(root), "<d>"),
                run.stderr.replace(str(root), "<d>"))

    assert norm(marked, marked_dir) == norm(plain, plain_dir)


def test_repro_a_marked_file_passes_check(tmp_path: Path) -> None:
    """Issue #1790's program: three bytes `EF BB BF` before a valid
    program.  `vera check` refused it with E006 at line 1, column 1 at
    f71c401c."""
    path = tmp_path / "bom.vera"
    path.write_bytes(BOM + _MAIN.encode("utf-8"))
    run = _vera("check", "--json", str(path))
    envelope = json.loads(run.stdout)
    assert run.returncode == 0 and envelope["ok"] is True, envelope
    assert envelope["diagnostics"] == [], envelope


def test_a_marked_source_on_stdin_is_accepted() -> None:
    """The route through a pipe: bytes on stdin go through the same
    reader."""
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "check", "--json", "-"], cwd=ROOT,
        input=BOM + _MAIN.encode("utf-8"), capture_output=True, timeout=300,
        check=False)
    envelope = json.loads(proc.stdout.decode("utf-8"))
    assert proc.returncode == 0 and envelope["ok"] is True, envelope


def test_the_reader_drops_one_leading_mark_only() -> None:
    assert decode_source(BOM + b"x") == "x"
    assert decode_source(BOM + BOM + b"x") == "\ufeffx"
    assert decode_source(b"x" + BOM) == "x\ufeff"
    assert decode_source(b"") == ""
    assert decode_source(BOM) == ""


def test_parse_file_reads_a_marked_file(tmp_path: Path) -> None:
    path = tmp_path / "bom.vera"
    path.write_bytes(BOM + _MAIN.encode("utf-8"))
    assert parse_file(path) is not None


def test_a_string_with_a_leading_mark_is_not_a_file(
) -> None:
    """A `str` already decoded keeps its leading U+FEFF, and E006 names
    it."""
    with pytest.raises(VeraError) as info:
        parse("\ufeff" + _MAIN, file="doc.vera")
    d = info.value.diagnostic
    assert d.error_code == "E006"
    assert "U+FEFF (zero width no-break space)" in d.description
    assert (d.location.line, d.location.column) == (1, 1)


# --- fmt -------------------------------------------------------------------


def test_fmt_check_calls_a_marked_file_not_canonical(tmp_path: Path) -> None:
    from vera.formatter import format_source
    path = tmp_path / "main.vera"
    path.write_bytes(BOM + format_source(_MAIN).encode("utf-8"))
    run = _vera("fmt", "--check", str(path))
    assert run.returncode == 1, run
    assert "Would reformat" in run.stderr, run
    path.write_bytes(format_source(_MAIN).encode("utf-8"))
    assert _vera("fmt", "--check", str(path)).returncode == 0


def test_fmt_write_writes_the_file_without_the_mark(tmp_path: Path) -> None:
    from vera.formatter import format_source
    path = tmp_path / "main.vera"
    path.write_bytes(BOM + format_source(_MAIN).encode("utf-8"))
    assert _vera("fmt", "--write", str(path)).returncode == 0
    assert path.read_bytes() == format_source(_MAIN).encode("utf-8")
    assert _vera("fmt", "--check", str(path)).returncode == 0


def test_fmt_prints_a_marked_file_without_the_mark(tmp_path: Path) -> None:
    from vera.formatter import format_source
    path = tmp_path / "main.vera"
    path.write_bytes(BOM + _MAIN.encode("utf-8"))
    run = _vera("fmt", str(path))
    assert run.returncode == 0 and run.stdout == format_source(_MAIN), run


# --- E006 names a character nobody can see ---------------------------------

#: The characters the lexer refuses that have no glyph, across the
#: categories it refuses (Cf and Cc).  A Zs, Zl or Zp character is
#: whitespace to the lexer and never reaches E006 (see the last cell).
INVISIBLE = [
    "\ufeff",  # Cf, the byte-order mark itself
    "\u200b",  # Cf, zero width space
    "\u200d",  # Cf, zero width joiner
    "\u200e",  # Cf, left-to-right mark
    "\u202e",  # Cf, right-to-left override
    "\u2060",  # Cf, word joiner
    "\u00ad",  # Cf, soft hyphen
    "\u0600",  # Cf, arabic number sign
    "\u034f",  # Mn, combining grapheme joiner (default-ignorable)
    "\ufe0f",  # Mn, variation selector-16
    "\u3164",  # Lo, hangul filler
    "\x00",    # Cc, no name
    "\x01",    # Cc, no name
    "\x7f",    # Cc, no name
    "\x80",    # Cc, no name
]

_FN = ("public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
       "  effects(pure)\n{\n  0\n}\n")
POSITIONS = ("start-after-mark", "mid-line", "end-of-file")


def _glyphless_name(char: str) -> str:
    return f"U+{ord(char):04X} ({unicodedata.name(char, '').lower() or 'control character'})"


def _place(char: str, position: str) -> tuple[str, int, int]:
    """Source holding *char* at *position*, with the line and column
    E006 must report."""
    if position == "start-after-mark":
        return char + _FN, 1, 1
    if position == "mid-line":
        return _FN.replace("  0\n", "  0" + char + " + 1\n", 1), 6, 4
    return _FN + char, 8, 1


@pytest.mark.parametrize("position", POSITIONS)
@pytest.mark.parametrize("char", INVISIBLE, ids=lambda c: f"U+{ord(c):04X}")
def test_e006_names_a_character_with_no_glyph(
    char: str, position: str, tmp_path: Path,
) -> None:
    source, line, column = _place(char, position)
    path = tmp_path / "x.vera"
    # The route a file takes: a mark first when the character leads, which
    # the reader drops, so the character itself is at line 1, column 1.
    path.write_bytes((BOM if position == "start-after-mark" else b"")
                     + source.encode("utf-8"))
    with pytest.raises(VeraError) as info:
        parse_file(path)
    d = info.value.diagnostic
    assert d.error_code == "E006", d
    assert (d.location.line, d.location.column) == (line, column), d
    assert _glyphless_name(char) in d.description, d.description
    assert f'"{char}"' not in d.description, d.description


@pytest.mark.parametrize("char", ["$", "`", "\\", "é", "€", "😀", "∀", "#"])
def test_e006_still_quotes_a_character_with_a_glyph(char: str) -> None:
    """Negative space: a visible character the lexer refuses is E006 and is
    quoted as at base."""
    source = _FN.replace("  0\n", "  0 " + char + " 1\n", 1)
    with pytest.raises(VeraError) as info:
        parse(source, file="x.vera")
    d = info.value.diagnostic
    assert d.error_code == "E006", d
    assert f'"{char}"' in d.description, d.description
    assert "U+" not in d.description, d.description


def test_a_marked_file_s_first_line_import_error_quotes_the_line_without_it(
    tmp_path: Path,
) -> None:
    """The resolver reads the importing file again for the quoted line: it
    reads what the parser saw, so a column on line 1 indexes the line."""
    path = tmp_path / "main.vera"
    path.write_bytes(
        BOM + b"import nowhere(f);\n" + _MAIN.encode("utf-8"))
    run = _vera("check", "--json", str(path))
    diags = json.loads(run.stdout)["diagnostics"]
    found = [d for d in diags if d["location"]["line"] == 1]
    assert found, diags
    assert found[0]["source_line"] == "import nowhere(f);", found[0]


@pytest.mark.parametrize("where", ["string", "comment"])
@pytest.mark.parametrize("char", INVISIBLE, ids=lambda c: f"U+{ord(c):04X}")
def test_the_same_characters_in_a_string_or_a_comment_stay_data(
    char: str, where: str, tmp_path: Path,
) -> None:
    if where == "string":
        source = _FN.replace("  0\n", '  let @String = "a' + char + 'b";\n  0\n')
    else:
        source = "-- a" + char + "b\n" + _FN
    path = tmp_path / "x.vera"
    path.write_bytes(source.encode("utf-8"))
    run = _vera("check", "--json", str(path))
    envelope: dict[str, Any] = json.loads(run.stdout)
    assert envelope["ok"] is True, envelope
    assert not [d for d in envelope["diagnostics"]
                if d.get("error_code") == "E006"], envelope


@pytest.mark.parametrize("char", ["\u00a0", "\u1680", "\u2003", "\u3000",
                                  "\u2028", "\u2029"],
                         ids=lambda c: f"U+{ord(c):04X}")
def test_whitespace_characters_stay_whitespace(char: str) -> None:
    """Unchanged from base: the Zs, Zl and Zp characters are whitespace to
    the lexer (the grammar's `%ignore /\\s+/`, Python's Unicode `\\s`) and
    are not E006.  Pinned, not endorsed: spec 1.2 lists spaces, tabs and
    newlines."""
    parse(char + _FN, file="x.vera")
    parse(_FN.replace("  0\n", "  0" + char + "\n", 1), file="x.vera")


# --- E024's locator ignores the mark the reader ignores ---------------------

_BAD = b"public \xffn main(-> @Int)\n  requires(true)\n"


def _e024(raw: bytes, tmp_path: Path) -> Any:
    path = tmp_path / "bad.vera"
    path.write_bytes(raw)
    run = _vera("check", "--json", str(path))
    [diag] = json.loads(run.stdout)["diagnostics"]
    assert diag["error_code"] == "E024", diag
    return diag


@pytest.mark.parametrize("prefix", [b"", b"x\n\n"], ids=["line1", "line3"])
def test_e024_places_a_marked_file_as_the_unmarked_one(
    prefix: bytes, tmp_path: Path,
) -> None:
    """The mark is not a column: an invalid byte after it is at the column
    and on the quoted line of the unmarked file; lines after the first are
    as they were."""
    plain = _e024(prefix + _BAD, tmp_path)
    marked = _e024(BOM + prefix + _BAD, tmp_path)
    assert marked["location"]["line"] == plain["location"]["line"]
    assert marked["location"]["column"] == plain["location"]["column"]
    assert marked["source_line"] == plain["source_line"]
    assert "\ufeff" not in marked["source_line"]
    where = (plain["location"]["line"], plain["location"]["column"])
    assert "(line %d, column %d)" % where in marked["description"]


@pytest.mark.parametrize("mark", [b"\xff\xfe", b"\xfe\xff",
                                  b"\xff\xfe\x00\x00", b"\x00\x00\xfe\xff"])
def test_e024_for_a_utf16_or_utf32_mark_is_unchanged(
    mark: bytes, tmp_path: Path,
) -> None:
    diag = _e024(mark + b"p\x00", tmp_path)
    assert "byte-order mark" in diag["description"]
    assert diag.get("source_line", "") == ""
    assert diag["location"]["line"] == 1
