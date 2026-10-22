"""A source that is not UTF-8, and a string escape that names a surrogate
(#1666, #1728).

#1666: every reading of a source file was `read_text(encoding="utf-8")`, and
the `UnicodeDecodeError` a file in another encoding raised reached no handler
of its own: `vera check`, `vera verify` and `vera test` reported it as the
internal error E699, `vera compile`, `vera run`, `vera ast`, `vera parse`,
`vera fmt` and `vera serve` exited with a traceback (an empty stdout under
`--json`), and an imported module that was not UTF-8 was E013, a module that
failed to parse.  The class is every reading of a source file by every
command: the entry file, given as a path or on stdin, and every module the
resolver loads, which is also how the language server reads one (its
documents arrive as text).  Each reading goes through `vera.parser`'s
`read_source` or `decode_source`, which raise E024 located at the file that
does not decode, at the line and column of its first byte that does not.

#1728: the escape decoder accepted a `\\u{...}` escape naming a surrogate,
U+D800 to U+DFFF, which is no Unicode scalar value and has no UTF-8 encoding,
so the literal passed `vera check` and `vera verify` and `vera compile` died
in the string pool.  The class is every code point a string literal can spell
that is not a Unicode scalar value: the surrogates, since a value above
U+10FFFF was already E009.  Every literal is decoded at one terminal,
`STRING_LIT` (expressions, patterns, interpolation fragments, contracts,
refinements), which refuses a surrogate with E009, so no later stage sees
one.  A raw surrogate cannot enter from a file: its UTF-8 form (ED A0 80)
does not decode, so it is E024 (the matrix's `raw-surrogate` kind).

The matrix crosses the command (`check`, `verify`, `compile`, `run`, `test`,
`ast`, `parse`, `fmt`, `serve`; text, and `--json` where the command has
it) with where the bytes are (the entry file, an imported module) and the
kind (a Latin-1 byte, UTF-16 with its byte-order mark, a raw surrogate's
bytes, a `\\u{D800}` escape), each run through the suite's CLI driver
(`vera.cli.main` in process, with the streams a process has: an exception
the command does not handle fails the cell, where a process would print a
traceback).  Under `--json` every command prints the refusal in the one
envelope: `vera ast --json`, which printed a refused program's diagnostic as
text on stderr and nothing on stdout (#1789), prints the envelope `vera
compile --json` prints.  Products that are not cells: `ast`, `parse` and `fmt` read the
entry file alone, so they meet no imported module; `vera parse` prints the
parse tree, which holds a literal's escapes undecoded (as it holds `\\q`),
so the escape is no refusal there.  An imported module's escape is reported
as E013, the resolver's report of a module that does not transform, naming
the module's E009.
"""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/cli.py", "vera/errors.py", "vera/parser.py", "vera/resolver.py",
    "vera/transform.py",
])

ROOT = Path(__file__).resolve().parent.parent

# =====================================================================
# The programs
# =====================================================================

#: The entry program: `LIT` is the string literal each kind spells.
_MAIN = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(LIT);
  0
}
"""

#: A module whose one function returns the literal ...
_LIB = """\
module lib;

public fn word(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  LIT
}
"""

#: ... and the entry program that imports it, which is UTF-8.
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


def _position(prefix: str) -> tuple[int, int]:
    """The line and column (1-based) of the character after *prefix*."""
    return prefix.count("\n") + 1, len(prefix) - (prefix.rfind("\n") + 1) + 1


def _spell(kind: str, template: str) -> tuple[bytes, tuple[int, int] | None]:
    """*template* with `LIT` spelled as *kind*: its bytes, and the position
    of the first byte that does not decode (none for a kind that decodes)."""
    head, tail = template.split("LIT")
    if kind == "latin1":
        text = template.replace("LIT", '"café"')
        return text.encode("latin-1"), _position(head + '"caf')
    if kind == "utf16":
        return template.replace("LIT", '"cafe"').encode("utf-16"), (1, 1)
    if kind == "raw-surrogate":
        raw = head.encode("utf-8") + b'"a\xed\xa0\x80b"' + tail.encode("utf-8")
        return raw, _position(head + '"a')
    if kind == "escape":
        return template.replace("LIT", '"\\u{D800}"').encode("utf-8"), None
    assert kind == "utf8"
    return template.replace("LIT", '"café"').encode("utf-8"), None


@dataclass(frozen=True)
class Case:
    """The files one cell writes and what the head reports for them."""

    #: The file the command is given.
    entry: Path
    #: The file that holds the kind's bytes.
    holder: Path
    #: The code the head reports.
    code: str
    #: Where E024 is located in *holder*; `None` for an escape.
    position: tuple[int, int] | None


def _write(kind: str, where: str, root: Path) -> Case:
    if where == "entry":
        raw, position = _spell(kind, _MAIN)
        entry = root / "main.vera"
        entry.write_bytes(raw)
        holder = entry
    else:
        raw, position = _spell(kind, _LIB)
        holder = root / "lib.vera"
        holder.write_bytes(raw)
        entry = root / "main.vera"
        entry.write_bytes(_IMPORTER.encode("utf-8"))
    code = "E024" if position is not None else (
        "E009" if where == "entry" else "E013")
    return Case(entry, holder, code, position)


# =====================================================================
# The CLI
# =====================================================================


def _vera(*args: str, stdin: str = "") -> pipeline.CliResult:
    """`vera *args*`, through the suite's driver: `vera.cli.main` in
    process, with the streams a process has.  An exception the command does
    not handle propagates, where a process would print its traceback."""
    return pipeline.cli(*args, stdin=stdin)


def _envelope(run: pipeline.CliResult) -> dict[str, Any]:
    out = json.loads(run.stdout)
    assert isinstance(out, dict), out
    return out


def _codes(envelope: dict[str, Any]) -> list[str]:
    return [d.get("error_code", "") for d in envelope["diagnostics"]]


#: Each command, and whether it has `--json`.
COMMANDS = {"check": True, "verify": True, "compile": True, "run": True,
            "test": True, "ast": True, "parse": False, "fmt": False,
            "serve": False}

#: The arguments a command needs beside the file.
_EXTRA = {"compile": ("--wat",), "serve": ("--port", "0")}

#: The commands that read the entry file alone.
ENTRY_ONLY = frozenset({"ast", "parse", "fmt"})

KINDS = ("latin1", "utf16", "raw-surrogate", "escape")


def _argv(command: str, as_json: bool, path: Path) -> list[str]:
    return [command, *_EXTRA.get(command, ()),
            *(("--json",) if as_json else ()), str(path)]


def _modes(command: str) -> tuple[bool, ...]:
    return (False, True) if COMMANDS[command] else (False,)


def _cells() -> list[object]:
    return [pytest.param(command, as_json, where, kind,
                         id=f"{command}-{'json' if as_json else 'text'}"
                            f"-{where}-{kind}")
            for command in COMMANDS for as_json in _modes(command)
            for where in ("entry", "import") for kind in KINDS
            if not (where == "import" and command in ENTRY_ONLY)
            and not (command == "parse" and kind == "escape")]


def _assert_reported(run: pipeline.CliResult, case: Case,
                     as_json: bool) -> None:
    """The command refused the source with *case*'s code, located at the
    file that holds the bytes for E024, with no traceback."""
    assert run.returncode == 1, run
    assert "Traceback" not in run.stderr, run.stderr[-3000:]
    if as_json:
        envelope = _envelope(run)
        assert envelope["ok"] is False, envelope
        codes = _codes(envelope)
        assert case.code in codes and "E699" not in codes, envelope
        found = next(d for d in envelope["diagnostics"]
                     if d.get("error_code") == case.code)
        if case.position is not None:
            # A module's E024 is its own: the import does not become E013.
            assert "E013" not in codes, envelope
            location = found["location"]
            assert Path(location["file"]).resolve() == case.holder.resolve()
            assert (location["line"], location["column"]) == case.position
        elif case.code == "E013":
            assert "E009" in found["description"], found
            assert "surrogate" in found["description"], found
        else:
            assert "surrogate" in found["description"], found
        return
    assert f"[{case.code}]" in run.stderr, run.stderr[-3000:]
    if case.position is not None:
        line, column = case.position
        assert f"{case.holder.name}, line {line}, column {column}:" \
            in run.stderr, run.stderr[-3000:]
    else:
        assert "surrogate" in run.stderr, run.stderr[-3000:]


@pytest.mark.parametrize(("command", "as_json", "where", "kind"), _cells())
def test_every_command_refuses_the_source_with_a_code(
    command: str, as_json: bool, where: str, kind: str, tmp_path: Path,
) -> None:
    """Every command reports a source that is not UTF-8 as E024 at the file
    and the byte, and a surrogate escape as E009 (E013 for a module's),
    with exit status 1, no traceback, and under `--json` in its envelope
    (`vera ast --json` among them, which printed a refusal as text).  At
    506d2161 each was E699, a traceback, E013, text, or exit 0."""
    case = _write(kind, where, tmp_path)
    run = _vera(*_argv(command, as_json, case.entry))
    _assert_reported(run, case, as_json)


def _accepted(command: str, as_json: bool,
              run: pipeline.CliResult) -> None:
    assert run.returncode == 0, run
    assert "Traceback" not in run.stderr, run.stderr[-3000:]
    if as_json and command in ("check", "verify", "compile", "test"):
        envelope = _envelope(run)
        assert envelope.get("ok", True) is True, envelope
        assert not _codes(envelope), envelope


def _accepted_cells() -> list[object]:
    return [pytest.param(command, as_json, where,
                         id=f"{command}-{'json' if as_json else 'text'}"
                            f"-{where}")
            for command in COMMANDS if command != "serve"
            for as_json in _modes(command)
            for where in ("entry", "import")
            if not (where == "import" and command in ENTRY_ONLY)]


@pytest.mark.parametrize(("command", "as_json", "where"), _accepted_cells())
def test_a_utf8_source_is_accepted_as_at_the_base(
    command: str, as_json: bool, where: str, tmp_path: Path,
) -> None:
    """The nearest accepted neighbour: the same programs spelled in UTF-8
    (`"café"`) pass every command, with the same verdict as at 506d2161:
    exit 0, no diagnostic, `vera run` printing `café` and a newline, and
    every obligation `vera verify` reports verified."""
    case = _write("utf8", where, tmp_path)
    run = _vera(*_argv(command, as_json, case.entry))
    _accepted(command, as_json, run)
    if command == "run" and not as_json:
        assert run.stdout == "café\n", run
    if command == "verify" and as_json:
        statuses = {o["status"] for o in _envelope(run)["obligations"]}
        assert statuses <= {"verified"}, statuses


#: A program whose body is a `String` where an `Int` is declared: one
#: diagnostic, at line 6, column 3.
_MISTYPED = (
    "public fn main(@Unit -> @Int)", "  requires(true)", "  ensures(true)",
    "  effects(pure)", "{", '  "café"', "}", "",
)


@pytest.mark.parametrize("newline", ["\n", "\r\n", "\r"],
                         ids=["lf", "crlf", "cr"])
def test_a_file_s_line_ends_place_a_diagnostic_as_at_the_base(
    newline: str, tmp_path: Path,
) -> None:
    """A file is read with universal newlines, as `Path.read_text` read it
    at 506d2161: the same diagnostic sits at the same line and column
    whatever the file's line ends, a lone `\\r` among them."""
    path = tmp_path / "mistyped.vera"
    path.write_bytes(newline.join(_MISTYPED).encode("utf-8"))
    envelope = _envelope(_vera("check", "--json", str(path)))
    locations = [(d["location"]["line"], d["location"]["column"])
                 for d in envelope["diagnostics"]]
    assert locations == [(6, 3)], envelope


# =====================================================================
# The reported programs, and every other reading
# =====================================================================

#: Issue #1666's program, as its `printf` writes it: one Latin-1 byte.
_ISSUE_1666 = (b'public fn main(@Unit -> @Unit)\n  requires(true)\n'
               b'  ensures(true)\n  effects(<IO>)\n{\n  IO.print("caf\xe9")\n}\n')


def test_repro_1666_a_latin1_file_is_e024_at_compile_and_check(
    tmp_path: Path,
) -> None:
    """Issue #1666's program: `vera compile --json` printed nothing (a
    traceback on stderr) and `vera check --json` an E699 envelope at
    506d2161; each prints one E024 at line 6, column 16, the `é`."""
    path = tmp_path / "latin1.vera"
    path.write_bytes(_ISSUE_1666)
    for command in ("compile", "check"):
        run = _vera(command, "--json", str(path))
        envelope = _envelope(run)
        assert run.returncode == 1 and _codes(envelope) == ["E024"], envelope
        location = envelope["diagnostics"][0]["location"]
        assert (location["line"], location["column"]) == (6, 16), location
        assert "0xE9" in envelope["diagnostics"][0]["description"]


#: Issue #1728's program.
_ISSUE_1728 = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @String = "\\u{D800}";
  string_length(@String.0)
}
"""


def test_repro_1728_a_lone_surrogate_escape_is_e009_at_check_and_compile(
    tmp_path: Path,
) -> None:
    """Issue #1728's program: `vera check` passed it and `vera compile` died
    with a `UnicodeEncodeError` at 506d2161; each refuses it with E009 at
    the literal, line 6."""
    path = tmp_path / "surrogate.vera"
    path.write_bytes(_ISSUE_1728.encode("utf-8"))
    for command in ("check", "compile"):
        run = _vera(command, "--json", str(path))
        envelope = _envelope(run)
        assert run.returncode == 1 and _codes(envelope) == ["E009"], envelope
        found = envelope["diagnostics"][0]
        assert found["location"]["line"] == 6, found
        assert "surrogate" in found["description"], found


def test_repro_1789_ast_json_prints_a_refusal_in_the_envelope(
    tmp_path: Path,
) -> None:
    """Issue #1789's program, an invalid escape: `vera ast --json` exited 1
    with an empty stdout and the E009 as text on stderr at 506d2161; it
    prints the envelope `vera compile --json` prints for it."""
    path = tmp_path / "escape.vera"
    path.write_bytes(_ISSUE_1728.replace("\\u{D800}", "a\\qb").encode("utf-8"))
    run = _vera("ast", "--json", str(path))
    envelope = _envelope(run)
    assert run.returncode == 1 and envelope["ok"] is False, run
    assert _codes(envelope) == ["E009"], envelope
    assert envelope == _envelope(_vera("compile", "--json", str(path)))


def test_repro_a_source_on_stdin_that_is_not_utf8_is_e024() -> None:
    """`vera check -` reads its source from stdin: Latin-1 bytes there were
    E699 at 506d2161, and are E024 located at `-`, the path given.  The
    bytes reach stdin through a process's pipe: the driver's stdin is
    text, which has no Latin-1 byte to hold."""
    raw, position = _spell("latin1", _MAIN)
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "check", "--json", "-"], cwd=ROOT,
        input=raw, capture_output=True, timeout=300, check=False)
    envelope = json.loads(proc.stdout.decode("utf-8"))
    assert proc.returncode == 1 and _codes(envelope) == ["E024"], envelope
    location = envelope["diagnostics"][0]["location"]
    assert location["file"] == "-", location
    assert (location["line"], location["column"]) == position, location


def test_a_utf8_source_on_stdin_is_accepted_as_at_the_base() -> None:
    """The neighbour on stdin: UTF-8 checks clean and runs, printing
    `café`."""
    text = _MAIN.replace("LIT", '"café"')
    run = _vera("check", "-", stdin=text)
    assert run.returncode == 0, run
    run = _vera("run", "-", stdin=text)
    assert run.returncode == 0 and run.stdout == "café\n", run


@pytest.mark.parametrize("raw", [b"a\r\nb\rc\nd", "café\r\n".encode("utf-8")],
                         ids=["crlf-cr-lf", "utf8-crlf"])
def test_stdin_s_bytes_decode_to_the_text_the_stream_read(raw: bytes) -> None:
    """The differential for stdin: the command decodes stdin's bytes itself
    now, and for UTF-8 bytes it returns the text `sys.stdin.read()` returned
    on this platform (CPython's stdin translates newlines on Windows alone),
    each read in its own process from the same bytes."""
    prologue = "import sys; sys.stdin.reconfigure(encoding='utf-8'); "
    reads = {
        "stream": prologue + "print(ascii(sys.stdin.read()))",
        "decoder": prologue + ("from vera.cli import _read_stdin; "
                               "print(ascii(_read_stdin('-')))"),
    }
    out = {name: subprocess.run(
        [sys.executable, "-c", code], cwd=ROOT, input=raw,
        capture_output=True, timeout=120, check=True).stdout
        for name, code in reads.items()}
    assert out["stream"] == out["decoder"], out


def test_repro_the_language_server_reports_a_module_that_is_not_utf8(
    tmp_path: Path,
) -> None:
    """The language server reads a document's imports through the resolver:
    a Latin-1 module was E013 at 506d2161, and is the module's E024,
    published with its file and message.  Where it is published is not
    asserted: the server places a module's diagnostic at the module's line
    in the open document (#1788)."""
    from vera.lsp.features import analyze, to_lsp_diagnostics
    from vera.obligations.session import VerificationSession

    case = _write("latin1", "import", tmp_path)
    text = case.entry.read_text(encoding="utf-8")
    analysis = analyze(VerificationSession(), case.entry.as_uri(), text)
    codes = [d.error_code for d in analysis.diagnostics]
    assert "E024" in codes and "E013" not in codes, codes
    found = next(d for d in analysis.diagnostics if d.error_code == "E024")
    assert found.location.file is not None
    assert Path(found.location.file).resolve() == case.holder.resolve()
    published = [d for d in to_lsp_diagnostics(analysis) if d.code == "E024"]
    assert published and published[0].message.startswith(found.description)


def test_repro_reconcile_file_reports_a_source_that_is_not_utf8(
    tmp_path: Path,
) -> None:
    """`reconcile_file` (`scripts/check_reconciliation.py`'s entry) raised
    `UnicodeDecodeError` at 506d2161; it records the E024 as the program's
    refusal, a stop before the join."""
    from vera.reconcile import reconcile_file

    case = _write("latin1", "entry", tmp_path)
    run = reconcile_file(case.entry)
    assert run.program is None and len(run.check_errors) == 1, run
    assert "UTF-8" in run.check_errors[0], run.check_errors


@pytest.mark.parametrize("api", ["parse_file", "typecheck_file",
                                 "verify_file"])
def test_repro_the_parser_s_file_functions_raise_e024(
    api: str, tmp_path: Path,
) -> None:
    """`vera.parser`'s file functions raised `UnicodeDecodeError` at
    506d2161; each raises the E024 as a `VeraError`."""
    import vera.parser
    from vera.errors import VeraError

    case = _write("latin1", "entry", tmp_path)
    with pytest.raises(VeraError) as caught:
        getattr(vera.parser, api)(case.entry)
    assert caught.value.diagnostic.error_code == "E024"
    location = caught.value.diagnostic.location
    assert (location.line, location.column) == case.position


# =====================================================================
# The diagnostic's text, and its fix applied
# =====================================================================


def test_e024_names_the_byte_the_offset_and_a_utf16_byte_order_mark(
    tmp_path: Path,
) -> None:
    """E024's description names the byte and its offset, and for a file
    that begins with a UTF-16 byte-order mark says the file is UTF-16."""
    case = _write("utf16", "entry", tmp_path)
    envelope = _envelope(_vera("check", "--json", str(case.entry)))
    found = envelope["diagnostics"][0]
    assert "0xFF" in found["description"] and "offset 0" in found["description"]
    assert "UTF-16" in found["description"], found
    assert found["spec_ref"] == 'Chapter 1, Section 1.1 "Source Encoding"'


@pytest.mark.parametrize(("kind", "command", "codec"), [
    ("latin1", "iconv -f ISO-8859-1 -t UTF-8", "latin-1"),
    ("utf16", "iconv -f UTF-16 -t UTF-8", "utf-16"),
])
def test_e024_s_fix_applied_to_the_file_passes_check(
    kind: str, command: str, codec: str, tmp_path: Path,
) -> None:
    """E024's fix converts the file to UTF-8 with the `iconv` command it
    names; the file it writes (the same conversion, in Python) checks
    clean."""
    case = _write(kind, "entry", tmp_path)
    envelope = _envelope(_vera("check", "--json", str(case.entry)))
    fix = envelope["diagnostics"][0]["fix"]
    assert command in fix, fix
    case.entry.write_bytes(
        case.entry.read_bytes().decode(codec).encode("utf-8"))
    run = _vera("check", "--json", str(case.entry))
    assert run.returncode == 0 and not _codes(_envelope(run)), run


def test_the_surrogate_fix_applied_to_a_pair_passes_check() -> None:
    """E009's fix for a surrogate writes a character outside the Basic
    Multilingual Plane as one escape of its code point: the UTF-16 pair
    `\\u{D83D}\\u{DE00}` replaced by `\\u{1F600}` checks clean."""
    pair = _ISSUE_1728.replace("\\u{D800}", "\\u{D83D}\\u{DE00}")
    checked = pipeline.check(pair)
    found = [d for d in checked.diagnostics if d.error_code == "E009"]
    assert found and "\\u{1F600}" in found[0].fix, checked.diagnostics
    fixed = pair.replace("\\u{D83D}\\u{DE00}", "\\u{1F600}")
    assert pipeline.check(fixed).ok, pipeline.check(fixed).diagnostics


# =====================================================================
# Every literal, every surrogate
# =====================================================================

_HEAD = "  requires(true) ensures(true) effects(pure)\n"

#: Each place a string literal can be written, with `ESC` for the escape.
SITES = {
    "expression": f"""\
public fn f(@Unit -> @Nat)
{_HEAD}{{ string_length("aESCb") }}
""",
    "pattern": f"""\
public fn f(@String -> @Int)
{_HEAD}{{ match @String.0 {{ "ESC" -> 1, _ -> 0 }} }}
""",
    "interpolation": f"""\
public fn f(@String -> @String)
{_HEAD}{{ "aESC\\(@String.0)b" }}
""",
    "requires": """\
public fn f(@Nat -> @Nat)
  requires(string_length("ESC") > 0) ensures(true) effects(pure)
{ @Nat.0 }
""",
    "ensures": """\
public fn f(@Nat -> @Nat)
  requires(true) ensures(string_length("ESC") > 0) effects(pure)
{ @Nat.0 }
""",
    "refinement": f"""\
type Tagged = {{ @String | string_length(@String.0) > string_length("ESC") }};

public fn f(@Tagged -> @Nat)
{_HEAD}{{ string_length(@Tagged.0) }}
""",
}


@pytest.mark.parametrize("site", sorted(SITES))
def test_a_surrogate_escape_is_refused_wherever_a_literal_is_written(
    site: str,
) -> None:
    """Every literal is decoded at one terminal: the escape is E009 at each
    place a literal can be written, and the scalar value beside the
    surrogates, `\\u{E000}`, is accepted there."""
    refused = pipeline.check(SITES[site].replace("ESC", "\\u{D800}"))
    found = [d for d in refused.diagnostics if d.error_code == "E009"]
    assert found and "surrogate" in found[0].description, refused.diagnostics
    accepted = pipeline.check(SITES[site].replace("ESC", "\\u{E000}"))
    assert accepted.ok, accepted.diagnostics


@pytest.mark.parametrize(("digits", "words"), [
    ("D800", "surrogate"), ("DBFF", "surrogate"), ("DC00", "surrogate"),
    ("DFFF", "surrogate"), ("d800", "surrogate"), ("00D800", "surrogate"),
    ("110000", "out of range"),
])
def test_an_escape_that_is_no_scalar_value_is_refused(
    digits: str, words: str,
) -> None:
    """The surrogates, at both ends of each half and in any spelling, and a
    code point above U+10FFFF (refused before this change too), are E009."""
    checked = pipeline.check(_ISSUE_1728.replace("D800", digits))
    found = [d for d in checked.diagnostics if d.error_code == "E009"]
    assert found and words in found[0].description, checked.diagnostics


def test_a_surrogate_pair_is_refused_at_its_first_escape() -> None:
    """A UTF-16 pair spelled as two escapes is two surrogates, not one
    character: the first is refused."""
    checked = pipeline.check(
        _ISSUE_1728.replace("\\u{D800}", "\\u{D83D}\\u{DE00}"))
    found = [d for d in checked.diagnostics if d.error_code == "E009"]
    assert found and "\\u{D83D}" in found[0].description, checked.diagnostics


@pytest.mark.parametrize("digits", ["0", "D7FF", "E000", "FFFF", "1F600",
                                    "10FFFF"])
def test_an_escape_that_names_a_scalar_value_compiles(digits: str) -> None:
    """The scalar values beside the surrogates and at the ends of the range
    check, and compile: the string pool encodes each."""
    source = _ISSUE_1728.replace("D800", digits)
    assert pipeline.check(source).ok
    pipeline.compile(source)


# =====================================================================
# One cell per mechanism, unparametrised: the diff lane's mutmut copy runs
# the matrix above sampled, so a mechanism only a matrix cell asserts is one
# the lane counts as unasserted (CLAUDE.md § Fix the class, not the
# instance: the mutant killers are unparametrised).
# =====================================================================

#: The note E024's fix adds when it guesses Latin-1.
_LATIN1_NOTE = (
    " That command reads the source as Latin-1 (ISO-8859-1); a source in "
    "another encoding names its own after `-f`. In a string literal, a "
    "character can also be written as an escape of its code point, such as "
    "`\\u{E9}` for é."
)


def _e024(raw: bytes, file: str | None = "main.vera") -> Any:
    """The diagnostic *raw* raises where a command decodes it as *file*."""
    from vera.errors import SourceEncodingError
    from vera.parser import decode_source

    with pytest.raises(SourceEncodingError) as caught:
        decode_source(raw, file)
    return caught.value.diagnostic


def test_e024_counts_lines_and_columns_as_the_reader_does() -> None:
    """E024's line counts `\\r\\n`, a lone `\\r` and `\\n` as one line end
    each, as the reader does, whichever comes first, and its column counts
    the characters along the line, not its bytes."""
    cases = [
        (b"one\r\ntwo\r  caf\xe9\n", (3, 6)),
        (b"one\rtwo\r\n  caf\xe9\n", (3, 6)),
        (b"one\ntwo\n  caf\xe9\n", (3, 6)),
        ("été".encode("utf-8") + b"\xff", (1, 4)),
    ]
    for raw, position in cases:
        location = _e024(raw).location
        assert (location.line, location.column) == position, (raw, location)


def test_e024_quotes_the_line_that_holds_the_byte() -> None:
    """E024's `source_line` is the line that holds the byte, from the line
    end before it to the line end after it, of whichever kind each is, the
    byte shown as U+FFFD: between lines of each kind and of mixed kinds,
    after a line end at offset 0, and on the first and the last line, the
    last with no line end after it."""
    cases = [
        (b"one\ntwo\n  caf\xe9 x\nfour\nfive\n", "  caf� x"),
        (b"one\rtwo\r  caf\xe9 x\rfour\rfive\r", "  caf� x"),
        (b"one\r\ntwo\r\n  caf\xe9 x\r\nfour\r\n", "  caf� x"),
        (b"one\r\ntwo\r  caf\xe9 x\nfour\n", "  caf� x"),
        (b"\n  caf\xe9\n", "  caf�"),
        (b"\r  caf\xe9\r", "  caf�"),
        (b"  caf\xe9 x\nmore\n", "  caf� x"),
        (b"one\n  caf\xe9", "  caf�"),
    ]
    for raw, quoted in cases:
        assert _e024(raw).source_line == quoted, raw


def test_e024_s_text_names_the_byte_its_offset_line_and_column() -> None:
    """E024 as a command reports it, every field: the byte and its offset,
    the line and column it sits at, the line it quotes, why, the fix, the
    spec section and the code."""
    found = _e024(b"one\n  caf\xe9\n", "dir/main.vera")
    assert found.to_dict() == {
        "severity": "error",
        "description": (
            "Source file is not valid UTF-8: the byte 0xE9 at offset 9 "
            "(line 2, column 6) does not begin a valid UTF-8 sequence."),
        "location": {"line": 2, "column": 6, "file": "dir/main.vera"},
        "source_line": "  caf�",
        "rationale": (
            "Vera source is UTF-8: every command reads the program, and each "
            "module it imports, as UTF-8. A byte sequence that is not UTF-8 "
            "names no character, so what the file says is undefined; a file "
            "saved in another encoding, such as Latin-1 or UTF-16, converts "
            "to UTF-8 with its text unchanged."),
        "fix": (
            "Save the file as UTF-8: in its directory, `iconv -f ISO-8859-1 "
            "-t UTF-8 main.vera > main.utf8.vera` writes a UTF-8 copy, which "
            "then replaces main.vera." + _LATIN1_NOTE),
        "spec_ref": 'Chapter 1, Section 1.1 "Source Encoding"',
        "error_code": "E024",
    }


def test_e024_names_each_byte_order_mark_and_quotes_no_line() -> None:
    """A file that begins with a UTF-16 or a UTF-32 byte-order mark, in
    either byte order, is named as that encoding, in the description and in
    the fix's `iconv` command, and quotes no line: what follows the mark is
    no line of UTF-8.  A little-endian UTF-32 mark begins with the UTF-16
    one, so the longer mark is the one named."""
    text = "public fn f(@Unit -> @Unit)\n"
    cases = [
        (b"\xff\xfe" + text.encode("utf-16-le"), "UTF-16", 0xFF, 0),
        (b"\xfe\xff" + text.encode("utf-16-be"), "UTF-16", 0xFE, 0),
        (b"\xff\xfe\x00\x00" + text.encode("utf-32-le"), "UTF-32", 0xFF, 0),
        (b"\x00\x00\xfe\xff" + text.encode("utf-32-be"), "UTF-32", 0xFE, 2),
    ]
    for raw, mark, byte, offset in cases:
        found = _e024(raw)
        assert found.description == (
            f"Source file is not valid UTF-8: the byte 0x{byte:02X} at offset "
            f"{offset} (line 1, column {offset + 1}) does not begin a valid "
            f"UTF-8 sequence. The file begins with a {mark} byte-order mark: "
            f"it is {mark}, not UTF-8."), raw[:4]
        assert found.source_line == "", raw[:4]
        assert found.fix == (
            f"Save the file as UTF-8: in its directory, `iconv -f {mark} -t "
            f"UTF-8 main.vera > main.utf8.vera` writes a UTF-8 copy, which "
            f"then replaces main.vera."), raw[:4]


def test_e024_s_fix_converts_the_file_it_names_or_the_pipe() -> None:
    """E024's fix converts a file into a UTF-8 copy beside it, its names
    quoted for the shell, and converts stdin (`-`, `/dev/stdin`, or no file
    at all) in the pipe that feeds `vera`."""
    raw = b'  IO.print("caf\xe9")\n'
    assert _e024(raw, "dir/my prog.vera").fix == (
        "Save the file as UTF-8: in its directory, `iconv -f ISO-8859-1 -t "
        "UTF-8 'my prog.vera' > 'my prog.utf8.vera'` writes a UTF-8 copy, "
        "which then replaces my prog.vera." + _LATIN1_NOTE)
    for label in ("-", "/dev/stdin", None):
        assert _e024(raw, label).fix == (
            "Convert the source to UTF-8 before `vera` reads it: pipe it "
            "through `iconv -f ISO-8859-1 -t UTF-8`." + _LATIN1_NOTE), label


def _canonical() -> str:
    """A canonical program with a comment: a comment runs to its line's end,
    so a line end the reader did not translate would run into it."""
    from vera.formatter import format_source

    return format_source("-- a comment\n" + _MAIN.replace("LIT", '"cafe"'))


def test_fmt_check_calls_a_file_with_carriage_returns_not_canonical(
    tmp_path: Path,
) -> None:
    """`vera fmt --check` passes a canonical file and refuses the same text
    with `\\r\\n` line ends: canonical Vera is LF-only (spec 1.8 rule 10)."""
    canonical = _canonical()
    lf, crlf = tmp_path / "lf.vera", tmp_path / "crlf.vera"
    lf.write_bytes(canonical.encode("utf-8"))
    crlf.write_bytes(canonical.replace("\n", "\r\n").encode("utf-8"))
    assert _vera("fmt", "--check", str(lf)).returncode == 0
    run = _vera("fmt", "--check", str(crlf))
    assert run.returncode == 1 and "Would reformat" in run.stderr, run


def test_fmt_formats_crlf_and_lone_cr_line_ends_as_lf(tmp_path: Path) -> None:
    """`vera fmt` reads `\\r\\n` and a lone `\\r` as line ends and prints
    the file's canonical, LF-only form."""
    canonical = _canonical()
    path = tmp_path / "main.vera"
    for newline in ("\r\n", "\r"):
        path.write_bytes(canonical.replace("\n", newline).encode("utf-8"))
        run = _vera("fmt", str(path))
        assert (run.returncode, run.stdout) == (0, canonical), newline


def test_fmt_reports_e024_and_a_parse_error_at_the_file(tmp_path: Path) -> None:
    """`vera fmt` names the file it was given in the diagnostics it reads
    the file into: E024 for bytes that are not UTF-8, and the parse error
    of a file that does not parse."""
    raw, position = _spell("latin1", _MAIN)
    latin1 = tmp_path / "latin1.vera"
    latin1.write_bytes(raw)
    run = _vera("fmt", str(latin1))
    assert run.returncode == 1, run
    assert (f"[E024] Error at {latin1}, line {position[0]}, "
            f"column {position[1]}:") in run.stderr, run.stderr
    broken = tmp_path / "broken.vera"
    broken.write_bytes(b"public fn f(\n")
    run = _vera("fmt", str(broken))
    assert run.returncode == 1 and f"Error at {broken}, line" in run.stderr, run


def test_ast_on_a_missing_file_exits_1(tmp_path: Path) -> None:
    """`vera ast` on a path that names no file exits 1 with the message the
    other commands print."""
    missing = tmp_path / "missing.vera"
    run = _vera("ast", str(missing))
    assert (run.returncode, run.stderr) == (
        1, f"Error: file not found: {missing}\n"), run


def test_reconcile_file_records_e024_and_runs_a_utf8_program_to_the_join(
    tmp_path: Path,
) -> None:
    """`reconcile_file` records a source that is not UTF-8 as its refusal,
    E024's description, and runs the same program in UTF-8 to the join."""
    from vera.reconcile import reconcile_file

    for name in ("refused", "accepted"):
        (tmp_path / name).mkdir()
    refused = _write("latin1", "entry", tmp_path / "refused")
    run = reconcile_file(refused.entry)
    assert run.path == refused.entry and run.program is None, run
    assert run.check_errors == [_e024(refused.entry.read_bytes()).description]
    accepted = _write("utf8", "entry", tmp_path / "accepted")
    run = reconcile_file(accepted.entry)
    assert run.path == accepted.entry and run.check_errors == [], run
    assert run.program is not None and run.compile_result is not None, run


def test_e009_s_surrogate_diagnostic_is_exact() -> None:
    """The E009 a surrogate escape raises, every field: the escape as
    written, at the literal, with the surrogate rationale and fix."""
    from vera.transform import (
        _E009_ESCAPE_SPEC,
        _E009_SURROGATE_FIX,
        _E009_SURROGATE_RATIONALE,
    )

    (found,) = [d for d in pipeline.check(_ISSUE_1728).diagnostics
                if d.error_code == "E009"]
    assert found.description == (
        "Unicode escape names a surrogate, not a Unicode scalar value: "
        "\\u{D800}")
    assert (found.location.line, found.location.column) == (6, 17)
    assert (found.rationale, found.fix, found.spec_ref) == (
        _E009_SURROGATE_RATIONALE, _E009_SURROGATE_FIX, _E009_ESCAPE_SPEC)


def test_the_parser_s_file_functions_report_a_parse_error_at_the_path(
    tmp_path: Path,
) -> None:
    """`vera.parser`'s file functions parse the file under its path: a file
    that does not parse raises a parse error located at it."""
    import vera.parser
    from vera.errors import ParseError

    path = tmp_path / "broken.vera"
    path.write_bytes(b"public fn f(\n")
    for api in ("parse_file", "typecheck_file", "verify_file"):
        with pytest.raises(ParseError) as caught:
            getattr(vera.parser, api)(path)
        assert caught.value.diagnostic.location.file == str(path), api
