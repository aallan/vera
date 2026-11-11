"""The quoted String of an uncaught exception is cut at a character (#1526).

The entry-point boundary quotes at most 64 bytes of a thrown `String` and
appends an ellipsis.  The cut is a byte count; the emitted code backs it up
while the byte at the cut is a UTF-8 continuation byte, at most three steps
(a character is at most four bytes), so the quoted value is whole characters.

The class: a multi-byte character (1, 2, 3 or 4 bytes wide) whose first byte
sits at every offset from four before the cut to one after, on each host
(wasmtime, the WASI 0.2 host, the browser runtime).  Each cell asserts the
quoted value holds no U+FFFD, is the longest whole-character prefix of the
thrown string within 64 bytes, and ends in the ellipsis exactly when the
string was longer than the cut.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tests import pipeline
from vera.codegen.api import CompileResult, execute
from vera.runtime.traps import WasmTrapError

pytestmark = pytest.mark.matrix(
    decides=[
        "vera/codegen/functions.py",
        "vera/runtime/wasi_host.py",
        "vera/browser/runtime.mjs",
    ],
)

CUT = 64
MARKER = ", and the value thrown was "
ELLIPSIS = "…"

#: Width in bytes -> the character.
CHARACTERS = {1: "a", 2: "é", 3: "€", 4: "😀"}
#: The offset of the character's first byte relative to the cut.
OFFSETS = range(-4, 2)
TAIL = "bcd"

_NODE = None
try:
    from tests.test_browser import _HAS_EXNREF, _run_node
    if _HAS_EXNREF:
        _NODE = _run_node
except ImportError:  # pragma: no cover — the browser harness module moved
    _NODE = None

browser = pytest.mark.skipif(
    _NODE is None,
    reason="Node.js not available or lacks --experimental-wasm-exnref support",
)


def thrown(width: int, offset: int) -> str:
    return "a" * (CUT + offset) + CHARACTERS[width] + TAIL


def program(value: str) -> str:
    return (
        "public fn main(-> @Int)\n"
        "  requires(true) ensures(true) effects(<Exn<String>>)\n"
        '{\n  throw("' + value + '")\n}\n')


def expected_quote(value: str) -> str:
    """The quoted value the message must hold: *value* whole when it fits,
    else its longest whole-character prefix within the cut, and the
    ellipsis."""
    raw = value.encode("utf-8")
    if len(raw) <= CUT:
        return value
    cut = CUT
    while raw[cut] & 0xC0 == 0x80:
        cut -= 1
    return raw[:cut].decode("utf-8") + ELLIPSIS


def quoted(message: str) -> str:
    assert message.count(MARKER) == 1, message
    tail = message.split(MARKER)[1]
    assert tail.startswith('"') and tail.endswith('"'), tail
    return tail[1:-1]


def assert_cut(value: str, message: str) -> None:
    q = quoted(message)
    assert "�" not in q, q
    longer = len(value.encode("utf-8")) > CUT
    assert q.endswith(ELLIPSIS) == longer, q
    body = q[:-1] if longer else q
    assert value.startswith(body), (value, q)
    assert q == expected_quote(value), (value, q)


def _compile(value: str) -> CompileResult:
    compiled = pipeline.compile(program(value), file="cut.vera")
    _ = compiled.parsed.program
    result = compiled.result
    assert result.ok, [d.description for d in result.diagnostics]
    return result


CELLS = [(w, o) for w in CHARACTERS for o in OFFSETS]


def _id(cell: tuple[int, int]) -> str:
    return f"{cell[0]}byte@{cell[1]:+d}"


@pytest.mark.parametrize("cell", CELLS, ids=_id)
def test_wasmtime_cuts_at_a_character(cell: tuple[int, int]) -> None:
    value = thrown(*cell)
    with pytest.raises(WasmTrapError) as info:
        execute(_compile(value), fn_name="main")
    assert info.value.kind == "uncaught_exception"
    assert_cut(value, str(info.value))


@pytest.mark.parametrize("cell", CELLS, ids=_id)
def test_the_wasi_host_cuts_at_a_character(cell: tuple[int, int]) -> None:
    from vera.runtime.wasi_host import execute_wasi_p2
    value = thrown(*cell)
    with pytest.raises(WasmTrapError) as info:
        execute_wasi_p2(_compile(value))
    assert info.value.kind == "uncaught_exception"
    assert_cut(value, str(info.value))


@browser
@pytest.mark.parametrize("cell", CELLS, ids=_id)
def test_the_browser_cuts_at_a_character(
    cell: tuple[int, int], tmp_path: Path,
) -> None:
    value = thrown(*cell)
    wasm = tmp_path / "cut.wasm"
    wasm.write_bytes(_compile(value).wasm_bytes)
    assert _NODE is not None
    out = _NODE(wasm, fn="main")
    assert out["trapKind"] == "uncaught_exception", out
    assert_cut(value, out["error"])


# --- The reported instance, as a user runs it ------------------------------

REPRO = (
    "public fn main(-> @Int)\n"
    "  requires(true) ensures(true) effects(<Exn<String>>)\n"
    "{\n"
    '  throw(string_concat(string_repeat("a", 63), "é and more"))\n'
    "}\n")


@pytest.mark.parametrize("target", ["wasmtime", "wasi-p2"])
def test_repro_vera_run_json_quotes_whole_characters(
    target: str, tmp_path: Path,
) -> None:
    source = tmp_path / "cut.vera"
    source.write_text(REPRO, encoding="utf-8")
    cmd = [sys.executable, "-m", "vera.cli", "run"]
    if target != "wasmtime":
        cmd += ["--target", target]
    proc = subprocess.run(
        cmd + ["--json", str(source)], capture_output=True, text=True,
        encoding="utf-8", timeout=300, check=False, cwd=tmp_path)
    assert proc.returncode == 1, (proc.returncode, proc.stderr[-800:])
    [diag] = json.loads(proc.stdout)["diagnostics"]
    assert diag["trap_kind"] == "uncaught_exception"
    assert quoted(diag["description"]) == "a" * 63 + ELLIPSIS


def test_a_string_within_the_cut_is_quoted_whole() -> None:
    """Negative space: 64 bytes ending in a two-byte character fit, so the
    cut never moves and no ellipsis is added."""
    value = "a" * 62 + "é"
    assert len(value.encode("utf-8")) == CUT
    with pytest.raises(WasmTrapError) as info:
        execute(_compile(value), fn_name="main")
    assert quoted(str(info.value)) == value
