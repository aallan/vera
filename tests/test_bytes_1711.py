"""Bytes in, out and through: the six operations of issue #1711.

A program gets bytes in with `IO.read_bytes`, out with `IO.write_bytes`,
and through with the UTF-8 conversions `string_to_bytes` and
`bytes_to_string` and base64 over bytes, `base64_encode_bytes` and
`base64_decode_bytes`.  The four conversions are compiled in place, so the
Python host, the browser runtime and the WASI 0.2 component run the same
code for them.  The two IO operations are host imports of the `io` family:
the Python host and the WASI command world move a file's bytes unchanged,
the browser runtime refuses both as it refuses `IO.read_file`, and the WASI
server world refuses both at compile, naming the interface its proxy world
lacks.

The class is a byte operation that loses, adds or changes a byte, or
answers `Ok` where `Err` is right or the reverse, on any host.  The
instrument crosses each operation with the hosts that run it:

- `bytes_to_string` against CPython's strict UTF-8 decoder over a table of
  the decision's inputs: every lone byte; every lead byte from `C0` to `FF`
  followed by each boundary of the continuation ranges (`7F`/`80`,
  `8F`/`90`, `9F`/`A0`, `BF`/`C0`), at two, three and four bytes; the
  third and fourth bytes' boundaries under each lead's lowest valid second
  byte; the encodings of the scalar values at the ends of every range of
  Unicode's table of well-formed sequences; and faults after an ASCII, a
  two-byte and a four-byte prefix, so the offset an `Err` names is held at
  positions past the first.  An `Ok` is held to the bytes it decoded, read
  back through `string_to_bytes`, and an `Err` to the offset CPython names
  (`UnicodeDecodeError.start`).
- `string_to_bytes` against `str.encode("utf-8")`, the empty string
  included, and its round trip through `bytes_to_string`.
- `base64_encode_bytes` against `base64.b64encode` (every byte value, and
  each of the three padding cases), its round trip through
  `base64_decode_bytes`, and `base64_decode_bytes` against the string
  decoder `base64_decode` on the same inputs, valid and invalid.
- `IO.write_bytes` then `IO.read_bytes` of every byte value, a file the
  test wrote (CR, LF, `00` and `FF` read back unchanged), an empty file, a
  missing file and a missing directory, natively and in the WASI command
  world, and a program whose only file operation is a write; the browser's
  refusal where the native host reads and writes; the server world's
  refusal.
- Three megabytes through each path while a collection runs.  Each cell
  takes well under a second, so none carries `stress`.

Products that are not cells: the browser and the WASI server world for the
file operations' round trip, which refuse them, and whose refusals are the
cells; and the text of an `Err` the file system gives, which names the
host's error (`FileNotFoundError`'s natively, `no-entry` in the WASI
component), so those cells hold it to the `Err` arm only.  The browser's and
the server world's refusal texts are the hosts' own, and are held whole.
"""

from __future__ import annotations

import base64
import json
import shutil
import subprocess
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline
from vera.codegen import CompileResult
from vera.runtime.wasi_host import execute_wasi_p2

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of its parametrised cells, and all of them when it changes this file or a
# module that decides the operations: their records and rows, their
# emitters and the widths code generation reads for them, and each host's
# implementation of the two IO operations.
pytestmark = pytest.mark.matrix(decides=[
    "vera/builtins.py",
    "vera/environment.py",
    "vera/wasm/calls_encoding.py",
    "vera/wasm/inference.py",
    "vera/codegen/api.py",
    "vera/runtime/heap.py",
    "vera/browser/runtime.mjs",
    "vera/codegen/wasi.py",
])

ROOT = Path(__file__).resolve().parent.parent
HARNESS = ROOT / "vera" / "browser" / "harness.mjs"
NODE = shutil.which("node")


def _node_supports_exnref() -> bool:
    """Whether the Node.js on PATH runs the browser harness's modules."""
    if NODE is None:
        return False
    try:
        proc = subprocess.run(
            [NODE, "--experimental-wasm-exnref", "-e", "0"],
            capture_output=True, timeout=5, check=False)
    except (OSError, subprocess.SubprocessError):
        return False
    return proc.returncode == 0


_HAS_NODE = _node_supports_exnref()


def _target_param(target: str) -> Any:
    if target == "browser":
        return pytest.param(target, marks=pytest.mark.skipif(
            not _HAS_NODE, reason="Node.js with exnref is not available"))
    return target


TARGETS = [_target_param(t) for t in ("native", "browser", "wasi-p2")]


# =====================================================================
# The programs
# =====================================================================

#: An `Int` from 0 to 255 as a `Byte`, an `Array<Int>` of them as an
#: `Array<Byte>`, and an `Array<Byte>` printed as its values.
_HELPERS = """\
private fn byte_of(@Byte -> @Byte)
  requires(true)
  ensures(@Byte.result == @Byte.0)
  effects(pure)
{
  @Byte.0
}

private fn to_byte(@Int -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  match int_to_byte(@Int.0) {
    Some(@Byte) -> @Byte.0,
    None -> byte_of(0)
  }
}

private fn bytes_of(@Array<Int> -> @Array<Byte>)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_map(@Array<Int>.0, fn(@Int -> @Byte) effects(pure) { to_byte(@Int.0) })
}

private fn show_bytes(@Array<Byte> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_join(array_map(@Array<Byte>.0, fn(@Byte -> @String) effects(pure) {
    int_to_string(byte_to_int(@Byte.0))
  }), ",")
}

"""

#: Allocates `n` strings of 4,096 bytes, each dead at once, and returns
#: their total length: run while a value is live, it grows the heap, and
#: the collector collects before every growth (the churn of
#: `tests/test_gc_mark_width_1510.py`).
_CHURN = """\
private fn churn(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { @Nat.1 } else {
    churn(@Nat.1 + string_length(string_repeat("y", 4096)), @Nat.0 - 1)
  }
}

"""


def _int_literal(vectors: list[list[int]]) -> str:
    return "[" + ", ".join(
        "[" + ", ".join(str(b) for b in v) + "]" for v in vectors) + "]"


def _show(data: Iterable[int]) -> str:
    return ",".join(str(b) for b in data)


# --- bytes_to_string --------------------------------------------------

#: The bytes either side of every boundary of the continuation ranges of
#: Unicode's table of well-formed UTF-8 (§3.9, Table 3-7): `80`..`BF`, and
#: the narrowed second bytes `A0`..`BF` (after `E0`), `80`..`9F` (`ED`),
#: `90`..`BF` (`F0`) and `80`..`8F` (`F4`).
_BOUNDS = (0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0)

#: Each lead byte's lowest valid second byte.
_LOWEST_SECOND = {0xE0: 0xA0, 0xF0: 0x90}

#: The scalar values at the ends of every row of the table.
_SCALAR_ENDS = (
    0x0, 0x7F, 0x80, 0x7FF, 0x800, 0xFFF, 0x1000, 0xCFFF, 0xD000, 0xD7FF,
    0xE000, 0xFFFF, 0x10000, 0x3FFFF, 0x40000, 0xFFFFF, 0x100000, 0x10FFFF,
)

#: Ill-formed tails, each after three prefixes that are well formed.
_FAULTS = ([0x80], [0xC2], [0xE0, 0x80], [0xED, 0xA0, 0x80],
           [0xF4, 0x90, 0x80, 0x80], [0xFF])
_PREFIXES = ([0x61], [0xC3, 0xA9], [0xF0, 0x9F, 0x98, 0x80, 0x61])


def utf8_vectors() -> list[list[int]]:
    """The decision's inputs (the module docstring's first bullet)."""
    vectors: list[list[int]] = [[b] for b in range(256)]
    for lead in range(0xC0, 0x100):
        for second in _BOUNDS:
            vectors.append([lead, second])
            vectors.append([lead, second, 0x80])
            vectors.append([lead, second, 0x80, 0x80])
    for lead in range(0xE0, 0xF5):
        second = _LOWEST_SECOND.get(lead, 0x80)
        for edge in _BOUNDS:
            vectors.append([lead, second, edge])
            vectors.append([lead, second, edge, 0x80])
            if lead >= 0xF0:
                vectors.append([lead, second, 0x80, edge])
    vectors.extend(list(chr(cp).encode("utf-8")) for cp in _SCALAR_ENDS)
    for prefix in _PREFIXES:
        for fault in _FAULTS:
            vectors.append(prefix + fault)
    return vectors


def decoded(vector: list[int]) -> str:
    """The line the decode program prints for *vector*: CPython's strict
    decoder is the oracle, `Err` naming the first byte of the first
    sequence that is not well formed."""
    try:
        bytes(vector).decode("utf-8")
    except UnicodeDecodeError as exc:
        return f"err invalid UTF-8 at byte {exc.start}"
    return f"ok {_show(vector)}"


def decode_program(vectors: list[list[int]]) -> str:
    return _HELPERS + f"""\
private fn decode_line(@Array<Byte> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match bytes_to_string(@Array<Byte>.0) {{
    Ok(@String) -> string_concat("ok ", show_bytes(string_to_bytes(@String.0))),
    Err(@String) -> string_concat("err ", @String.0)
  }}
}}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  let @Array<Array<Int>> = {_int_literal(vectors)};
  IO.print(string_join(array_map(@Array<Array<Int>>.0, fn(@Array<Int> -> @String) effects(pure) {{
    decode_line(bytes_of(@Array<Int>.0))
  }}), "\\n"));
  IO.print("\\n")
}}
"""


# --- string_to_bytes --------------------------------------------------

#: A string as Vera writes it, and its value.
_STRINGS: tuple[tuple[str, str], ...] = (
    ('""', ""),
    ('"a"', "a"),
    ('"héllo"', "héllo"),
    ('"€"', "€"),
    ('"😀"', "😀"),
    ('"a\\tb\\nc"', "a\tb\nc"),
    ('"\\0"', "\0"),
    ('"\\u{7F}\\u{80}\\u{7FF}\\u{800}\\u{FFFF}\\u{10000}\\u{10FFFF}"',
     "\x7f\x80߿ࠀ￿\U00010000\U0010ffff"),
)


def encode_program() -> str:
    calls = ", ".join(f"encode_line({written})" for written, _ in _STRINGS)
    return _HELPERS + f"""\
private fn encode_line(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Array<Byte> = string_to_bytes(@String.0);
  let @String = match bytes_to_string(@Array<Byte>.0) {{
    Ok(@String) -> if @String.0 == @String.1 then {{ "same" }} else {{ "differs" }},
    Err(@String) -> string_concat("err ", @String.0)
  }};
  string_concat(string_concat("[", show_bytes(@Array<Byte>.0)), string_concat("] ", @String.0))
}}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  IO.print(string_join([{calls}], "\\n"));
  IO.print("\\n")
}}
"""


def encoded() -> str:
    return "".join(
        f"[{_show(value.encode('utf-8'))}] same\n" for _, value in _STRINGS)


# --- base64 over bytes --------------------------------------------------

#: Byte sequences to encode: empty, each padding case, the two characters
#: past `9` (`+`, `/`), and every byte value.
_TO_ENCODE: tuple[list[int], ...] = (
    [], [0], [0, 1], [0, 1, 2], [255], [255, 254], [251, 255, 191],
    [77, 97, 110], list(range(256)),
)

#: Strings to decode with both decoders, valid and not.
_TO_DECODE: tuple[str, ...] = (
    "", "QQ==", "QUI=", "QUJD", "AAEC", "+/8=", "SGVsbG8=", "ABC", "QQ!!",
    "Q===", "====", "QQ=A", "a b=",
)


def base64_program() -> str:
    encodes = ", ".join(
        f"encode_line(bytes_of({_int_literal([v])[1:-1]}))" for v in _TO_ENCODE)
    decodes = ", ".join(f'decode_line("{s}")' for s in _TO_DECODE)
    return _HELPERS + f"""\
private fn bytes_result(@Result<Array<Byte>, String> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match @Result<Array<Byte>, String>.0 {{
    Ok(@Array<Byte>) -> string_concat("ok ", show_bytes(@Array<Byte>.0)),
    Err(@String) -> string_concat("err ", @String.0)
  }}
}}

private fn string_result(@Result<String, String> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match @Result<String, String>.0 {{
    Ok(@String) -> string_concat("ok ", show_bytes(string_to_bytes(@String.0))),
    Err(@String) -> string_concat("err ", @String.0)
  }}
}}

private fn encode_line(@Array<Byte> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @String = base64_encode_bytes(@Array<Byte>.0);
  string_concat(string_concat(string_concat("enc ", @String.0), " "),
    bytes_result(base64_decode_bytes(@String.0)))
}}

private fn decode_line(@String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{{
  string_concat(string_concat(string_concat("dec ", bytes_result(base64_decode_bytes(@String.0))),
    " | "), string_result(base64_decode(@String.0)))
}}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
  IO.print(string_join([{encodes}], "\\n"));
  IO.print("\\n");
  IO.print(string_join([{decodes}], "\\n"));
  IO.print("\\n")
}}
"""


#: The two errors spec §9.6.16 names for the string decoder.
_LENGTH_ERROR = "invalid base64 length"
_CHAR_ERROR = "invalid base64"


# --- the file operations ----------------------------------------------

#: The bytes the test writes for the program to read: CR, LF, NUL, `FF`
#: and a lone continuation byte, none of which may be translated or
#: replaced on the way in.
_GIVEN = b"\r\n\x00\xff\x80A\r\n"

_FILE_HELPERS = """\
private fn written(@Result<Unit, String> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<Unit, String>.0 {
    Ok(_) -> "write ok\\n",
    Err(@String) -> string_concat(string_concat("write err ", @String.0), "\\n")
  }
}

private fn read_line_of(@Result<Array<Byte>, String> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<Array<Byte>, String>.0 {
    Ok(@Array<Byte>) -> string_concat(string_concat("read [", show_bytes(@Array<Byte>.0)), "]\\n"),
    Err(@String) -> string_concat(string_concat("read err ", @String.0), "\\n")
  }
}

private fn read_arm(@Result<Array<Byte>, String> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<Array<Byte>, String>.0 {
    Ok(@Array<Byte>) -> "ok",
    Err(@String) -> "err"
  }
}

private fn write_arm(@Result<Unit, String> -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Result<Unit, String>.0 {
    Ok(_) -> "ok",
    Err(@String) -> "err"
  }
}

"""

_ROUND_TRIP = _HELPERS + _FILE_HELPERS + """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Array<Byte> = bytes_of(array_range(0, 256));
  IO.print(written(IO.write_bytes("all.bin", @Array<Byte>.0)));
  IO.print(read_line_of(IO.read_bytes("all.bin")));
  IO.print(read_line_of(IO.read_bytes("given.bin")));
  IO.print(read_line_of(IO.read_bytes("empty.bin")));
  IO.print(written(IO.write_bytes("nothing.bin", [])));
  IO.print(read_line_of(IO.read_bytes("nothing.bin")));
  IO.print(string_concat(string_concat("missing ", read_arm(IO.read_bytes("missing.bin"))), "\\n"));
  IO.print(string_concat(string_concat("no dir ", write_arm(IO.write_bytes("no-such-dir/x.bin", @Array<Byte>.0))), "\\n"))
}
"""

_ROUND_TRIP_STDOUT = (
    "write ok\n"
    f"read [{_show(range(256))}]\n"
    f"read [{_show(_GIVEN)}]\n"
    "read []\n"
    "write ok\n"
    "read []\n"
    "missing err\n"
    "no dir err\n"
)

#: The browser runtime's refusal of every file operation, `IO.read_file`'s.
_BROWSER_REFUSAL = "File I/O not available in browser"

_BROWSER_PAIR = _HELPERS + _FILE_HELPERS + """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(written(IO.write_bytes("all.bin", bytes_of([1, 2, 3]))));
  IO.print(read_line_of(IO.read_bytes("given.bin")))
}
"""


# --- three megabytes --------------------------------------------------

_BIG = 3_000_000


def _big_file() -> bytes:
    return bytes((i * 7 + i // 256) % 256 for i in range(_BIG))


_BIG_FILE_PROGRAM = _CHURN + """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.read_bytes("big.bin") {
    Ok(@Array<Byte>) -> {
      let @Nat = churn(0, 3000);
      let @Int = array_fold(@Array<Byte>.0, 0, fn(@Int, @Byte -> @Int) effects(pure) {
        @Int.0 + byte_to_int(@Byte.0)
      });
      IO.print(string_concat(string_concat(int_to_string(array_length(@Array<Byte>.0)), " "),
        string_concat(string_concat(int_to_string(@Int.0), " "), nat_to_string(@Nat.0))))
    },
    Err(@String) -> IO.print(string_concat("err ", @String.0))
  }
}
"""

#: Three megabytes of a string through `string_to_bytes`, base64 and back,
#: with the churn while the bytes are live.
_BIG_STRING_PROGRAM = _CHURN + """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Array<Byte> = string_to_bytes(string_repeat("ab\\u{E9}", 1000000));
  let @String = base64_encode_bytes(@Array<Byte>.0);
  let @Nat = churn(0, 3000);
  match base64_decode_bytes(@String.0) {
    Ok(@Array<Byte>) -> {
      let @Int = array_fold(@Array<Byte>.0, 0, fn(@Int, @Byte -> @Int) effects(pure) {
        @Int.0 + byte_to_int(@Byte.0)
      });
      let @String = match bytes_to_string(@Array<Byte>.0) {
        Ok(@String) -> nat_to_string(string_length(@String.0)),
        Err(@String) -> @String.0
      };
      IO.print(string_concat(string_concat(int_to_string(array_length(@Array<Byte>.0)), " "),
        string_concat(string_concat(int_to_string(@Int.0), " "),
          string_concat(string_concat(@String.0, " "), nat_to_string(@Nat.0)))))
    },
    Err(@String) -> IO.print(string_concat("err ", @String.0))
  }
}
"""


def _big_string_stdout() -> str:
    data = ("abé" * 1_000_000).encode("utf-8")
    return f"{len(data)} {sum(data)} {len(data)} {4096 * 3000}"


# =====================================================================
# Running a program
# =====================================================================

def _compile(source: str, name: str) -> CompileResult:
    compiled = pipeline.compile(source, file=f"{name}.vera")
    assert compiled.ok, [d.description for d in compiled.diagnostics][:5]
    return compiled.result


def _compile_eager(source: str, name: str,
                   monkeypatch: pytest.MonkeyPatch) -> CompileResult:
    """*source* compiled with `VERA_EAGER_GC=1`, which `$alloc` reads as it
    is emitted: every allocation collects first, so a pointer held across
    an allocation without a root is swept by that allocation."""
    with monkeypatch.context() as patch:
        patch.setenv("VERA_EAGER_GC", "1")
        result = _compile(source, name)
    assert "call $gc_collect" in result.wat.split("(func $alloc", 1)[1][:400]
    return result


def _stdout(result: CompileResult, target: str, tmp_path: Path) -> str:
    """What `main` prints on *target*, run from the working directory the
    caller set (the WASI component's preopened directory is `.`)."""
    if target == "native":
        ran = pipeline.run(result, budget_s=600)
        assert ran.trap is None, ran.trap
        return ran.stdout
    if target == "wasi-p2":
        return execute_wasi_p2(result).stdout
    assert target == "browser"
    wasm = tmp_path / "cell.wasm"
    wasm.write_bytes(result.wasm_bytes)
    proc = subprocess.run(
        [NODE or "node", "--experimental-wasm-exnref", str(HARNESS), str(wasm)],
        capture_output=True, text=True, encoding="utf-8", timeout=600,
        check=False)
    assert proc.returncode == 0, proc.stderr
    out = json.loads(proc.stdout)
    assert out.get("error") is None, out["error"]
    return str(out["stdout"])


# =====================================================================
# The conversions, on every host
# =====================================================================

@pytest.mark.parametrize("target", TARGETS)
def test_bytes_to_string_decodes_as_cpython_does(
    target: str, tmp_path: Path,
) -> None:
    """Every input of the decision table decodes to the bytes it holds, or
    is an `Err` naming the offset CPython's strict decoder names."""
    vectors = utf8_vectors()
    result = _compile(decode_program(vectors), "utf8_decode")
    lines = _stdout(result, target, tmp_path).split("\n")
    assert lines[-1] == ""
    got = lines[:-1]
    assert len(got) == len(vectors)
    wrong = [(v, g, decoded(v)) for v, g in zip(vectors, got, strict=True)
             if g != decoded(v)]
    assert wrong == [], wrong[:10]


@pytest.mark.parametrize("target", TARGETS)
def test_string_to_bytes_is_the_utf8_encoding(target: str, tmp_path: Path) -> None:
    """Each string's bytes are its UTF-8 encoding, and decode back to it."""
    result = _compile(encode_program(), "utf8_encode")
    assert _stdout(result, target, tmp_path) == encoded()


@pytest.mark.parametrize("target", TARGETS)
def test_base64_over_bytes(target: str, tmp_path: Path) -> None:
    """`base64_encode_bytes` is RFC 4648's encoding and decodes back to its
    input; `base64_decode_bytes` agrees with `base64_decode` on every input,
    valid or not, with the two errors spec §9.6.16 names."""
    result = _compile(base64_program(), "base64_bytes")
    lines = _stdout(result, target, tmp_path).split("\n")
    assert lines[-1] == ""
    encodes, decodes = lines[:len(_TO_ENCODE)], lines[len(_TO_ENCODE):-1]
    assert encodes == [
        f"enc {base64.b64encode(bytes(v)).decode('ascii')} ok {_show(v)}"
        for v in _TO_ENCODE]
    assert len(decodes) == len(_TO_DECODE)
    for text, line in zip(_TO_DECODE, decodes, strict=True):
        as_bytes, _, as_string = line.removeprefix("dec ").partition(" | ")
        assert as_bytes == as_string, (text, line)
    rendered = dict(zip(_TO_DECODE, (d.removeprefix("dec ").partition(" | ")[0]
                                     for d in decodes), strict=True))
    for text in ("", "QQ==", "QUI=", "QUJD", "AAEC", "+/8=", "SGVsbG8="):
        assert rendered[text] == f"ok {_show(base64.b64decode(text))}", text
    assert rendered["ABC"] == f"err {_LENGTH_ERROR}"
    assert rendered["QQ!!"] == f"err {_CHAR_ERROR}"


# =====================================================================
# The file operations
# =====================================================================

def _write_inputs(directory: Path) -> None:
    (directory / "given.bin").write_bytes(_GIVEN)
    (directory / "empty.bin").write_bytes(b"")


@pytest.mark.parametrize("target", ["native", "wasi-p2"])
def test_bytes_round_trip_through_a_file(
    target: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Every byte value written and read back, a file the test wrote read
    unchanged, an empty file read as no bytes, a missing file and a missing
    directory an `Err`: natively and in the WASI command world, whose
    component reads its working directory as the preopened `/`."""
    _write_inputs(tmp_path)
    monkeypatch.chdir(tmp_path)
    result = _compile(_ROUND_TRIP, "round_trip")
    assert _stdout(result, target, tmp_path) == _ROUND_TRIP_STDOUT
    assert (tmp_path / "all.bin").read_bytes() == bytes(range(256))
    assert (tmp_path / "nothing.bin").read_bytes() == b""


#: A program whose one file operation is a write: in the WASI command world
#: the adapter's preopen descriptor and its filesystem messages must follow
#: from `IO.write_bytes` alone, where a read in the same program would
#: supply them.
_WRITE_ONLY = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.write_bytes("w.bin", string_to_bytes("\\u{0}\\u{FF}\\r\\n")) {
    Ok(_) -> IO.print("ok\\n"),
    Err(@String) -> IO.print(@String.0)
  }
}
"""


@pytest.mark.parametrize("target", ["native", "wasi-p2"])
def test_a_write_alone_reaches_the_file(
    target: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A program whose only file operation is `IO.write_bytes` writes its
    bytes, natively and in the WASI command world."""
    monkeypatch.chdir(tmp_path)
    result = _compile(_WRITE_ONLY, "write_only")
    assert _stdout(result, target, tmp_path) == "ok\n"
    assert (tmp_path / "w.bin").read_bytes() == "\0ÿ\r\n".encode("utf-8")


@pytest.mark.skipif(not _HAS_NODE, reason="Node.js with exnref is not available")
def test_the_browser_refuses_the_file_operations_the_native_host_performs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The same module writes and reads under wasmtime and gets the browser
    runtime's refusal, `IO.read_file`'s text, from both operations: the file
    exists and the directory is writable, so the native `Ok` arms are
    reachable and the browser's `Err` is the runtime's, not the file
    system's."""
    _write_inputs(tmp_path)
    monkeypatch.chdir(tmp_path)
    result = _compile(_BROWSER_PAIR, "browser_pair")
    assert _stdout(result, "native", tmp_path) == (
        f"write ok\nread [{_show(_GIVEN)}]\n")
    assert (tmp_path / "all.bin").read_bytes() == b"\x01\x02\x03"
    assert _stdout(result, "browser", tmp_path) == (
        f"write err {_BROWSER_REFUSAL}\nread err {_BROWSER_REFUSAL}\n")


_SERVER_CALLS = {
    "read_bytes": 'let @Result<Array<Byte>, String> = IO.read_bytes("x.bin");',
    "write_bytes": 'let @Result<Unit, String> = IO.write_bytes("x.bin", []);',
}


@pytest.mark.parametrize("op", sorted(_SERVER_CALLS))
def test_the_server_world_refuses_the_file_operations(op: str) -> None:
    """`--world server` refuses each, naming it and the interface the
    `wasmtime serve` proxy world lacks, as it refuses `IO.read_file`."""
    from vera.codegen.wasi import emit_wasi_component

    result = _compile(f"""\
public fn handle(@Request -> @Response)
  requires(true)
  ensures(true)
  effects(<HttpServer, IO>)
{{
  {_SERVER_CALLS[op]}
  Response(200, map_new(), "hi")
}}
""", f"server_{op}")
    with pytest.raises(ValueError) as refused:
        emit_wasi_component(result, world="server")
    assert (f"does not support IO.{op} (wasi:filesystem is not in the"
            " wasmtime serve proxy world)") in str(refused.value)


def test_repro_1711_a_binary_file_is_its_bytes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The issue's instance: a file whose bytes are not UTF-8 is an `Err`
    from `IO.read_file` on the native host, and its bytes from
    `IO.read_bytes`."""
    image = b"\x89PNG\r\n\x1a\n\xff"
    (tmp_path / "image.bin").write_bytes(image)
    monkeypatch.chdir(tmp_path)
    result = _compile(_HELPERS + _FILE_HELPERS + """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @String = match IO.read_file("image.bin") {
    Ok(@String) -> "text ok",
    Err(@String) -> "text err"
  };
  IO.print(string_concat(@String.0, "\\n"));
  IO.print(read_line_of(IO.read_bytes("image.bin")))
}
""", "repro_1711")
    assert _stdout(result, "native", tmp_path) == (
        f"text err\nread [{_show(image)}]\n")


# =====================================================================
# Three megabytes, with the collector running
# =====================================================================

@pytest.mark.parametrize("target", ["native", "wasi-p2"])
def test_three_megabytes_read_from_a_file(
    target: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A 3,000,000-byte file read whole and held live across 12 MB of
    churn, which collects before every growth of the heap, then summed."""
    data = _big_file()
    (tmp_path / "big.bin").write_bytes(data)
    monkeypatch.chdir(tmp_path)
    result = _compile(_BIG_FILE_PROGRAM, "big_file")
    assert _stdout(result, target, tmp_path) == (
        f"{_BIG} {sum(data)} {4096 * 3000}")


@pytest.mark.parametrize("target", TARGETS)
def test_three_megabytes_through_the_conversions(
    target: str, tmp_path: Path,
) -> None:
    """Three megabytes of a string through `string_to_bytes`, base64 both
    ways and `bytes_to_string`, held live across the churn."""
    result = _compile(_BIG_STRING_PROGRAM, "big_string")
    assert _stdout(result, target, tmp_path) == _big_string_stdout()


# =====================================================================
# The same programs with a collection at every allocation
# =====================================================================

#: Every seventh input of the decode table: each class of the table at
#: once, without a collection per allocation over all of it.
_EAGER_VECTORS = utf8_vectors()[::7]


@pytest.mark.parametrize("target", TARGETS)
def test_the_conversions_under_eager_collection(
    target: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The decode, encode and base64 programs compiled with
    `VERA_EAGER_GC=1` print what they print under ordinary collection: the
    block each conversion allocates is rooted across the allocations after
    it."""
    decode = _compile_eager(decode_program(_EAGER_VECTORS), "eager_decode",
                            monkeypatch)
    assert _stdout(decode, target, tmp_path) == "".join(
        decoded(v) + "\n" for v in _EAGER_VECTORS)
    encode = _compile_eager(encode_program(), "eager_encode", monkeypatch)
    assert _stdout(encode, target, tmp_path) == encoded()
    b64 = _compile_eager(base64_program(), "eager_base64", monkeypatch)
    plain = _compile(base64_program(), "plain_base64")
    assert _stdout(b64, target, tmp_path) == _stdout(plain, target, tmp_path)


@pytest.mark.parametrize("target", ["native", "wasi-p2"])
def test_the_file_operations_under_eager_collection(
    target: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The file round trip compiled with `VERA_EAGER_GC=1`: the array the
    host builds is rooted across the allocation of the `Ok` around it."""
    _write_inputs(tmp_path)
    monkeypatch.chdir(tmp_path)
    result = _compile_eager(_ROUND_TRIP, "eager_round_trip", monkeypatch)
    assert _stdout(result, target, tmp_path) == _ROUND_TRIP_STDOUT
    assert (tmp_path / "all.bin").read_bytes() == bytes(range(256))


# =====================================================================
# The checker's view
# =====================================================================

#: Each operation called with an argument of the wrong type, the code that
#: refuses it, and the same call with the right type.
_WRONG_ARGUMENT = {
    "string_to_bytes": ("string_to_bytes(1)", 'string_to_bytes("a")',
                        "@Array<Byte>", "pure", "E202"),
    "bytes_to_string": ('bytes_to_string("a")', "bytes_to_string([])",
                        "@Result<String, String>", "pure", "E202"),
    "base64_encode_bytes": ('base64_encode_bytes("a")', "base64_encode_bytes([])",
                            "@String", "pure", "E202"),
    "base64_decode_bytes": ("base64_decode_bytes(1)", 'base64_decode_bytes("QQ==")',
                            "@Result<Array<Byte>, String>", "pure", "E202"),
    "read_bytes": ("IO.read_bytes(1)", 'IO.read_bytes("a")',
                   "@Result<Array<Byte>, String>", "<IO>", "E204"),
    "write_bytes": ('IO.write_bytes("a", "b")', 'IO.write_bytes("a", [])',
                    "@Result<Unit, String>", "<IO>", "E204"),
}


def _call_source(call: str, ret: str, effect: str) -> str:
    row = "effects(pure)" if effect == "pure" else f"effects({effect})"
    return (f"public fn f(@Unit -> {ret})\n  requires(true)\n  ensures(true)\n"
            f"  {row}\n{{\n  {call}\n}}\n")


@pytest.mark.parametrize("op", sorted(_WRONG_ARGUMENT))
def test_a_wrong_argument_type_is_refused(op: str) -> None:
    """The wrong type is refused with the call's argument code, and the
    nearest accepted neighbour, the same call at the right type, checks
    clean with the declared result type."""
    wrong, right, ret, effect, code = _WRONG_ARGUMENT[op]
    refused = pipeline.check(_call_source(wrong, ret, effect))
    assert [d.error_code for d in refused.errors] == [code], [
        d.description for d in refused.errors]
    accepted = pipeline.check(_call_source(right, ret, effect))
    assert accepted.ok, [d.description for d in accepted.errors]
    assert not accepted.warnings, [d.description for d in accepted.warnings]


def test_the_operations_are_published_with_their_version() -> None:
    """`vera builtins --json` lists the four conversions at the version
    that adds them, and `vera effects --json` lists the two IO operations
    among `IO`'s."""
    from vera.introspect import builtins_payload, effects_payload

    since = {item["name"]: item["since"] for item in builtins_payload()["items"]}
    for name in ("string_to_bytes", "bytes_to_string",
                 "base64_encode_bytes", "base64_decode_bytes"):
        assert since.get(name) == "0.2.4", name
    io = next(item for item in effects_payload()["items"] if item["name"] == "IO")
    assert {"read_bytes", "write_bytes"} <= set(io["ops"])
