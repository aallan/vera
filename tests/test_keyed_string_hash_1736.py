"""A `String` key's hash in the persistent `Map` and `Set` is keyed for each
instantiation (#1736).

At c9235415 the trie hashed a `String` key by FNV-1a over its bytes through
a bijective mixer, with no key, so `String` keys chosen to share a hash
shared one collision node, which every operation on it searches and copies
whole.  The hash is now SipHash-1-3 under a 128-bit key the module draws
from its host once per instantiation, through the `hash_key` import:
`os.urandom` natively, `crypto.getRandomValues` in the browser, and
`wasi:random` inside a WASI component, so a stock host supplies it.

The class is every `String`-keyed trie on every host: a stored entry's hash
is SipHash-1-3 of the key's bytes under the instantiation's key (checked
against the reference below, never against the module's own hash read
back), each instantiation draws its own key and none is zero, no output
depends on the key, and keys that share a path through the trie under one
key do not share it under another.  The negative space: every other key
representation hashes as it did and its module draws no key, and the `Hash`
ability's `hash()` of a `String` is still the deterministic FNV-1a spec
§9.8.1 promises.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

import pytest
import wasmtime

from tests import pipeline
from tests.test_persistent_map_set_1676 import (
    _browser,
    _drive,
    _needs_node,
    _needs_wasmtime_cli,
    _serve,
    _trie,
    _wasi_cli,
)
from vera.codegen import CompileResult
from vera.wasm import hamt

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of its parametrised cells, and every cell when it changes this file or a
# module that decides the class.
pytestmark = pytest.mark.matrix(decides=[
    "vera/wasm/hamt.py",
    "vera/codegen/api.py",
    "vera/browser/runtime.mjs",
    "vera/codegen/wasi.py",
])


# =====================================================================
# The reference: SipHash-c-d in Python, held to two outside oracles
# =====================================================================

_MASK = (1 << 64) - 1


def _rotl(x: int, b: int) -> int:
    return ((x << b) | (x >> (64 - b))) & _MASK


def siphash(k0: int, k1: int, data: bytes, c: int = 1, d: int = 3) -> int:
    """SipHash-c-d of *data* under the key whose two little-endian 64-bit
    words are *k0* and *k1*: SipHash-1-3 by default, CPython's string hash."""
    v0 = k0 ^ 0x736F6D6570736575
    v1 = k1 ^ 0x646F72616E646F6D
    v2 = k0 ^ 0x6C7967656E657261
    v3 = k1 ^ 0x7465646279746573

    def rounds(n: int) -> None:
        nonlocal v0, v1, v2, v3
        for _ in range(n):
            v0 = (v0 + v1) & _MASK
            v1 = _rotl(v1, 13) ^ v0
            v0 = _rotl(v0, 32)
            v2 = (v2 + v3) & _MASK
            v3 = _rotl(v3, 16) ^ v2
            v0 = (v0 + v3) & _MASK
            v3 = _rotl(v3, 21) ^ v0
            v2 = (v2 + v1) & _MASK
            v1 = _rotl(v1, 17) ^ v2
            v2 = _rotl(v2, 32)

    whole = len(data) - len(data) % 8
    for i in range(0, whole, 8):
        m = int.from_bytes(data[i:i + 8], "little")
        v3 ^= m
        rounds(c)
        v0 ^= m
    m = (len(data) & 0xFF) << 56 | int.from_bytes(data[whole:], "little")
    v3 ^= m
    rounds(c)
    v0 ^= m
    v2 ^= 0xFF
    rounds(d)
    return v0 ^ v1 ^ v2 ^ v3


def fnv1a(data: bytes) -> int:
    """64-bit FNV-1a, the `Hash` ability's `String` hash."""
    h = 0xCBF29CE484222325
    for byte in data:
        h = ((h ^ byte) * 0x100000001B3) & _MASK
    return h


def _signed(word: int) -> int:
    return word - (1 << 64) if word >= 1 << 63 else word


def _unsigned(word: int) -> int:
    return word & _MASK


#: Inputs either side of every boundary SipHash's word loop and tail have.
_REFERENCE_SAMPLES = [bytes(range(n)) for n in range(1, 40)] + [
    b"probe", "café ☃".encode(), b"x" * 1000]


@pytest.mark.skipif(
    sys.hash_info.algorithm != "siphash13" or sys.hash_info.cutoff != 0,
    reason="this interpreter does not hash bytes by SipHash-1-3")
def test_the_reference_is_cpythons_siphash13() -> None:
    """CPython hashes `bytes` by SipHash-1-3, and `PYTHONHASHSEED=0` makes its
    key zero: its hash of every sample is the reference's under the zero key
    (as CPython reads it: signed, -1 taken as -2)."""
    code = ("import sys\n"
            "for line in sys.stdin.read().split():\n"
            "    print(hash(bytes.fromhex(line)))\n")
    env = {k: v for k, v in os.environ.items()
           if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE")}
    env["PYTHONHASHSEED"] = "0"
    proc = subprocess.run(
        [sys.executable, "-c", code], input="\n".join(s.hex() for s in _REFERENCE_SAMPLES),
        capture_output=True, text=True, encoding="utf-8", env=env, timeout=60, check=True)
    cpython = [int(line) for line in proc.stdout.split()]
    reference = [-2 if (h := _signed(siphash(0, 0, s))) == -1 else h for s in _REFERENCE_SAMPLES]
    assert reference == cpython


def test_the_reference_meets_the_siphash_papers_vectors() -> None:
    """The SipHash paper's SipHash-2-4 vectors, under the key 00 01 .. 0f:
    the empty message and the fifteen bytes 00 .. 0e."""
    key = bytes(range(16))
    k0, k1 = int.from_bytes(key[:8], "little"), int.from_bytes(key[8:], "little")
    assert siphash(k0, k1, b"", 2, 4) == 0x726FDB47DD0E0E31
    assert siphash(k0, k1, bytes(range(15)), 2, 4) == 0xA129CA6149BE45E5


# =====================================================================
# The native host's key, drawn or supplied
# =====================================================================

@contextmanager
def _native_key(words: list[int] | None = None) -> Iterator[list[int]]:
    """The words the native host's key binder hands a module while the
    block runs: drawn from the operating system, or *words* in turn.  The
    list it yields records every word handed out."""
    from vera.codegen import api

    drawn: list[int] = []
    real: Callable[[], int] | None = getattr(api, "_hash_key_word", None)
    supply = iter(words) if words is not None else None

    def word() -> int:
        value = next(supply) if supply is not None else (real() if real else 0)
        drawn.append(value)
        return value

    with mock.patch.object(api, "_hash_key_word", word, create=True):
        yield drawn


def _run_keyed(result: CompileResult) -> tuple[object, bytes]:
    """`main`'s value and the module's memory after a pure program runs,
    its key bound by the native host's own binder and every other import
    refused."""
    from vera.codegen import api

    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    module = wasmtime.Module(engine, result.wat)
    linker = wasmtime.Linker(engine)
    keyed = False
    for imported in module.imports:
        if (imported.module, imported.name) == ("vera", "hash_key"):
            keyed = True
            continue

        def refuse(*args: object, _name: str = str(imported.name)) -> None:
            raise AssertionError(f"the module called the host import {_name} {args}")
        assert isinstance(imported.type, wasmtime.FuncType), imported.name
        linker.define_func(str(imported.module), str(imported.name), imported.type, refuse)
    if keyed:
        api.HOST_BINDERS["hash"](linker, {"hash_key"}, None)  # type: ignore[arg-type]
    exports = linker.instantiate(store, module).exports(store)
    main = exports["main"]
    assert isinstance(main, wasmtime.Func)
    value = main(store, *([0] if main.type(store).params else []))
    memory = exports["memory"]
    assert isinstance(memory, wasmtime.Memory)
    return value, memory.read(store, 0, memory.data_len(store))


def _i32(mem: bytes, at: int) -> int:
    return int.from_bytes(mem[at:at + 4], "little")


def _i64(mem: bytes, at: int) -> int:
    return int.from_bytes(mem[at:at + 8], "little")


def _entries(mem: bytes, header: int) -> list[tuple[bytes, int, int]]:
    """Every entry of the `String`-keyed trie under *header*: its key's
    bytes, its stored hash, and the number of branches above it."""
    found: list[tuple[bytes, int, int]] = []

    def entry(at: int, depth: int) -> None:
        word = _i64(mem, at + 16)
        ptr, length = word & 0xFFFFFFFF, word >> 32
        found.append((mem[ptr:ptr + length], _i64(mem, at), depth))

    def walk(node: int, shift: int, depth: int) -> None:
        if shift > hamt.LAST_SHIFT:
            for i in range(_i32(mem, node)):
                entry(_i32(mem, node + 4 + 4 * i), depth)
            return
        dm, nm = _i32(mem, node), _i32(mem, node + 4)
        ne = bin(dm).count("1")
        for i in range(ne):
            entry(_i32(mem, node + 8 + 4 * i), depth + 1)
        for j in range(bin(nm).count("1")):
            walk(_i32(mem, node + 8 + 4 * (ne + j)), shift + 5, depth + 1)

    root = _i32(mem, header + 4)
    if root:
        walk(root, 0, 0)
    return found


def _vera_string(text: str) -> str:
    assert '"' not in text and "\\" not in text, text
    return f'"{text}"'


# =====================================================================
# Every stored hash is SipHash-1-3 under the instantiation's key
# =====================================================================

#: Keys of every length either side of SipHash's 8-byte words up to five
#: of them, multi-byte UTF-8, and one of a thousand bytes.
_LENGTHS_KEYS = (
    ["abcdefghijklmnopqrstuvwxyz0123456789ABCDE"[:n] for n in range(41)]
    + ["café", "☃☃☃", "naïve ☃ über"])


def _every_length_program() -> str:
    lets = ["  let @Map<String, Int> = map_new();"]
    for i, key in enumerate(_LENGTHS_KEYS):
        lets.append(f"  let @Map<String, Int> = map_insert(@Map<String, Int>.0, {_vera_string(key)}, {i});")
    lets.append(f'  let @Map<String, Int> = map_insert(@Map<String, Int>.0, string_repeat("ab", 500), {len(_LENGTHS_KEYS)});')
    body = "\n".join(lets)
    return f"""\
public fn main(@Unit -> @Map<String, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{{
{body}
  @Map<String, Int>.0
}}
"""


def test_repro_1736_every_stored_hash_is_siphash13_under_the_instantiations_key() -> None:
    """At c9235415 the module drew no key and stored FNV-1a through
    MurmurHash3's finalizer.  Each entry's stored hash is the reference's
    SipHash-1-3 of the key's UTF-8 bytes under the two words the native
    host drew for this instantiation, at every length from 0 to 40 bytes,
    multi-byte keys and a 1,000-byte key, and the trie keeps its layout."""
    result = pipeline.compile(_every_length_program(), file="lengths.vera").result
    assert result.ok, result.diagnostics
    with _native_key() as drawn:
        header, mem = _run_keyed(result)
    assert len(drawn) == 2, f"the module drew {len(drawn)} words of a key from its host"
    k0, k1 = (_unsigned(w) for w in drawn)
    assert isinstance(header, int)
    entries = _entries(mem, header)
    want = [k.encode() for k in _LENGTHS_KEYS] + [b"ab" * 500]
    assert sorted(e[0] for e in entries) == sorted(want)
    assert [(key, stored) for key, stored, _ in entries] == [
        (key, siphash(k0, k1, key)) for key, _, _ in entries]
    assert _trie(mem, header) == (len(want), [])


# =====================================================================
# Each host: two instantiations, two keys, neither zero
# =====================================================================

def _key_probe(name: str) -> tuple[str, tuple[str, ...]]:
    """``map_size`` answers, for a map of one entry, the hash that entry
    stored, and for an empty one the key's first word; ``set_size`` the
    key's second.  A program prints what its instantiation drew and stored."""
    if name == "map_size":
        body = ["local.get $m", "i32.load",
                "if (result i64)",
                "local.get $m", "i32.load offset=4", "i32.load offset=8", "i64.load",
                "else", "global.get $hamt$k0", "end"]
        return hamt._func("map_size", [("m", "i32")], ["i64"], [], body), ()
    if name == "set_size":
        return hamt._func("set_size", [("m", "i32")], ["i64"], [], ["global.get $hamt$k1"]), ()
    return _REAL_HELPER(name)


_REAL_HELPER = hamt.helper

_PROBE_LETS = """\
  let @Map<String, Int> = map_insert(map_new(), "probe", 1);
  let @Map<String, Int> = map_new();
  let @Set<String> = set_new();
  let @String = string_join([int_to_string(map_size(@Map<String, Int>.1)), int_to_string(map_size(@Map<String, Int>.0)), int_to_string(set_size(@Set<String>.0))], " ");"""

_PROBE_MAIN = f"""\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
{_PROBE_LETS}
  IO.print(@String.0);
  IO.print("\\n")
}}
"""

_PROBE_HANDLER = f"""\
public fn handle(@Request -> @Response)
  requires(true)
  ensures(true)
  effects(<HttpServer>)
{{
{_PROBE_LETS}
  Response(200, map_new(), @String.0)
}}
"""


def _probe_compile(source: str, monkeypatch: pytest.MonkeyPatch) -> CompileResult:
    with monkeypatch.context() as patch:
        patch.setattr(hamt, "helper", _key_probe)
        result = pipeline.compile(source, file="probe.vera").result
    assert "(global $hamt$k0" in result.wat, "the module holds no key"
    assert result.ok, result.diagnostics
    return result


def _probed(out: str) -> tuple[int, int, int]:
    stored, k0, k1 = (_unsigned(int(part)) for part in out.split())
    return stored, k0, k1


def _in_browser(result: CompileResult, tmp_path: Path) -> str:
    tmp_path.mkdir(parents=True, exist_ok=True)
    return _browser(result, tmp_path)


#: How each host runs a program: each call is an instantiation of its own.
_PROBE_HOSTS: dict[str, Callable[[CompileResult, Path], str]] = {
    "native": lambda result, _tmp: pipeline.run(result).execution.stdout,
    "browser": _in_browser,
    "wasi-cli": lambda result, _tmp: _wasi_cli(result),
}


def _served(result: CompileResult, tmp_path: Path,
            headers: list[tuple[str, str]] | None = None) -> tuple[int, str]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    return _serve(result, tmp_path, headers)


def _probe_param(host: str) -> object:
    return pytest.param(host, marks=_needs_node) if host == "browser" else host


def _assert_two_keys(runs: list[tuple[int, int, int]]) -> None:
    (h1, a0, a1), (h2, b0, b1) = runs
    assert 0 not in (a0, a1, b0, b1), runs
    assert (a0, a1) != (b0, b1), "two instantiations drew one key"
    assert h1 == siphash(a0, a1, b"probe") and h2 == siphash(b0, b1, b"probe"), runs
    assert h1 != h2


@pytest.mark.parametrize("host", [_probe_param(h) for h in _PROBE_HOSTS])
def test_repro_1736_two_instantiations_draw_two_keys(
    host: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Each host hands each instantiation a key of its own, neither of whose
    words is zero, and the entry the module stores hashes under it."""
    result = _probe_compile(_PROBE_MAIN, monkeypatch)
    runs = [_probed(_PROBE_HOSTS[host](result, tmp_path / str(i))) for i in range(2)]
    _assert_two_keys(runs)


_PROBE_JSON = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Map<String, Json> = match json_parse("{\\"probe\\": 1}") {
    Ok(@Json) -> match @Json.0 { JObject(@Map<String, Json>) -> @Map<String, Json>.0, _ -> map_new() },
    Err(@String) -> map_new()
  };
  let @Map<String, Int> = map_new();
  let @Set<String> = set_new();
  IO.print(string_join([int_to_string(map_size(@Map<String, Json>.0)), int_to_string(map_size(@Map<String, Int>.0)), int_to_string(set_size(@Set<String>.0))], " "));
  IO.print("\\n")
}
"""


@pytest.mark.parametrize("host", [_probe_param(h) for h in ("native", "browser")])
def test_repro_1736_a_map_the_host_builds_hashes_under_the_key(
    host: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The JSON host builds a `JObject`'s map through the module's own
    `map_from_arrays$ks_vb`, so its entries hash under the instantiation's
    key like any other."""
    result = _probe_compile(_PROBE_JSON, monkeypatch)
    stored, k0, k1 = _probed(_PROBE_HOSTS[host](result, tmp_path))
    assert 0 not in (k0, k1)
    assert stored == siphash(k0, k1, b"probe")


def test_repro_1736_the_native_key_is_the_one_the_host_drew(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    result = _probe_compile(_PROBE_MAIN, monkeypatch)
    with _native_key() as drawn:
        out = pipeline.run(result).execution.stdout
    _stored, k0, k1 = _probed(out)
    assert [k0, k1] == [_unsigned(w) for w in drawn]


def test_repro_1736_the_native_server_draws_a_key_per_request(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`vera serve` instantiates the module for each request, and the
    `Request`'s headers are built through the module's map, so each request
    hashes under a key of its own."""
    result = _probe_compile(_PROBE_HANDLER, monkeypatch)
    runs = []
    for _ in range(2):
        status, body = _drive(result, [("x-a", "1")])
        assert status == 200, body
        runs.append(_probed(body))
    _assert_two_keys(runs)


@_needs_wasmtime_cli
def test_repro_1736_the_server_world_draws_a_key_per_request(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Under the stock `wasmtime serve` the component draws its key from its
    own `wasi:random`, with no Vera host."""
    result = _probe_compile(_PROBE_HANDLER, monkeypatch)
    runs = []
    for i in range(2):
        status, body = _served(result, tmp_path / str(i), [("x-a", "1")])
        assert status == 200, body
        runs.append(_probed(body))
    _assert_two_keys(runs)


# =====================================================================
# No output depends on the key
# =====================================================================

_DETERMINISM_KEYS = [
    "", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh",
    "abcdefghi", "abcdefghijklmno", "abcdefghijklmnop", "abcdefghijklmnopq",
    "café", "☃", "naïve ☃ über", "probe",
]
_LONG = "x" * 100


def _determinism_program(handler: bool = False) -> str:
    keys = [_vera_string(k) for k in _DETERMINISM_KEYS] + ['string_repeat("x", 100)']
    lets = ["  let @Map<String, Int> = map_new();"]
    lets += [f"  let @Map<String, Int> = map_insert(@Map<String, Int>.0, {k}, {i});"
             for i, k in enumerate(keys)]
    lets += [
        '  let @Map<String, Int> = map_insert(@Map<String, Int>.0, "abc", 100);',
        '  let @Map<String, Int> = map_remove(@Map<String, Int>.0, "abcde");',
        '  let @Map<String, Int> = map_remove(@Map<String, Int>.0, "absent");',
        '  let @Map<String, Int> = map_insert(@Map<String, Int>.0, "abcde", 55);',
        "  let @Set<String> = set_new();",
    ]
    lets += [f"  let @Set<String> = set_add(@Set<String>.0, {k});" for k in keys]
    lets += [
        '  let @Set<String> = set_add(@Set<String>.0, "ab");',
        '  let @Set<String> = set_remove(@Set<String>.0, "abcdefg");',
    ]
    probes = [*keys, '"absent"']
    gets = ", ".join(
        f'match map_get(@Map<String, Int>.0, {k}) {{ Some(@Int) -> int_to_string(@Int.0), None -> "-" }}'
        for k in probes)
    has = ", ".join(f'if set_contains(@Set<String>.0, {k}) then {{ "1" }} else {{ "0" }}' for k in probes)
    parts = [
        "int_to_string(map_size(@Map<String, Int>.0))",
        'string_join(map_keys(@Map<String, Int>.0), "|")',
        'string_join(array_map(map_values(@Map<String, Int>.0), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ",")',
        "int_to_string(array_fold(map_values(@Map<String, Int>.0), 7, fn(@Int, @Int -> @Int) effects(pure) { (@Int.1 * 31 + @Int.0) % 1000000007 }))",
        f'string_join([{gets}], ",")',
        "int_to_string(set_size(@Set<String>.0))",
        'string_join(set_to_array(@Set<String>.0), "|")',
        f'string_join([{has}], "")',
    ]
    lets.append(f"  let @String = string_join([{', '.join(parts)}], \" \");")
    body = "\n".join(lets)
    if handler:
        return f"""\
public fn handle(@Request -> @Response)
  requires(true)
  ensures(true)
  effects(<HttpServer>)
{{
{body}
  Response(200, map_new(), @String.0)
}}
"""
    return f"""\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{{
{body}
  IO.print(@String.0);
  IO.print("\\n")
}}
"""


def _expected_transcript() -> str:
    """What the program prints, from the semantics of spec §9.4.2 and §9.4.3
    (a Python dict keeps exactly that order), which no key can move."""
    keys = [*_DETERMINISM_KEYS, _LONG]
    m: dict[str, int] = {}
    for i, k in enumerate(keys):
        m[k] = i
    m["abc"] = 100
    del m["abcde"]
    m["abcde"] = 55
    s: dict[str, None] = dict.fromkeys(keys)
    del s["abcdefg"]
    probes = [*keys, "absent"]
    fold = 7
    for v in m.values():
        fold = (fold * 31 + v) % 1000000007
    return " ".join([
        str(len(m)), "|".join(m), ",".join(str(v) for v in m.values()), str(fold),
        ",".join(str(m[k]) if k in m else "-" for k in probes),
        str(len(s)), "|".join(s), "".join("1" if k in s else "0" for k in probes),
    ])


#: The two keys the native cells hand a module: the SipHash paper's test
#: key, 00 01 .. 0f, and the sixteen bytes after it.
K1 = (0x0706050403020100, 0x0F0E0D0C0B0A0908)
K2 = (0x1716151413121110, 0x1F1E1D1C1B1A1918)


def test_outputs_do_not_depend_on_the_native_key() -> None:
    """Under the two test keys and a drawn one, the program prints what the
    model says: insertion, a key inserted again, a removed key inserted
    again, lookups of present and absent keys, and both enumerations."""
    result = pipeline.compile(_determinism_program(), file="determinism.vera").result
    assert result.ok, result.diagnostics
    outs = []
    for words in ([*K1], [*K2], None):
        with _native_key([_signed(w) for w in words] if words else None):
            outs.append(pipeline.run(result).execution.stdout)
    assert outs == [_expected_transcript() + "\n"] * 3


@pytest.mark.parametrize("host", [_probe_param(h) for h in ("browser", "wasi-cli")])
def test_outputs_do_not_depend_on_the_key(
    host: str, tmp_path: Path,
) -> None:
    """Two instantiations, two keys (the probe cells above show each host
    draws one of its own), one transcript: the model's."""
    result = pipeline.compile(_determinism_program(), file="determinism.vera").result
    assert result.ok, result.diagnostics
    run = _PROBE_HOSTS[host]
    outs = [run(result, tmp_path / str(i)) for i in range(2)]
    assert outs == [_expected_transcript() + "\n"] * 2


def test_the_native_server_answers_alike_under_any_key() -> None:
    result = pipeline.compile(_determinism_program(handler=True), file="determinism.vera").result
    assert result.ok, result.diagnostics
    assert [_drive(result) for _ in range(2)] == [(200, _expected_transcript())] * 2


@_needs_wasmtime_cli
def test_the_server_world_answers_alike_under_any_key(tmp_path: Path) -> None:
    result = pipeline.compile(_determinism_program(handler=True), file="determinism.vera").result
    assert result.ok, result.diagnostics
    answers = [_served(result, tmp_path / str(i)) for i in range(2)]
    assert answers == [(200, _expected_transcript())] * 2


#: A JSON text's members and an element's attributes, neither in sorted
#: order, a member given twice and an attribute inserted again, written
#: back by `json_stringify` and `html_to_string`, which read the map
#: through the module's `map_keys$ks` and `map_values$v*`.  The element is
#: built, not parsed: the Node harness has no `DOMParser`.
_HOST_READERS = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Map<String, String> = map_insert(map_insert(map_insert(map_insert(map_new(), "pear", "1"), "apple", "2"), "kiwi", "3"), "pear", "4");
  let @Map<String, String> = map_new();
  let @HtmlNode = HtmlElement("div", @Map<String, String>.0, [HtmlElement("p", @Map<String, String>.1, [HtmlText("x")])]);
  IO.print(match json_parse("{\\"pear\\": 1, \\"apple\\": 2, \\"kiwi\\": 3, \\"\\": 4, \\"caf\u00e9\\": 5, \\"apple\\": 6}") {
    Ok(@Json) -> json_stringify(@Json.0),
    Err(@String) -> @String.0
  });
  IO.print(" ");
  IO.print(string_join(array_map(html_query(@HtmlNode.0, "p"), fn(@HtmlNode -> @String) effects(pure) { html_to_string(@HtmlNode.0) }), ";"));
  IO.print("\\n")
}
"""

#: What the base (c9235415) printed, natively.
_HOST_READERS_OUT = '{"pear":1,"apple":6,"kiwi":3,"":4,"caf\u00e9":5} <p pear="4" apple="2" kiwi="3">x</p>\n'


def test_the_hosts_write_a_map_alike_under_the_native_key() -> None:
    """`json_stringify` of a parsed `JObject` and `html_to_string` of an
    element's attributes print what the base printed, under the two test
    keys and a drawn one."""
    result = pipeline.compile(_HOST_READERS, file="readers.vera").result
    assert result.ok, result.diagnostics
    outs = []
    for words in ([*K1], [*K2], None):
        with _native_key([_signed(w) for w in words] if words else None):
            outs.append(pipeline.run(result).execution.stdout)
    assert outs == [_HOST_READERS_OUT] * 3


@_needs_node
def test_the_browser_writes_a_map_alike_under_any_key(tmp_path: Path) -> None:
    result = pipeline.compile(_HOST_READERS, file="readers.vera").result
    assert result.ok, result.diagnostics
    assert [_in_browser(result, tmp_path / str(i)) for i in range(2)] == [_HOST_READERS_OUT] * 2


#: A handler's response headers, inserted out of order, one inserted
#: again (it keeps its place and takes its new value), one removed, and
#: one inserted last.
_RESPONSE_HEADERS = """\
public fn handle(@Request -> @Response)
  requires(true)
  ensures(true)
  effects(<HttpServer>)
{
  let @Map<String, String> = map_insert(map_insert(map_insert(map_insert(map_new(), "x-pear", "1"), "x-apple", "2"), "x-kiwi", "3"), "x-pear", "4");
  Response(200, map_remove(map_insert(@Map<String, String>.0, "x-date", "5"), "x-apple"), "ok")
}
"""

#: The order the semantics of spec §9.4.3 give them, and the base printed.
_RESPONSE_HEADERS_OUT = [("x-pear", "4"), ("x-kiwi", "3"), ("x-date", "5")]


def test_the_native_server_writes_the_response_headers_alike_under_any_key() -> None:
    from vera.codegen.api import HttpRequestData

    result = pipeline.compile(_RESPONSE_HEADERS, file="headers.vera").result
    assert result.ok, result.diagnostics
    written = []
    for words in ([*K1], [*K2], None):
        with _native_key([_signed(w) for w in words] if words else None):
            ran = pipeline.run(result, "handle", http_request=HttpRequestData(
                method="GET", path="/", headers={}, body=""))
        response = ran.execution.http_response
        assert response is not None
        headers = response["headers"]
        assert isinstance(headers, dict)
        written.append(list(headers.items()))
    assert written == [_RESPONSE_HEADERS_OUT] * 3


@_needs_wasmtime_cli
def test_the_server_world_writes_the_response_headers_alike_under_any_key(
    tmp_path: Path,
) -> None:
    """Under `wasmtime serve` the adapter reads the headers through the
    module's `map_keys$ks` and `map_values$vs`; the host adds its own
    after them."""
    from tests.test_wasi_target import _serve_request, _WasmtimeServe
    from vera.codegen.wasi import emit_wasi_component

    result = pipeline.compile(_RESPONSE_HEADERS, file="headers.vera").result
    assert result.ok, result.diagnostics
    component = emit_wasi_component(result, world="server")
    written = []
    for i in range(2):
        served = tmp_path / str(i)
        served.mkdir()
        with _WasmtimeServe(component, served, flags=("-O", "pooling-allocator=n")) as server:
            status, headers, body = _serve_request(server.port, "GET", "/", [], "")
        assert (status, body) == (200, "ok")
        written.append([(k, v) for k, v in headers.items() if k.startswith("x-")])
    assert written == [_RESPONSE_HEADERS_OUT] * 2


# =====================================================================
# Keys that share a path under one key spread under another
# =====================================================================

#: Eight keys whose SipHash-1-3 under K1 shares its low fifteen bits, so the
#: three first digits of the trie's path (19, 29, 19), found by brute force
#: over ``key-<i>`` with the reference above.  Under K2 their first digits
#: are 17, 18, 15, 29, 16, 28, 15 and 26.
_SHARED_UNDER_K1 = [
    "key-9744", "key-13399", "key-20171", "key-20747",
    "key-25512", "key-28919", "key-29718", "key-29722",
]


def _shared_path_program() -> str:
    lets = ["  let @Map<String, Int> = map_new();"]
    lets += [f"  let @Map<String, Int> = map_insert(@Map<String, Int>.0, {_vera_string(k)}, {i});"
             for i, k in enumerate(_SHARED_UNDER_K1)]
    body = "\n".join(lets)
    return f"""\
public fn main(@Unit -> @Map<String, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{{
{body}
  @Map<String, Int>.0
}}
"""


def test_repro_1736_keys_sharing_a_path_under_one_key_spread_under_another() -> None:
    """A seed folded into the hash after it is computed moves every key by
    the same amount, so keys that collide under one seed collide under
    all; the key must enter the hash.  The eight keys share three digits
    under K1, so the module sits every one at least four branches deep; under
    K2 the same keys sit at most two deep."""
    for key in _SHARED_UNDER_K1:
        assert siphash(*K1, key.encode()) & 0x7FFF == siphash(*K1, b"key-9744") & 0x7FFF
    result = pipeline.compile(_shared_path_program(), file="shared.vera").result
    assert result.ok, result.diagnostics
    depths = {}
    for name, key in (("K1", K1), ("K2", K2)):
        with _native_key([_signed(w) for w in key]):
            header, mem = _run_keyed(result)
        assert isinstance(header, int)
        entries = _entries(mem, header)
        assert len(entries) == len(_SHARED_UNDER_K1)
        depths[name] = sorted(depth for _, _, depth in entries)
    assert min(depths["K1"]) >= 4, depths
    assert max(depths["K2"]) <= 2, depths


# =====================================================================
# The negative space
# =====================================================================

_KEY_TYPES = {
    "Int": "7", "Nat": "7", "Bool": "true", "Byte": "seven(())",
    "Float64": "7.5", "String": '"seven"', "Option<Int>": "Some(7)",
}

_SEVEN = """\
private fn seven(@Unit -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  match int_to_byte(7) { Some(@Byte) -> @Byte.0, None -> 0 }
}

"""


@pytest.mark.parametrize("collection", ["Map", "Set"])
@pytest.mark.parametrize("key", list(_KEY_TYPES))
def test_only_a_string_key_draws_a_key(key: str, collection: str) -> None:
    """A module draws a key exactly when it hashes a `String` in a trie:
    every other representation's hash is a bijection of its word, so no two
    of its keys can share a hash and none needs a key."""
    k = _KEY_TYPES[key]
    if collection == "Map":
        binding = f"let @Map<{key}, Int> = map_insert(map_new(), {k}, 1);"
        use = f"map_size(@Map<{key}, Int>.0)"
    else:
        binding = f"let @Set<{key}> = set_add(set_new(), {k});"
        use = f"set_size(@Set<{key}>.0)"
    source = _SEVEN + f"""\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {binding}
  {use}
}}
"""
    result = pipeline.compile(source, file="keys.vera").result
    assert result.ok, result.diagnostics
    imports = set(re.findall(r'\(import "vera" "([^"]+)"', result.wat))
    assert ("hash_key" in imports) is (key == "String"), imports
    assert ("$hamt$k0" in result.wat) is (key == "String")


_HASH_ABILITY = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(string_join([int_to_string(hash("")), int_to_string(hash("probe")), int_to_string(hash("café ☃")), int_to_string(hash(Some("probe")))], " "));
  IO.print("\\n")
}
"""


def test_the_hash_abilitys_string_hash_is_still_fnv1a() -> None:
    """`hash()` is observable, and spec §9.8.1 promises it is deterministic:
    the key is the trie's alone.  A `String`'s is FNV-1a of its bytes, the
    same in every run, and a composite's folds it in as before."""
    result = pipeline.compile(_HASH_ABILITY, file="hash.vera").result
    assert result.ok, result.diagnostics
    prime = 0x100000001B3
    some = ((((0xCBF29CE484222325 ^ 1) * prime) & _MASK) ^ fnv1a(b"probe")) * prime & _MASK
    want = " ".join(str(_signed(h)) for h in (
        fnv1a(b""), fnv1a(b"probe"), fnv1a("café ☃".encode()), some))
    assert [pipeline.run(result).execution.stdout for _ in range(2)] == [want + "\n"] * 2


_ORDER = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  let @Map<String, Int> = map_insert(map_insert(map_insert(map_insert(map_new(), "pear", 1), "apple", 2), "kiwi", 3), "date", 4);
  let @Map<String, Int> = map_insert(map_remove(map_insert(@Map<String, Int>.0, "apple", 20), "kiwi"), "kiwi", 30);
  let @Set<String> = set_add(set_remove(set_add(set_add(set_add(set_new(), "fig"), "lime"), "fig"), "lime"), "plum");
  let @Map<Int, Int> = map_insert(map_insert(map_insert(map_new(), 99, 1), 3, 2), 42, 3);
  let @Set<Option<Int>> = set_add(set_add(set_new(), Some(1)), Some(1));
  IO.print(string_join(map_keys(@Map<String, Int>.0), ","));
  IO.print(" ");
  IO.print(string_join(array_map(map_values(@Map<String, Int>.0), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ","));
  IO.print(" ");
  IO.print(string_join(set_to_array(@Set<String>.0), ","));
  IO.print(" ");
  IO.print(string_join(array_map(map_keys(@Map<Int, Int>.0), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ","));
  IO.print(" ");
  IO.print(int_to_string(set_size(@Set<Option<Int>>.0)));
  IO.print("\\n")
}
"""


@pytest.mark.parametrize("host", [_probe_param(h) for h in _PROBE_HOSTS])
def test_every_host_enumerates_as_it_did(host: str, tmp_path: Path) -> None:
    """The base's output on every host (measured at c9235415): insertion
    order for `String` and `Int` keys, and #1732's two `Some(1)` keys,
    which compare by address."""
    result = pipeline.compile(_ORDER, file="order.vera").result
    assert result.ok, result.diagnostics
    assert _PROBE_HOSTS[host](result, tmp_path) == "pear,apple,date,kiwi 1,20,4,30 fig,plum 99,3,42 2\n"
