"""`Map` and `Set` as structural persistent collections in generated code (#1676).

A `Map<K, V>` or `Set<T>` lives in the module's own heap and its operations
are the module's own code: no host import implements one, so every host runs
the same instructions over the same blocks, and an insert copies the path it
changes and shares the rest with the collection it came from.

The class is every observable behaviour of the fourteen operations: what each
returns for every key, value and element representation, at every size the
structure's fan-out separates; that a collection an operation was given is
unchanged by it; the order the three enumerations read (insertion order: a
key keeps its first position when it is inserted again and loses it when it
is removed); key equality (SameValueZero for `Float64`, content for `String`);
and that each host and both WASI worlds agree.  The expectation of every
cell is computed by a model of those semantics below (`_Model`), never by a
host: the hosts disagreed before this change (#1729: a `Bool` or `Byte`
array the hosts wrote in four-byte cells; a `Set`'s order).

The unparametrised `repro` tests are the measurements the issue and the
review recorded, each red before the change for the reason it names.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import time
from collections.abc import Callable
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

import pytest
import wasmtime

from tests import pipeline
from vera.builtins import BUILTINS, HOST_IMPORTS
from vera.codegen import CompileResult
from vera.runtime.wasi_host import execute_wasi_p2

# A generated class instrument (tests/matrix_sample.py): a pull request runs
# a sample of its parametrised cells, and every cell when it changes this
# file or a module that decides the class.
pytestmark = pytest.mark.matrix(decides=[
    "vera/wasm/calls_containers.py",
    "vera/builtins.py",
])

ROOT = Path(__file__).resolve().parent.parent
HARNESS = ROOT / "vera" / "browser" / "harness.mjs"
NODE = shutil.which("node")
WASMTIME_CLI = shutil.which("wasmtime")


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
_needs_node = pytest.mark.skipif(
    not _HAS_NODE, reason="Node.js with --experimental-wasm-exnref is not available")
_needs_wasmtime_cli = pytest.mark.skipif(
    WASMTIME_CLI is None, reason="the stock wasmtime CLI (wasmtime serve) is not installed")


# =====================================================================
# Running a program on each host
# =====================================================================

@lru_cache(maxsize=64)
def _compiled(source: str) -> CompileResult:
    """Check and compile *source* once per process."""
    compiled = pipeline.compile(source, file="cell.vera")
    result = compiled.result
    assert result.ok, result.diagnostics
    return result


def _native(result: CompileResult) -> str:
    ran = pipeline.run(result, budget_s=600)
    assert ran.trap is None, ran.trap
    return ran.execution.stdout


def _browser(result: CompileResult, tmp_path: Path) -> str:
    wasm = tmp_path / "cell.wasm"
    wasm.write_bytes(result.wasm_bytes)
    proc = subprocess.run(
        [NODE or "node", "--experimental-wasm-exnref", str(HARNESS), str(wasm)],
        capture_output=True, text=True, encoding="utf-8", timeout=600, check=False)
    assert proc.returncode == 0, proc.stderr
    out = json.loads(proc.stdout)
    assert out.get("error") is None, out["error"]
    return str(out["stdout"])


def _wasi_cli(result: CompileResult) -> str:
    ran = execute_wasi_p2(result)
    assert ran.exit_code in (None, 0), ran.stderr
    return ran.stdout


HOSTS: dict[str, Callable[[CompileResult, Path], str]] = {
    "native": lambda result, _tmp: _native(result),
    "browser": _browser,
    "wasi-cli": lambda result, _tmp: _wasi_cli(result),
}


def _host_param(host: str) -> object:
    return pytest.param(host, marks=_needs_node) if host == "browser" else host


# =====================================================================
# The model: what each operation returns, independent of any host
# =====================================================================

KEY_TYPES = ("Int", "Nat", "Bool", "Byte", "Float64", "String")
VALUE_TYPES = ("Int", "Float64", "String", "Bool", "Option<Int>", "Map<String, Int>")
#: The sizes either side of the 32-way fan-out, one level of it, and two.
SIZES = (0, 1, 2, 31, 32, 33, 1024, 10000)
#: The distinct values a key type has, where it has fewer than the sizes.
DOMAIN = {"Bool": 2, "Byte": 256}


def _key(key: str, i: int) -> object:
    """Key number *i* as the model compares it (distinct for every i below
    the type's domain)."""
    return {
        "Int": lambda: i * 7919 - 31337,
        "Nat": lambda: i * 7919 + 3,
        "Bool": lambda: i % 2 == 0,
        "Byte": lambda: (i * 37) % 256,
        "Float64": lambda: i * 0.5 - 7.25,
        "String": lambda: f"k{i * 7919}",
    }[key]()


def _show_key(key: str, k: object) -> str:
    if key == "Bool":
        return "true" if k else "false"
    if key == "Float64":
        assert isinstance(k, float)
        return str(int(k * 4))
    return str(k)


def _show_value(value: str, i: int, gen: int) -> str:
    """Value number *i* of generation *gen*, as the program renders it."""
    n = i + gen
    if value == "Int":
        return str(i * 3 + gen * 1000003)
    if value == "Float64":
        return str(n * 4 + 1)
    if value == "String":
        return f"v{i}_{gen}"
    if value == "Bool":
        return "true" if n % 3 == 0 else "false"
    if value == "Option<Int>":
        return f"S{n}" if n % 2 == 0 else "N"
    assert value == "Map<String, Int>"
    return f"x{i}={n}"


@dataclass
class _Model:
    """An insertion-ordered map (a set is a map whose values are absent)."""

    entries: dict[object, str]

    def insert(self, k: object, v: str) -> _Model:
        out = dict(self.entries)
        out[k] = v  # a present key keeps its position
        return _Model(out)

    def remove(self, k: object) -> _Model:
        out = dict(self.entries)
        out.pop(k, None)
        return _Model(out)

    def add(self, k: object) -> _Model:
        if k in self.entries:
            return self
        return self.insert(k, "")


def _stage(tag: str, key: str, m: _Model, with_values: bool) -> str:
    keys = ",".join(_show_key(key, k) for k in m.entries)
    if not with_values:
        return f"{tag} {len(m.entries)} [{keys}]\n"
    values = ",".join(m.entries.values())
    return f"{tag} {len(m.entries)} [{keys}] [{values}]\n"


def expected_transcript(key: str, value: str | None, n: int) -> str:
    """What the cell program prints: *value* None is a `Set<key>`."""
    k = [_key(key, i) for i in range(n + 6)]
    every_third = [i for i in range(n) if i % 3 == 0]
    evens = [i for i in range(n) if i % 2 == 0]
    if value is None:
        s1 = _Model({})
        for i in range(n):
            s1 = s1.add(k[i])
        s2 = s1
        for i in every_third:
            s2 = s2.add(k[i])
        s3 = s2
        for i in evens:
            s3 = s3.remove(k[i])
        s4 = s3
        for i in reversed(evens):
            s4 = s4.add(k[i])
        probes = range(n + 2)
        lines = [
            _stage("A", key, s1, False),
            "C " + ",".join("true" if k[i] in s1.entries else "false" for i in probes) + "\n",
            _stage("B", key, s2, False),
            _stage("R", key, s3, False),
            _stage("I", key, s4, False),
            _stage("P", key, s1, False),
            _stage("Q", key, s4.remove(k[n + 5]), False),
        ]
        return "".join(lines)
    m1 = _Model({})
    for i in range(n):
        m1 = m1.insert(k[i], _show_value(value, i, 0))
    m2 = m1
    for i in every_third:
        m2 = m2.insert(k[i], _show_value(value, i, 1))
    m3 = m2
    for i in evens:
        m3 = m3.remove(k[i])
    m4 = m3
    for i in reversed(evens):
        m4 = m4.insert(k[i], _show_value(value, i, 2))
    probes = range(n + 2)
    gets = ",".join(
        f"+{m1.entries[k[i]]}" if k[i] in m1.entries else "-" for i in probes)
    has = ",".join("true" if k[i] in m1.entries else "false" for i in probes)
    lines = [
        _stage("A", key, m1, True),
        f"G {gets}\nC {has}\n",
        _stage("B", key, m2, True),
        _stage("R", key, m3, True),
        _stage("I", key, m4, True),
        _stage("P", key, m1, True),
        _stage("Q", key, m4.remove(k[n + 5]), True),
    ]
    return "".join(lines)


# =====================================================================
# The cell programs
# =====================================================================

_PURE = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

_KEY_OF = {
    "Int": "@Int.0 * 7919 - 31337",
    "Nat": "abs(@Int.0 * 7919 + 3)",
    "Bool": "@Int.0 % 2 == 0",
    "Byte": "match int_to_byte((@Int.0 * 37) % 256) { Some(@Byte) -> @Byte.0, None -> 0 }",
    "Float64": "int_to_float(@Int.0) * 0.5 - 7.25",
    "String": 'string_concat("k", int_to_string(@Int.0 * 7919))',
}

_SHOW = {
    "Int": "int_to_string(@Int.0)",
    "Nat": "nat_to_string(@Nat.0)",
    "Bool": "bool_to_string(@Bool.0)",
    "Byte": "int_to_string(byte_to_int(@Byte.0))",
    "Float64": "int_to_string(float_to_int(@Float64.0 * 4.0))",
    "String": "@String.0",
    "Option<Int>": (
        'match @Option<Int>.0 { Some(@Int) -> string_concat("S", int_to_string(@Int.0)),'
        ' None -> "N" }'),
    "Map<String, Int>": (
        'string_concat(string_join(map_keys(@Map<String, Int>.0), ";"), string_concat("=",'
        " string_join(array_map(map_values(@Map<String, Int>.0), fn(@Int -> @String)"
        ' effects(pure) { int_to_string(@Int.0) }), ";")))'),
}

#: Value number `@Int.1` of generation `@Int.0`.
_VAL_OF = {
    "Int": "@Int.1 * 3 + @Int.0 * 1000003",
    "Float64": "int_to_float(@Int.1 + @Int.0) + 0.25",
    "String": (
        'string_concat(string_concat("v", int_to_string(@Int.1)),'
        ' string_concat("_", int_to_string(@Int.0)))'),
    "Bool": "(@Int.1 + @Int.0) % 3 == 0",
    "Option<Int>": "if (@Int.1 + @Int.0) % 2 == 0 then { Some(@Int.1 + @Int.0) } else { None }",
    "Map<String, Int>": (
        'map_insert(map_new(), string_concat("x", int_to_string(@Int.1)), @Int.1 + @Int.0)'),
}


def _join(t: str, expr: str) -> str:
    """`expr` (an `Array<t>`) rendered as its elements joined by commas."""
    return (f"string_join(array_map({expr}, fn(@{t} -> @String) effects(pure)"
            f" {{ show_{_ident(t)}(@{t}.0) }}), \",\")")


def _ident(t: str) -> str:
    return re.sub(r"\W+", "_", t).strip("_")


def _shows(types: list[str]) -> str:
    out = []
    for t in dict.fromkeys(types):
        out.append(f"private fn show_{_ident(t)}(@{t} -> @String)\n{_PURE}{{\n  {_SHOW[t]}\n}}\n")
    return "\n".join(out)


def cell_program(key: str, value: str | None, n: int, *, server: bool = False) -> str:
    """The program whose output `expected_transcript` predicts.

    `main` prints `transcript(())`; with *server*, `handle` returns it as
    the response body instead.
    """
    coll = f"Map<{key}, {value}>" if value is not None else f"Set<{key}>"
    ins = "map_insert" if value is not None else "set_add"
    rem = "map_remove" if value is not None else "set_remove"
    has = "map_contains" if value is not None else "set_contains"

    def with_value(gen: int) -> str:
        return f", val_of(@Int.0, {gen})" if value is not None else ""

    def fold(indices: str, op: str, gen: int | None) -> str:
        arg = with_value(gen) if gen is not None else ""
        return (f"array_fold({indices}, @{coll}.0, fn(@{coll}, @Int -> @{coll})"
                f" effects(pure) {{ {op}(@{coll}.0, key_of(@Int.0){arg}) }})")

    every_third = (f"array_filter(array_range(0, {n}), fn(@Int -> @Bool) effects(pure)"
                   " { @Int.0 % 3 == 0 })")
    evens = (f"array_filter(array_range(0, {n}), fn(@Int -> @Bool) effects(pure)"
             " { @Int.0 % 2 == 0 })")
    parts = [f"private fn key_of(@Int -> @{key})\n{_PURE}{{\n  {_KEY_OF[key]}\n}}\n"]
    shows = [key]
    if value is not None:
        parts.append(
            f"private fn val_of(@Int, @Int -> @{value})\n{_PURE}{{\n  {_VAL_OF[value]}\n}}\n")
        shows.append(value)
        parts.append(
            f"private fn show_get(@Option<{value}> -> @String)\n{_PURE}{{\n"
            f"  match @Option<{value}>.0 {{ Some(@{value}) -> string_concat(\"+\","
            f" show_{_ident(value)}(@{value}.0)), None -> \"-\" }}\n}}\n")
        values_part = (f'string_concat("] [", string_concat({_join(value, f"map_values(@{coll}.0)")},'
                       ' "]\\n"))')
        stage_body = (
            f"string_concat(@String.0, string_concat(\" \", string_concat("
            f"int_to_string(map_size(@{coll}.0)), string_concat(\" [\", string_concat("
            f"{_join(key, f'map_keys(@{coll}.0)')}, {values_part})))))")
        probes = (
            f"private fn probes(@{coll} -> @String)\n{_PURE}{{\n"
            f"  string_concat(\"G \", string_concat(string_join(array_map(array_range(0, {n + 2}),"
            f" fn(@Int -> @String) effects(pure) {{ show_get(map_get(@{coll}.0, key_of(@Int.0))) }}),"
            f" \",\"), string_concat(\"\\nC \", string_concat(string_join(array_map("
            f"array_range(0, {n + 2}), fn(@Int -> @String) effects(pure) {{ bool_to_string("
            f"{has}(@{coll}.0, key_of(@Int.0))) }}), \",\"), \"\\n\"))))\n}}\n")
    else:
        stage_body = (
            f"string_concat(@String.0, string_concat(\" \", string_concat("
            f"int_to_string(set_size(@{coll}.0)), string_concat(\" [\", string_concat("
            f"{_join(key, f'set_to_array(@{coll}.0)')}, \"]\\n\")))))")
        probes = (
            f"private fn probes(@{coll} -> @String)\n{_PURE}{{\n"
            f"  string_concat(\"C \", string_concat(string_join(array_map(array_range(0, {n + 2}),"
            f" fn(@Int -> @String) effects(pure) {{ bool_to_string({has}(@{coll}.0, key_of(@Int.0))) }}),"
            f" \",\"), \"\\n\"))\n}}\n")
    parts.append(_shows(shows))
    parts.append(f"private fn stage(@String, @{coll} -> @String)\n{_PURE}{{\n  {stage_body}\n}}\n")
    parts.append(probes)
    new = "map_new()" if value is not None else "set_new()"
    parts.append(
        f"private fn transcript(@Unit -> @String)\n{_PURE}{{\n"
        f"  let @{coll} = {new};\n"
        f"  let @{coll} = {fold(f'array_range(0, {n})', ins, 0)};\n"
        f"  let @{coll} = {fold(every_third, ins, 1)};\n"
        f"  let @{coll} = {fold(evens, rem, None)};\n"
        f"  let @{coll} = {fold(f'array_reverse({evens})', ins, 2)};\n"
        f"  string_concat(stage(\"A\", @{coll}.3), string_concat(probes(@{coll}.3),"
        f" string_concat(stage(\"B\", @{coll}.2), string_concat(stage(\"R\", @{coll}.1),"
        f" string_concat(stage(\"I\", @{coll}.0), string_concat(stage(\"P\", @{coll}.3),"
        f" stage(\"Q\", {rem}(@{coll}.0, key_of({n + 5})))))))))\n}}\n")
    if server:
        parts.append(
            "public fn handle(@Request -> @Response)\n  requires(true)\n  ensures(true)\n"
            "  effects(<HttpServer>)\n{\n  Response(200, map_new(), transcript(()))\n}\n")
    else:
        parts.append(
            "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
            "  effects(<IO>)\n{\n  IO.print(transcript(()))\n}\n")
    return "\n".join(parts)


def _cells() -> list[tuple[str, str | None, int]]:
    cells = []
    for key in KEY_TYPES:
        sizes = [n for n in SIZES if n <= DOMAIN.get(key, n)]
        if key in DOMAIN and DOMAIN[key] not in sizes:
            sizes.append(DOMAIN[key])
        for value in (*VALUE_TYPES, None):
            for n in sizes:
                cells.append((key, value, n))
    return cells


CELLS = _cells()


def _cell_id(cell: tuple[str, str | None, int]) -> str:
    key, value, n = cell
    shape = f"Map<{key},{value}>" if value is not None else f"Set<{key}>"
    return f"{_ident(shape)}-{n}"


@pytest.mark.parametrize("host", [_host_param(h) for h in HOSTS])
@pytest.mark.parametrize("cell", CELLS, ids=[_cell_id(c) for c in CELLS])
def test_every_operation_returns_what_the_model_says(
    cell: tuple[str, str | None, int], host: str, tmp_path: Path,
) -> None:
    """Each operation, at each key, value and element representation and
    size, on each host: the program's transcript is the model's."""
    key, value, n = cell
    result = _compiled(cell_program(key, value, n))
    assert HOSTS[host](result, tmp_path) == expected_transcript(key, value, n)


# =====================================================================
# The measurements the issue and the review recorded
# =====================================================================

#: The issue's fold, as `TestHostHandleReclamation573` writes it.
def _issue_fold(n: int) -> str:
    return f"""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(
    array_range(1, {n + 1}),
    @Map<Int, Int>.0,
    fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) {{
      map_insert(@Map<Int, Int>.0, @Int.0, @Int.0)
    }}
  );
  match map_get(@Map<Int, Int>.0, {n // 2}) {{
    Some(@Int) -> @Int.0,
    None -> -1
  }}
}}
"""


def _timed_fold(n: int) -> float:
    """Seconds `main` of the issue's fold over *n* keys takes to run,
    compilation excluded, with its value checked."""
    result = _compiled(_issue_fold(n))
    started = time.perf_counter()
    ran = pipeline.run(result, budget_s=600)
    elapsed = time.perf_counter() - started
    assert ran.trap is None, ran.trap
    assert ran.execution.value == n // 2
    return elapsed


@pytest.mark.stress
@pytest.mark.budget(600)
def test_repro_1676_the_issue_fold_takes_under_a_second() -> None:
    """The acceptance test the decision named: 10,000 inserts, measured at
    48 to 94 s when the issue was opened and 50.4 s at c1fc89b2."""
    assert _timed_fold(10_000) < 1.0


@pytest.mark.stress
@pytest.mark.budget(600)
def test_repro_1676_a_hundred_thousand_inserts_take_under_ten_seconds() -> None:
    assert _timed_fold(100_000) < 10.0


@pytest.mark.stress
@pytest.mark.budget(600)
@pytest.mark.xfail(strict=True, reason=(
    "the allocator, not the trie: from 10,000 to 100,000 inserts the "
    "allocations per insert go 5.0 to 5.7 while the first-fit free-list "
    "steps per allocation go 35 to 98, the collections 37 to 160 and the "
    "heap 38 to 478 pages; measured 48.8 times as long"))
def test_repro_1676_ten_times_the_inserts_take_at_most_fifteen_times_as_long() -> None:
    """An insert's cost grows with the depth of the trie, not with the map:
    a cost that grew with the map would take a hundred times as long."""
    small = min(_timed_fold(10_000) for _ in range(3))
    large = _timed_fold(100_000)
    assert large <= 15 * small, (small, large)


#: Issue #1729's program: a `Set<Byte>` and a `Map<Bool, Int>` enumerated
#: into the arrays generated code reads one byte per element of.
_ONE_BYTE_ARRAYS = """\
private fn b(@Byte -> @Byte)
  requires(true) ensures(@Byte.result == @Byte.0) effects(pure)
{
  @Byte.0
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Byte> = set_to_array(set_add(set_add(set_add(set_new(), b(7)), b(200)), b(3)));
  IO.print(string_join(array_map(@Array<Byte>.0, fn(@Byte -> @String) effects(pure) { int_to_string(byte_to_int(@Byte.0)) }), " "));
  IO.print(" | ");
  let @Array<Bool> = map_keys(map_insert(map_insert(map_new(), false, 1), true, 2));
  IO.print(string_join(array_map(@Array<Bool>.0, fn(@Bool -> @String) effects(pure) { bool_to_string(@Bool.0) }), " "));
  IO.print(" | ");
  let @Array<Bool> = map_values(map_insert(map_insert(map_new(), "a", false), "b", true));
  IO.print(string_join(array_map(@Array<Bool>.0, fn(@Bool -> @String) effects(pure) { bool_to_string(@Bool.0) }), " "));
  IO.print("\\n")
}
"""


@pytest.mark.parametrize("host", [_host_param(h) for h in HOSTS])
def test_repro_1729_a_bool_or_byte_array_holds_what_went_in(
    host: str, tmp_path: Path,
) -> None:
    """At c1fc89b2 the hosts wrote these arrays in four-byte cells, and the
    program printed `200 0 0 | false false | false false` natively."""
    out = HOSTS[host](_compiled(_ONE_BYTE_ARRAYS), tmp_path)
    assert out == "7 200 3 | false true | false true\n"


_SET_ORDER = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Set<String> = set_add(set_add(set_add(set_add(set_add(set_new(), "pear"), "apple"), "fig"), "kiwi"), "date");
  let @Set<String> = set_add(set_remove(set_add(@Set<String>.0, "pear"), "fig"), "fig");
  let @Set<Int> = set_add(set_add(set_add(set_add(set_new(), 40), 3), 17), 9);
  IO.print(string_join(set_to_array(@Set<String>.0), ","));
  IO.print(" ");
  IO.print(string_join(array_map(set_to_array(@Set<Int>.0), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ","));
  IO.print("\\n")
}
"""


@pytest.mark.parametrize("host", [_host_param(h) for h in HOSTS])
def test_repro_a_set_iterates_in_insertion_order(host: str, tmp_path: Path) -> None:
    """At c1fc89b2 the native host enumerated a set in Python's set order:
    a `Set<String>` differently on every run, a `Set<Int>` as 40,17,3,9."""
    out = HOSTS[host](_compiled(_SET_ORDER), tmp_path)
    assert out == "pear,apple,kiwi,date,fig 40,3,17,9\n"


_FLOAT_KEYS = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Float64 = 0.0 * -1.0;
  let @Map<Float64, Int> = map_insert(map_insert(map_new(), @Float64.0, 1), 0.0, 2);
  IO.print(int_to_string(map_size(@Map<Float64, Int>.0)));
  IO.print(" ");
  IO.print(string_join(array_map(map_keys(@Map<Float64, Int>.0), fn(@Float64 -> @String) effects(pure) { float_to_string(1.0 / @Float64.0) }), ","));
  IO.print(" ");
  let @Map<Float64, Int> = map_insert(map_insert(map_insert(map_new(), nan(), 1), 1.0, 2), 0.0 / 0.0, 3);
  IO.print(int_to_string(map_size(@Map<Float64, Int>.0)));
  IO.print(" ");
  IO.print(string_join(array_map(map_keys(@Map<Float64, Int>.0), fn(@Float64 -> @String) effects(pure) { float_to_string(@Float64.0) }), ","));
  IO.print(" ");
  IO.print(string_join(array_map(map_values(@Map<Float64, Int>.0), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ","));
  IO.print(" ");
  let @Set<Float64> = set_add(set_add(set_add(set_new(), nan()), 0.0 * -1.0), 0.0);
  IO.print(int_to_string(set_size(@Set<Float64>.0)));
  IO.print(" ");
  IO.print(bool_to_string(set_contains(@Set<Float64>.0, 0.0)));
  IO.print(bool_to_string(set_contains(@Set<Float64>.0, 0.0 / 0.0)));
  IO.print("\\n")
}
"""


@pytest.mark.parametrize("host", [_host_param(h) for h in HOSTS])
def test_repro_a_float64_key_is_canonical_and_keeps_its_position(
    host: str, tmp_path: Path,
) -> None:
    """SameValueZero: -0.0 and 0.0 are one key, and every NaN is one key.
    The key is stored canonically, so a -0.0 inserted first reads back as
    0.0 (at c1fc89b2 the native host read back -0.0, `1.0 / k` = -inf), and
    a NaN inserted again keeps its first position (at c1fc89b2 the native
    host moved it to the end: `1.0,nan`, values `2,3`)."""
    out = HOSTS[host](_compiled(_FLOAT_KEYS), tmp_path)
    assert out == "1 inf 2 nan,1.0 3,2 2 truetrue\n"


def _module_imports(result: CompileResult) -> set[str]:
    return set(re.findall(r'\(import "vera" "([^"]+)"', result.wat))


def _every_operation_program() -> str:
    """Every one of the fourteen operations at every key, value and
    element representation the matrix crosses."""
    calls: list[str] = []
    for key in KEY_TYPES:
        k = f"key_{_ident(key)}(1)"
        calls.append(f"set_size(set_remove(set_add(set_new(), {k}), {k}))")
        calls.append(f"array_length(set_to_array(set_add(set_new(), {k})))")
        calls.append(f"(if set_contains(set_new(), {k}) then {{ 1 }} else {{ 0 }})")
        for value in VALUE_TYPES:
            v = f"val_{_ident(value)}(1)"
            m = f"map_insert(map_new(), {k}, {v})"
            calls.append(f"map_size(map_remove({m}, {k}))")
            calls.append(f"array_length(map_keys({m})) + array_length(map_values({m}))")
            calls.append(f"(if map_contains({m}, {k}) then {{ 1 }} else {{ 0 }})")
            calls.append(
                f"(match map_get({m}, {k}) {{ Some(@{value}) -> 1, None -> 0 }})")
    fns = []
    for key in KEY_TYPES:
        fns.append(f"private fn key_{_ident(key)}(@Int -> @{key})\n{_PURE}{{\n  {_KEY_OF[key]}\n}}\n")
    for value in VALUE_TYPES:
        body = _VAL_OF[value].replace("@Int.1", "@Int.0").replace("@Int.0 + @Int.0", "@Int.0")
        fns.append(f"private fn val_{_ident(value)}(@Int -> @{value})\n{_PURE}{{\n  {body}\n}}\n")
    total = " + ".join(calls)
    fns.append(f"public fn main(@Unit -> @Int)\n{_PURE}{{\n  {total}\n}}\n")
    return "\n".join(fns)


def test_repro_no_module_declares_a_map_or_set_host_import() -> None:
    """The operations are the module's own code at every instance: at
    c1fc89b2 this program declared 69 `map_*` and `set_*` imports."""
    imports = _module_imports(_compiled(_every_operation_program()))
    hosted = sorted(n for n in imports if n.startswith(("map_", "set_")))
    assert hosted == []


def test_repro_the_registry_has_no_map_or_set_host_row() -> None:
    rows = [row.name for row in HOST_IMPORTS if row.family in ("map", "set")]
    assert rows == []


def test_the_fourteen_names_keep_their_records() -> None:
    """`vera builtins --json` lists the same names with the same `since`."""
    names = {
        "map_new": "0.0.94", "map_insert": "0.0.94", "map_get": "0.0.94",
        "map_contains": "0.0.94", "map_remove": "0.0.94", "map_size": "0.0.94",
        "map_keys": "0.0.94", "map_values": "0.0.94",
        "set_new": "0.0.95", "set_add": "0.0.95", "set_contains": "0.0.95",
        "set_remove": "0.0.95", "set_size": "0.0.95", "set_to_array": "0.0.95",
    }
    assert {name: BUILTINS[name].since for name in names} == names


_CLI_WORLD = """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<Int, Int> = map_insert(map_insert(map_new(), 5, 50), 2, 20);
  let @Map<String, String> = map_insert(map_new(), "k", "v");
  let @Set<Int> = set_add(set_add(set_new(), 9), 9);
  let @Set<String> = set_remove(set_add(set_add(set_new(), "a"), "b"), "a");
  IO.print(int_to_string(map_size(@Map<Int, Int>.0)));
  IO.print(option_unwrap_or(map_get(@Map<String, String>.0, "k"), "-"));
  IO.print(int_to_string(set_size(@Set<Int>.0)));
  IO.print(string_join(set_to_array(@Set<String>.0), ","));
  IO.print("\\n")
}
"""


def test_repro_maps_and_sets_of_every_instance_run_in_the_cli_world() -> None:
    """At c1fc89b2 the cli world refused every `Map` and `Set` program,
    naming the family (`map (map_insert$ki_vi, ...)`, `set (...)`)."""
    result = _compiled(_CLI_WORLD)
    assert _wasi_cli(result) == _native(result) == "2v1b\n"


_SERVER_WORLD = """\
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  let @Map<Int, Int> = map_insert(map_insert(map_new(), 5, 50), 2, 20);
  let @Set<String> = set_add(set_add(set_new(), "a"), "b");
  Response(200, map_insert(map_new(), "content-type", "text/plain"),
    string_concat(int_to_string(map_size(@Map<Int, Int>.0)),
      string_join(set_to_array(@Set<String>.0), ",")))
}
"""


def test_repro_maps_and_sets_of_every_instance_compile_for_the_server_world() -> None:
    """At c1fc89b2 the server world refused a `Map` at any instance but
    `Map<String, String>` (`supports Map host ops only at the
    Map<String, String> instantiation`) and every `Set` (`set (...)`)."""
    from wasmtime.component import Component

    from vera.codegen.wasi import emit_wasi_component

    component = emit_wasi_component(_compiled(_SERVER_WORLD), world="server")
    Component(wasmtime.Engine(), component)


def _counted_bytes(result: CompileResult) -> int:
    """The bytes `$alloc` hands out while `main` runs a pure program."""
    wat = result.wat
    anchor = "  (global $gc_free_head"
    assert wat.count(anchor) == 1
    wat = wat.replace(
        anchor, '  (global $alloc_bytes (export "alloc_bytes") (mut i32) (i32.const 0))\n' + anchor)
    head = re.search(r"  \(func \$alloc \(param \$size i32\) \(result i32\)\n(    \(local [^\n]*\n)+", wat)
    assert head is not None
    count = ("    global.get $alloc_bytes\n    local.get $size\n    i32.add\n"
             "    global.set $alloc_bytes\n")
    wat = wat[:head.end()] + count + wat[head.end():]
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    module = wasmtime.Module(engine, wat)
    linker = wasmtime.Linker(engine)
    for imported in module.imports:
        def refuse(*args: object, _name: str = imported.name) -> None:
            raise AssertionError(f"the module called the host import {_name} {args}")
        assert isinstance(imported.type, wasmtime.FuncType), imported.name
        linker.define_func(imported.module, imported.name, imported.type, refuse)
    exports = linker.instantiate(store, module).exports(store)
    main = exports["main"]
    assert isinstance(main, wasmtime.Func)
    main(store, *([0] if main.type(store).params else []))
    value = exports["alloc_bytes"].value(store)
    assert isinstance(value, int)
    return value


def _one_more_insert(n: int, extra: bool) -> str:
    last = f"map_insert(@Map<Int, Int>.0, {n}, 0)" if extra else "@Map<Int, Int>.0"
    return f"""\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(array_range(0, {n}), @Map<Int, Int>.0,
    fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) {{ map_insert(@Map<Int, Int>.0, @Int.0, @Int.0) }});
  map_size({last})
}}
"""


#: What one insert may allocate: a header and an entry, and a copy of each
#: node on its path, at most thirteen branches of 32 children and a
#: collision node, each block with its header and its alignment.
INSERT_BYTES_BOUND = 16 + 32 + 13 * (8 + 4 * 32) + 64 + 15 * 8


@pytest.mark.parametrize("n", [
    1024, pytest.param(10_000, marks=pytest.mark.stress)])
def test_repro_one_insert_allocates_a_path_not_a_map(n: int) -> None:
    """At c1fc89b2 the operation was a host import, which re-encoded the
    whole bucket: a 1,024-key map's insert wrote a 2,048-slot bucket."""
    extra = _counted_bytes(_compiled(_one_more_insert(n, True)))
    base = _counted_bytes(_compiled(_one_more_insert(n, False)))
    assert 0 < extra - base <= INSERT_BYTES_BOUND, (extra, base)


def _wide_object(n: int) -> str:
    return f"""\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{{
  let @Array<String> = array_map(array_range(0, {n}), fn(@Int -> @String) effects(pure) {{
    string_concat(string_concat("\\"k", int_to_string(@Int.0)), string_concat("\\":", int_to_string(@Int.0)))
  }});
  match json_parse(string_concat(string_concat("{{", string_join(@Array<String>.0, ",")), "}}")) {{
    Ok(@Json) -> {{
      IO.print(int_to_string(array_length(json_keys(@Json.0))));
      IO.print(" ");
      IO.print(int_to_string(string_length(json_stringify(@Json.0))))
    }},
    Err(@String) -> IO.print(@String.0)
  }};
  IO.print("\\n")
}}
"""


@pytest.mark.parametrize("host", [h for h in ("native", "browser")])
def test_repro_json_parse_builds_a_10000_member_object(host: str, tmp_path: Path) -> None:
    """At c1fc89b2 the host rooted every member's value while it built the
    object's map, and a 4,100-member object overflowed the shadow stack
    (`#692: host shadow-stack overflow`; the browser's
    `GC shadow stack overflow`): the widest that parsed had 4,090."""
    if host == "browser" and not _HAS_NODE:
        pytest.skip("Node.js with --experimental-wasm-exnref is not available")
    out = HOSTS[host](_compiled(_wide_object(10_000)), tmp_path)
    assert out == "10000 127781\n"


# =====================================================================
# The server world: the same transcripts as a request handler's body
# =====================================================================

def _serve(result: CompileResult, tmp_path: Path,
           headers: list[tuple[str, str]] | None = None) -> tuple[int, str]:
    """The status and body `wasmtime serve` answers one GET with."""
    from tests.test_wasi_target import _serve_request, _WasmtimeServe
    from vera.codegen.wasi import emit_wasi_component

    component = emit_wasi_component(result, world="server")
    # The module's closures need a function table beside the dispatch
    # table, and `wasmtime serve`'s pooling allocator admits one table
    # per instance (an out-of-scope limit: the PR body names it).
    with _WasmtimeServe(component, tmp_path,
                        flags=("-O", "pooling-allocator=n")) as server:
        status, _, body = _serve_request(server.port, "GET", "/", headers or [], "")
    return status, body


def _drive(result: CompileResult, headers: list[tuple[str, str]] | None = None) -> tuple[int, str]:
    """The status and body the native `vera serve` driver answers with."""
    from vera.codegen.api import HttpRequestData

    merged: dict[str, str] = {}
    for key, value in headers or []:
        merged[key.lower()] = value
    ran = pipeline.run(result, "handle", http_request=HttpRequestData(
        method="GET", path="/", headers=merged, body=""))
    assert ran.trap is None, ran.trap
    response = ran.execution.http_response
    assert response is not None
    return int(str(response["status"])), str(response["body"])


SERVER_CELLS = [
    (key, value, 33 if key not in DOMAIN else DOMAIN[key])
    for key in KEY_TYPES for value in ("Int", "String", None)]


@_needs_wasmtime_cli
@pytest.mark.parametrize("cell", SERVER_CELLS, ids=[_cell_id(c) for c in SERVER_CELLS])
def test_every_operation_serves_what_the_model_says(
    cell: tuple[str, str | None, int], tmp_path: Path,
) -> None:
    """At c1fc89b2 the server world built only `Map<String, String>`."""
    key, value, n = cell
    result = _compiled(cell_program(key, value, n, server=True))
    assert _serve(result, tmp_path) == (200, expected_transcript(key, value, n))


@pytest.mark.parametrize("cell", SERVER_CELLS, ids=[_cell_id(c) for c in SERVER_CELLS])
def test_the_native_server_drives_what_the_model_says(
    cell: tuple[str, str | None, int],
) -> None:
    key, value, n = cell
    result = _compiled(cell_program(key, value, n, server=True))
    assert _drive(result) == (200, expected_transcript(key, value, n))


_HEADER_ECHO = """\
private fn echo(@Map<String, String> -> @String)
  requires(true) ensures(true) effects(pure)
{
  string_join(array_map(array_filter(map_keys(@Map<String, String>.0), fn(@String -> @Bool) effects(pure) { string_starts_with(@String.0, "x-") }), fn(@String -> @String) effects(pure) { string_concat(@String.0, string_concat("=", option_unwrap_or(map_get(@Map<String, String>.0, @String.0), "?"))) }), ",")
}

public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) -> Response(200, map_new(), echo(@Map<String, String>.0))
  }
}
"""

#: A repeated header keeps its first position and its last value, as a
#: `Map` keeps a key inserted again.
_REQUEST_HEADERS = [("X-B", "1"), ("x-a", "2"), ("X-B", "3"), ("X-C", "4")]


def test_the_native_server_builds_the_request_headers_in_order() -> None:
    assert _drive(_compiled(_HEADER_ECHO), _REQUEST_HEADERS) == (200, "x-b=3,x-a=2,x-c=4")


@_needs_wasmtime_cli
def test_the_server_world_builds_the_request_headers_in_order(tmp_path: Path) -> None:
    status, body = _serve(_compiled(_HEADER_ECHO), tmp_path, _REQUEST_HEADERS)
    assert (status, body) == (200, "x-b=3,x-a=2,x-c=4")


# =====================================================================
# The mechanism, one named test per part (every pull request runs them)
# =====================================================================

def _run_pure(result: CompileResult) -> tuple[object, bytes]:
    """`main`'s value and the module's memory after a pure program runs."""
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    module = wasmtime.Module(engine, result.wat)
    linker = wasmtime.Linker(engine)
    for imported in module.imports:
        def refuse(*args: object, _name: str = imported.name) -> None:
            raise AssertionError(f"the module called the host import {_name} {args}")
        assert isinstance(imported.type, wasmtime.FuncType), imported.name
        linker.define_func(imported.module, imported.name, imported.type, refuse)
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


def _trie(mem: bytes, header: int) -> tuple[int, list[str]]:
    """The entries the trie under *header* holds, and every way it breaks
    the documented layout (``vera/wasm/hamt.py``): a branch below the root
    that is empty or holds one entry and nothing else, a collision node of
    fewer than two entries or not below the last branch, an entry its
    hash's digits do not lead to, or a count the header does not hold."""
    from vera.wasm.hamt import LAST_SHIFT

    broken: list[str] = []
    entries = 0

    def walk(node: int, shift: int, path: list[int]) -> None:
        nonlocal entries
        if shift > LAST_SHIFT:
            n = _i32(mem, node)
            if n < 2:
                broken.append(f"collision node {node} holds {n}")
            for i in range(n):
                entries += 1
                check(_i32(mem, node + 4 + 4 * i), path)
            return
        dm, nm = _i32(mem, node), _i32(mem, node + 4)
        if dm & nm:
            broken.append(f"branch {node}: a digit is both an entry and a node")
        ne, nn = bin(dm).count("1"), bin(nm).count("1")
        if path and ne + nn == 0:
            broken.append(f"empty branch {node} below the root")
        if path and nn == 0 and ne == 1:
            broken.append(f"branch {node} below the root holds one entry")
        digits = [d for d in range(32) if dm >> d & 1]
        for i, d in enumerate(digits):
            entries += 1
            check(_i32(mem, node + 8 + 4 * i), [*path, d])
        for j, d in enumerate(d for d in range(32) if nm >> d & 1):
            walk(_i32(mem, node + 8 + 4 * (ne + j)), shift + 5, [*path, d])

    def check(entry: int, path: list[int]) -> None:
        h = _i64(mem, entry)
        want = [(h >> (5 * level)) & 31 for level in range(len(path))]
        if want != path:
            broken.append(f"entry {entry} (hash {h:#x}) sits at {path}")
        if not _i64(mem, entry + 8) & 1:
            broken.append(f"entry {entry}'s insertion number is even")

    root = _i32(mem, header + 4)
    if root:
        walk(root, 0, [])
    if _i32(mem, header) != entries:
        broken.append(f"the header counts {_i32(mem, header)} of {entries} entries")
    return entries, broken


#: Keys that share digits at several levels, so inserts and removes make
#: and collapse branches below the root: 0, 32, 1024 and 32768 all have
#: the low digit 0 of their identity, and the finalizer spreads them; the
#: remove order takes most of them back out.
_CANONICAL = """\
public fn main(@Unit -> @Map<Int, Int>)
  requires(true) ensures(true) effects(pure)
{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(array_range(0, 2000), @Map<Int, Int>.0, fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) { map_insert(@Map<Int, Int>.0, @Int.0 * 32, @Int.0) });
  array_fold(array_range(0, 1990), @Map<Int, Int>.0, fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) { map_remove(@Map<Int, Int>.0, @Int.0 * 32) })
}
"""


def test_every_trie_keeps_its_layout() -> None:
    """After inserts and removes, the trie holds exactly the ten keys left,
    each where its hash leads, with no branch a remove left empty or with
    one entry below the root."""
    header, mem = _run_pure(_compiled(_CANONICAL))
    assert isinstance(header, int)
    entries, broken = _trie(mem, header)
    assert (entries, broken) == (10, [])


def test_a_map_emptied_by_removes_is_the_empty_map() -> None:
    header, mem = _run_pure(_compiled(_CANONICAL.replace("1990", "2000")))
    assert isinstance(header, int)
    assert (_i32(mem, header), _i32(mem, header + 4)) == (0, 0)


_PERSISTENT = """\
private fn show(@Map<Int, Int> -> @String)
  requires(true) ensures(true) effects(pure)
{
  string_concat(int_to_string(map_size(@Map<Int, Int>.0)), string_concat(":", string_join(array_map(map_values(@Map<Int, Int>.0), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ",")))
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Map<Int, Int> = map_new();
  let @Map<Int, Int> = array_fold(array_range(0, 40), @Map<Int, Int>.0, fn(@Map<Int, Int>, @Int -> @Map<Int, Int>) effects(pure) { map_insert(@Map<Int, Int>.0, @Int.0, @Int.0) });
  let @Map<Int, Int> = map_insert(@Map<Int, Int>.0, 5, 500);
  let @Map<Int, Int> = map_insert(@Map<Int, Int>.1, 40, 4000);
  let @Map<Int, Int> = map_remove(@Map<Int, Int>.2, 7);
  let @Map<Int, Int> = map_remove(@Map<Int, Int>.3, 99);
  let @Set<Int> = set_add(set_add(set_new(), 1), 2);
  let @Set<Int> = set_add(@Set<Int>.0, 3);
  let @Set<Int> = set_remove(@Set<Int>.1, 1);
  IO.print(show(@Map<Int, Int>.4));
  IO.print(" ");
  IO.print(string_join(array_map(array_concat(set_to_array(@Set<Int>.2), set_to_array(@Set<Int>.1)), fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) }), ","));
  IO.print(" ");
  IO.print(show(@Map<Int, Int>.3));
  IO.print(" ");
  IO.print(show(@Map<Int, Int>.1));
  IO.print("\\n")
}
"""


def test_an_update_leaves_the_collection_it_was_given_as_it_was() -> None:
    """The map an insert or a remove was given keeps its size and its
    entries, and so does a set: an update that wrote into a block it
    shares would change the first map and the first set printed."""
    out = _native(_compiled(_PERSISTENT))
    first = ",".join(str(i) for i in range(40))
    assert out.split(" ")[0] == f"40:{first}"
    assert out.split(" ")[1] == "1,2,1,2,3"
    assert out.split(" ")[2] == "40:" + ",".join("500" if i == 5 else str(i) for i in range(40))
    assert out.split(" ")[3].strip() == f"39:{','.join(str(i) for i in range(40) if i != 7)}"


_COUNTS = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(array_range(0, 100), @Map<String, Int>.0, fn(@Map<String, Int>, @Int -> @Map<String, Int>) effects(pure) { map_insert(@Map<String, Int>.0, int_to_string(@Int.0 % 50), @Int.0) });
  let @Map<String, Int> = map_remove(map_remove(@Map<String, Int>.0, "7"), "nope");
  map_size(@Map<String, Int>.1) * 1000 + map_size(@Map<String, Int>.0)
}
"""


def test_a_count_is_the_entries_a_map_holds() -> None:
    """A present key inserted again leaves the count, a removed key takes
    one off, and an absent one none."""
    result = _compiled(_COUNTS)
    value, _ = _run_pure(result)
    assert value == 50 * 1000 + 49


_STRING_CONTENT = """\
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_insert(map_insert(map_new(), "ab", 1), string_concat("a", "b"), 2);
  let @Set<String> = set_add(set_add(set_new(), string_concat("x", "y")), "xy");
  map_size(@Map<String, Int>.0) * 100 + option_unwrap_or(map_get(@Map<String, Int>.0, string_concat("", "ab")), 0) * 10 + set_size(@Set<String>.0)
}
"""


def test_a_string_key_compares_by_content() -> None:
    """Two `String` keys with one content at two addresses are one key."""
    value, _ = _run_pure(_compiled(_STRING_CONTENT))
    assert value == 1 * 100 + 2 * 10 + 1


def _constant_hash(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every key hashes alike, so every key meets every other in one
    collision node below the last branch."""
    from vera.wasm import hamt

    monkeypatch.setattr(hamt, "_hash_body", lambda cls: ["i64.const 7"])


def test_keys_that_share_every_hash_bit_are_all_kept(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """With the hash a constant, a map of 40 keys keeps all 40, finds each,
    enumerates them in insertion order and removes them one by one."""
    _constant_hash(monkeypatch)
    source = cell_program("Int", "Int", 40)
    result = pipeline.compile(source, file="collide.vera").result
    assert result.ok, result.diagnostics
    assert _native(result) == expected_transcript("Int", "Int", 40)
    header, mem = _run_pure(pipeline.compile(_CANONICAL, file="c.vera").result)
    assert isinstance(header, int)
    assert _trie(mem, header) == (10, [])


#: The cells the collision battery runs: every representation, at the sizes
#: either side of the fan-out (a collision node of n entries is O(n) an
#: operation, so the battery stops below the wide sizes).
COLLISION_CELLS = [c for c in CELLS if c[2] <= 33]


@pytest.mark.parametrize("cell", COLLISION_CELLS, ids=[_cell_id(c) for c in COLLISION_CELLS])
def test_every_operation_is_the_same_when_every_key_collides(
    cell: tuple[str, str | None, int], monkeypatch: pytest.MonkeyPatch,
) -> None:
    key, value, n = cell
    _constant_hash(monkeypatch)
    result = pipeline.compile(cell_program(key, value, n), file="collide.vera").result
    assert result.ok, result.diagnostics
    assert _native(result) == expected_transcript(key, value, n)


EAGER_CELLS = [c for c in CELLS if c[2] in (33, 1024) and c[1] in ("Int", "String", None)]


@pytest.mark.parametrize("cell", EAGER_CELLS, ids=[_cell_id(c) for c in EAGER_CELLS])
def test_every_operation_survives_a_collection_at_every_allocation(
    cell: tuple[str, str | None, int], monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`VERA_EAGER_GC=1` collects on every `$alloc`: a block the generated
    code held unrooted across one would be swept and the transcript
    would change."""
    key, value, n = cell
    with monkeypatch.context() as patch:
        patch.setenv("VERA_EAGER_GC", "1")
        result = pipeline.compile(cell_program(key, value, n), file="eager.vera").result
    assert result.ok, result.diagnostics
    assert _native(result) == expected_transcript(key, value, n)


def test_repro_eager_collection_keeps_every_block_rooted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The one eager-collection cell every pull request runs: a
    `Map<String, String>` and a `Set<String>` of 33 elements, across a
    level of the trie, with a collection at every `$alloc`."""
    for value in ("String", None):
        with monkeypatch.context() as patch:
            patch.setenv("VERA_EAGER_GC", "1")
            result = pipeline.compile(cell_program("String", value, 33), file="eager.vera").result
        assert result.ok, result.diagnostics
        assert _native(result) == expected_transcript("String", value, 33)


def test_a_set_enumerates_alike_in_every_process(tmp_path: Path) -> None:
    """At c1fc89b2 the native host enumerated a `Set<String>` in Python's
    set order, which a process's string hashing decides: two processes
    with two hash seeds printed two orders."""
    import os
    import sys

    program = tmp_path / "set_order.vera"
    program.write_text(_SET_ORDER, encoding="utf-8")
    outputs = set()
    for seed in ("1", "2", "3"):
        env = {k: v for k, v in os.environ.items()
               if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE")}
        env["PYTHONHASHSEED"] = seed
        proc = subprocess.run(
            [sys.executable, "-c",
             "import sys; from vera.cli import main; "
             "sys.argv = ['vera', 'run', sys.argv[1]]; main()",
             str(program)],
            capture_output=True, text=True, encoding="utf-8", env=env,
            timeout=300, check=False)
        assert proc.returncode == 0, proc.stderr
        outputs.add(proc.stdout)
    assert outputs == {"pear,apple,kiwi,date,fig 40,3,17,9\n"}


# =====================================================================
# The collector (#1722, #1510): a map's fan-out bounds what marking it
# leaves pending
# =====================================================================

#: Allocates `n` strings of 4,096 bytes, each dead at once (#1722's churn),
#: so collections run while the map is live.
_CHURN = """\
private fn churn(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @Nat.1 } else {
    churn(@Nat.1 + string_length(string_repeat("y", 4096)), @Nat.0 - 1)
  }
}
"""


def _wide_map(n: int, churn: int) -> str:
    return _CHURN + f"""
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(array_range(0, {n}), @Map<String, Int>.0, fn(@Map<String, Int>, @Int -> @Map<String, Int>) effects(pure) {{ map_insert(@Map<String, Int>.0, int_to_string(@Int.0), @Int.0) }});
  let @Nat = churn(0, {churn});
  array_fold(array_range(0, {n}), nat_to_int(@Nat.0) * 0, fn(@Int, @Int -> @Int) effects(pure) {{ @Int.1 + option_unwrap_or(map_get(@Map<String, Int>.0, int_to_string(@Int.0)), -{n * n}) }})
}}
"""


@pytest.mark.parametrize("n", [
    10_000,
    pytest.param(100_000, marks=pytest.mark.stress),
    pytest.param(1_000_000, marks=[pytest.mark.stress, pytest.mark.budget(3600)]),
])
def test_marking_a_wide_map_keeps_every_key(n: int) -> None:
    """Collections over a live map of every width keep every key, and each
    walk of #1722's rescan visits each word and header of its range at most
    once.  A branch scans 32 children at most and an entry one key; what
    still fills the worklist at 100,000 entries is the stale tails of
    reused blocks (#1718): 26 collections walk there, 157 at 1,000,000, and
    none at 10,000."""
    from tests.test_gc_mark_width_1510 import _assert_each_stretch_walked_once, _counted_run

    result = pipeline.compile(_wide_map(n, 3000), file="wide.vera").result
    assert result.ok, result.diagnostics
    value, counted, walked = _counted_run(result)
    assert value == n * (n - 1) // 2
    _assert_each_stretch_walked_once(walked)
    if n == 10_000:
        assert counted["walked"] == 0, counted


@_needs_node
def test_a_wide_map_keeps_every_key_in_the_browser(tmp_path: Path) -> None:
    result = pipeline.compile(_wide_map(10_000, 3000), file="wide.vera").result
    assert result.ok, result.diagnostics
    wasm = tmp_path / "wide.wasm"
    wasm.write_bytes(result.wasm_bytes)
    proc = subprocess.run(
        [NODE or "node", "--experimental-wasm-exnref", str(HARNESS), str(wasm)],
        capture_output=True, text=True, encoding="utf-8", timeout=600, check=False)
    assert proc.returncode == 0, proc.stderr
    out = json.loads(proc.stdout)
    assert out.get("error") is None, out["error"]
    assert out["value"] == 10_000 * 9_999 // 2


@pytest.mark.stress
def test_a_wide_map_keeps_every_key_under_eager_collection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Every allocation collects a heap that grows with the map, so the
    run is quadratic in the width: about two minutes at 10,000 keys."""
    with monkeypatch.context() as patch:
        patch.setenv("VERA_EAGER_GC", "1")
        result = pipeline.compile(_wide_map(10_000, 0), file="wide.vera").result
    assert result.ok, result.diagnostics
    ran = pipeline.run(result, budget_s=600)
    assert ran.trap is None, ran.trap
    assert ran.execution.value == 10_000 * 9_999 // 2
