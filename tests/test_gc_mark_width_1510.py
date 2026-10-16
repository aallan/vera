"""The collector marks any heap the program can allocate (#1510).

`$gc_collect` marks through a fixed worklist of 16,384 entries
(`GC_WORKLIST_SIZE` in `vera/codegen/assembly.py`).  A push that found it
full executed `unreachable`, so a correct program died in the collector
whenever a collection ran with more values pending at once than the
worklist holds, although the heap itself was already allocated.

The class is every program whose live heap, at some collection, has more
than 16,384 values pending at once: one wide structure (an array or a
`Map` bucket holding heap values), one long chain (a list whose spine
leaves every cell's head pending), a structure of closures each capturing
a heap value, or any mixture, on every target that runs the generated
collector — native, the browser runtime and the WASI 0.2 component, which
embeds the same core module.

The instrument crosses the structure (an `Array<String>`; a list of a user
`data`, built and walked by tail calls; an `Array` of boxed closures each
capturing a `String`; a `Map<String, Int>` built by `map_insert`) with the
width, the collection (`VERA_EAGER_GC=1`, which collects on every
allocation, and the ordinary collector with a churn of 4,096-byte strings
that grows the heap while the structure is live), and the target.  Each
program's value reads every element's content after the collections, so a
value the collector failed to mark — swept, and its first word overwritten
by the free-list link — changes the answer.

The widths are relative to each shape's boundary: the smallest width that
trapped at f9ca14f8, measured per structure and collection (`BOUNDARY`).
Below it the deepest collection's pending set fitted the worklist; at it the
16,385th push trapped.  The boundary minus one is the negative space, the
nearest width the old collector already marked, and keeps its value; the
boundary, one past it, 20,000 and 100,000 were red.

Products that are not cells: eager collection at 100,000 (every allocation
collects a heap of that size, so the run is quadratic in the width); a
`Map` of more than 1,000 keys (each `map_insert` re-encodes the whole map
in the host, so the chain is quadratic in its length, and `json_parse`, the
one path that builds a wide `Map` in one host call, stops at the host
shadow stack's limit first, issue #692); a `Map` under eager collection
(each insert's re-encode collects once per key); a `Map` on
`--target wasi-p2`, which has no `Map` host functions.

The rescan's parts are pinned by unparametrised tests at the end of the
file, which every pull request runs: the dropped child marked at all, a
rescan followed by another while drains drop, both ends of the dirty range
walked, each walk resuming where the last stopped (an iteration counter:
that defect costs time, not a value), and the layout guard that keeps the
seed from ever filling the worklist.
"""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from tests import pipeline
from vera.codegen import CompileResult
from vera.runtime.wasi_host import execute_wasi_p2

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class — the collector, and the trap registry
# that names what the collector can trap with.
pytestmark = pytest.mark.matrix(
    decides=["vera/codegen/assembly.py", "vera/trap_registry.py"])

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


# =====================================================================
# The programs
# =====================================================================

_HEAD = "  requires(true) ensures(true) effects(pure)\n"

#: Allocates `n` strings of 4,096 bytes, each dead at once, and returns
#: their total length.  Run while a structure is live, it makes the heap
#: grow, and the ordinary collector collects before every growth.
_CHURN = """\
private fn churn(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @Nat.1 } else {
    churn(@Nat.1 + string_length(string_repeat("y", 4096)), @Nat.0 - 1)
  }
}
"""

_FIRST_CODES = f"""\
private fn first_codes(@Array<String> -> @Int)
{_HEAD}{{
  array_fold(@Array<String>.0, 0, fn(@Int, @String -> @Int) effects(pure) \
{{ @Int.0 + string_char_code(@String.0, 0) }})
}}
"""


def _program(shape: str, n: int, churn: int) -> str:
    """`main` builds a structure holding `n` heap values, runs `churn`
    while it is live, then sums the first character code of every value
    the structure holds, plus the churn's total."""
    if shape == "array":
        return _CHURN + f"""
public fn main(-> @Int)
{_HEAD}{{
  let @Array<String> = array_map(array_range(0, {n}), \
fn(@Int -> @String) effects(pure) {{ int_to_string(@Int.0) }});
  let @Nat = churn(0, {churn});
  array_fold(@Array<String>.0, nat_to_int(@Nat.0), \
fn(@Int, @String -> @Int) effects(pure) \
{{ @Int.0 + string_char_code(@String.0, 0) }})
}}
"""
    if shape == "list":
        return _CHURN + f"""
private data Chain {{ Link(String, Chain), End }}

private fn build(@Nat, @Chain -> @Chain)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{{
  if @Nat.0 == 0 then {{ @Chain.0 }} else {{
    build(@Nat.0 - 1, Link(nat_to_string(@Nat.0), @Chain.0))
  }}
}}

private fn walk(@Chain, @Nat, @Int -> @Int)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{{
  if @Nat.0 == 0 then {{ @Int.0 }} else {{
    match @Chain.0 {{
      End -> @Int.0,
      Link(@String, @Chain) -> \
walk(@Chain.0, @Nat.0 - 1, @Int.0 + string_char_code(@String.0, 0))
    }}
  }}
}}

public fn main(-> @Int)
{_HEAD}{{
  let @Chain = build({n}, End);
  let @Nat = churn(0, {churn});
  walk(@Chain.0, {n + 1}, nat_to_int(@Nat.0))
}}
"""
    if shape == "closures":
        return _CHURN + f"""
type Thunk = fn(Unit -> String) effects(pure);

private data Box {{ MkBox(Thunk) }}

private fn force(@Box -> @String)
{_HEAD}{{
  match @Box.0 {{ MkBox(@Thunk) -> apply_fn(@Thunk.0, ()) }}
}}

public fn main(-> @Int)
{_HEAD}{{
  let @Array<Box> = array_map(array_range(0, {n}), \
fn(@Int -> @Box) effects(pure) {{
    let @String = int_to_string(@Int.0);
    MkBox(fn(@Unit -> @String) effects(pure) {{ @String.0 }})
  }});
  let @Nat = churn(0, {churn});
  array_fold(@Array<Box>.0, nat_to_int(@Nat.0), \
fn(@Int, @Box -> @Int) effects(pure) \
{{ @Int.0 + string_char_code(force(@Box.0), 0) }})
}}
"""
    if shape == "map":
        return _FIRST_CODES + f"""
public fn main(-> @Int)
{_HEAD}{{
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(array_range(0, {n}), \
@Map<String, Int>.0, fn(@Map<String, Int>, @Int -> @Map<String, Int>) \
effects(pure) {{ map_insert(@Map<String, Int>.0, int_to_string(@Int.0), \
@Int.0) }});
  first_codes(map_keys(@Map<String, Int>.0)) + map_size(@Map<String, Int>.0)
}}
"""
    raise ValueError(shape)


def _expected(shape: str, n: int, churn: int) -> int:
    """The value `_program(shape, n, churn)` returns."""
    if shape == "list":  # the cells hold the strings of 1..n
        return 4096 * churn + sum(ord(str(i)[0]) for i in range(1, n + 1))
    if shape == "map":  # the keys 0..n-1, then map_size
        return sum(ord(str(i)[0]) for i in range(n)) + n
    return 4096 * churn + sum(ord(str(i)[0]) for i in range(n))


# =====================================================================
# Running a cell
# =====================================================================

def _compile(source: str, name: str, eager: bool,
             monkeypatch: pytest.MonkeyPatch) -> CompileResult:
    """Check and compile *source*; `VERA_EAGER_GC` is read as `$alloc` is
    emitted, so it is set for the compile alone."""
    with monkeypatch.context() as patch:
        if eager:
            patch.setenv("VERA_EAGER_GC", "1")
        else:
            patch.delenv("VERA_EAGER_GC", raising=False)
        compiled = pipeline.compile(source, file=f"{name}.vera")
    result = compiled.result
    assert result.ok, result.diagnostics
    return result


def _run(result: CompileResult, target: str, tmp_path: Path) -> object:
    """`main`'s value on *target*, or a description of the trap."""
    if target == "native":
        ran = pipeline.run(result, budget_s=600)
        return ran.execution.value if ran.trap is None else (
            f"trap: {ran.trap}")
    if target == "wasi-p2":
        return execute_wasi_p2(result).value
    assert target == "browser"
    wasm = tmp_path / "cell.wasm"
    wasm.write_bytes(result.wasm_bytes)
    proc = subprocess.run(
        [NODE or "node", "--experimental-wasm-exnref", str(HARNESS),
         str(wasm)],
        capture_output=True, text=True, encoding="utf-8", timeout=600,
        check=False)
    assert proc.returncode == 0, proc.stderr
    out = json.loads(proc.stdout)
    return out["value"] if out.get("error") is None else (
        f"trap: {out['error']}")


def _assert_value(shape: str, n: int, churn: int, eager: bool, target: str,
                  tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    result = _compile(_program(shape, n, churn), f"{shape}_{n}", eager,
                      monkeypatch)
    assert _run(result, target, tmp_path) == _expected(shape, n, churn)


# =====================================================================
# The reported program
# =====================================================================

#: Issue #1510's program as the issue wrote it.  Its `churn` reads its two
#: slots the other way round, so `churn(0, 3000)` binds the counter to 0
#: and returns 3000 at once; the collections that trapped run inside
#: `array_map`, as the array grows past 16,384 strings.
_ISSUE_PROGRAM = """\
private fn churn(@Nat, @Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.1) effects(pure)
{
  if @Nat.1 == 0 then { @Nat.0 } else {
    churn(@Nat.0 + string_length(string_repeat("y", 4096)), @Nat.1 - 1)
  }
}

public fn main(-> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = array_map(array_range(0, 20000), \
fn(@Int -> @String) effects(pure) { int_to_string(@Int.0) });
  let @Nat = churn(0, 3000);
  array_length(@Array<String>.0) + @Nat.0
}
"""


def test_repro_1510_the_issue_program_runs() -> None:
    """The issue's program returns its 20,000-element array's length plus
    `churn`'s 3,000, where the collector used to trap `unreachable`."""
    ran = pipeline.run(_ISSUE_PROGRAM, file="repro1510.vera")
    assert ran.trap is None, ran.trap
    assert ran.execution.value == 23000


# =====================================================================
# The width matrix
# =====================================================================

#: The smallest width at which each shape trapped at f9ca14f8, per
#: collection.  The deepest collection of the eager array and the eager
#: closures has three values pending beneath the structure (the
#: `array_range` input twice and the `array_map` closure); the list's spine
#: leaves one head pending per cell plus the next cell, so it overflows one
#: width earlier than an array whose pending set is its elements alone.
BOUNDARY: dict[tuple[str, str], int] = {
    ("array", "eager"): 16382,
    ("array", "normal"): 16385,
    ("list", "eager"): 16384,
    ("list", "normal"): 16384,
    ("closures", "eager"): 16382,
    ("closures", "normal"): 16385,
}

#: Every width is a run of the structure's boundary, or past it.
WIDTHS = ("boundary-1", "boundary", "boundary+1", "20000", "100000")

#: Strings of 4,096 bytes the churn allocates: ordinary collection runs only
#: when the heap must grow, and 12 MB of churn grows it past every free
#: list the structures leave; eager collection runs on every allocation, so
#: a short churn collects with the structure whole as often as a long one.
CHURN = {"eager": 30, "normal": 3000}

SHAPES = ("array", "list", "closures")


def _width(shape: str, collection: str, label: str) -> int:
    boundary = BOUNDARY[shape, collection]
    return {"boundary-1": boundary - 1, "boundary": boundary,
            "boundary+1": boundary + 1}.get(label) or int(label)


def _target_param(target: str) -> object:
    if target == "browser":
        return pytest.param(target, marks=pytest.mark.skipif(
            not _HAS_NODE, reason="Node.js with exnref is not available"))
    return target


TARGETS = [_target_param(t) for t in ("native", "browser", "wasi-p2")]


#: Collecting on every allocation makes a run quadratic in its width: a
#: cell takes 2.5 s to 40 s (the closures, four allocations an element), so
#: the product runs in the stress lane, and the ordinary collector's cells,
#: none over a fifth of a second, run in the pull-request gate.
@pytest.mark.stress
@pytest.mark.parametrize("target", TARGETS)
@pytest.mark.parametrize("width", WIDTHS[:4])
@pytest.mark.parametrize("shape", SHAPES)
def test_eager_collection_marks_every_width(
    shape: str, width: str, target: str, tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Collecting on every allocation, each structure keeps every value it
    holds at each width, on each target."""
    n = _width(shape, "eager", width)
    _assert_value(shape, n, CHURN["eager"], True, target, tmp_path,
                  monkeypatch)


@pytest.mark.parametrize("target", TARGETS)
@pytest.mark.parametrize("width", WIDTHS)
@pytest.mark.parametrize("shape", SHAPES)
def test_ordinary_collection_marks_every_width(
    shape: str, width: str, target: str, tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """With the ordinary collector, a collection the churn forces while the
    whole structure is live keeps every value it holds, on each target."""
    n = _width(shape, "normal", width)
    _assert_value(shape, n, CHURN["normal"], False, target, tmp_path,
                  monkeypatch)


#: Key counts for a `Map` built by `map_insert`.  Each insert re-encodes the
#: whole map in the host, and the collector also marks the freed blocks a
#: stale word still points at, so at f9ca14f8 the chain's deepest collection
#: overflowed the worklist from 596 keys on — not at every count past it,
#: since which freed blocks a stale word reaches moves with the allocation
#: sequence (597, 599 and 600 completed; 596, 598 and 1,000 trapped).  595
#: is the negative space, the largest count below the first that trapped.
MAP_KEYS = (595, 596, 598, 1000)


#: The native host re-encodes a map in Python, about 6 s for 600 keys and
#: 15 s for 1,000, so the native cells run in the stress lane; the browser
#: host's JavaScript takes under half a second and runs in the gate.
@pytest.mark.parametrize("target", [
    pytest.param("native", marks=pytest.mark.stress),
    _target_param("browser"),
])
@pytest.mark.parametrize("keys", MAP_KEYS)
def test_a_map_built_by_insert_keeps_every_key(
    keys: int, target: str, tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A `Map<String, Int>` of `keys` entries, built one `map_insert` at a
    time, keeps every key through the collections its inserts run."""
    _assert_value("map", keys, 0, False, target, tmp_path, monkeypatch)


# =====================================================================
# The mechanism, one test per part of it
# =====================================================================
#
# The cells above sample; these run on every pull request.  Each pins one
# part of the rescan (`_emit_gc_scan` and Phase 2b of `_emit_gc_collect`)
# and fails when that part is taken out.

def test_a_dropped_child_is_marked_by_the_rescan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A collection that drops pushes marks the dropped strings through
    the rescan before it sweeps: every one of 20,000 strings is read back
    intact.  Without the rescan the strings past the worklist's 16,384th
    entry are swept, and their first word holds a free-list link."""
    _assert_value("array", 20000, CHURN["normal"], False, "native",
                  tmp_path, monkeypatch)


def test_a_rescan_that_fills_the_worklist_is_followed_by_another(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """100,000 strings need about six walks per collection, each pushing
    at most 16,384 of them: marking stops only when a drain drops nothing,
    not after one rescan."""
    _assert_value("array", 100000, CHURN["normal"], False, "native",
                  tmp_path, monkeypatch)


_TWO_ARRAYS = _CHURN + _FIRST_CODES + f"""
public fn main(-> @Int)
{_HEAD}{{
  let @Array<String> = array_map(array_range(0, 20000), \
fn(@Int -> @String) effects(pure) {{ int_to_string(@Int.0) }});
  let @Array<String> = array_map(array_range(0, 20000), \
fn(@Int -> @String) effects(pure) {{ int_to_string(@Int.0 + 20000) }});
  let @Nat = churn(0, {CHURN["normal"]});
  first_codes(@Array<String>.1) + first_codes(@Array<String>.0) \
+ nat_to_int(@Nat.0)
}}
"""


def test_both_of_two_dirty_structures_are_rescanned() -> None:
    """Two live arrays of 20,000 strings each overflow the worklist in one
    drain, so the dirty range runs from the lower array to the higher:
    the rescan walks all of it, and the strings of both arrays are read
    back intact."""
    ran = pipeline.run(_TWO_ARRAYS, file="two_arrays.vera", budget_s=600)
    assert ran.trap is None, ran.trap
    want = (sum(ord(str(i)[0]) for i in range(40000))
            + 4096 * CHURN["normal"])
    assert ran.execution.value == want


#: The counters `_counted_run` threads through the collector, each an
#: exported mutable global: the words the rescan's walks visit, the walks,
#: the collections that walked at least once, and that collection's flag.
_COUNTERS = ("walk_words", "walks", "walked", "walking")


def _bump(name: str) -> str:
    return f"global.get ${name}\ni32.const 1\ni32.add\nglobal.set ${name}\n"


def _counted_run(result: CompileResult) -> tuple[int, dict[str, int]]:
    """Run a pure program's `main` with the rescan's counters threaded
    into its collector, and return its value and the counters.

    The counters are placed at the labels Phase 2b's walk is emitted
    under, `$rw_done` (where a walk starts) and `$rs_scan_loop` (once per
    word a walk visits), each asserted present exactly once."""
    import wasmtime

    wat = result.wat
    decls = "".join(
        f'  (global ${name} (export "{name}") (mut i32) (i32.const 0))\n'
        for name in _COUNTERS)
    anchor = "  (global $gc_free_head"
    assert wat.count(anchor) == 1
    wat = wat.replace(anchor, decls + anchor)
    for label, code in (
        ("loop $rs_scan_loop\n", "loop $rs_scan_loop\n" + _bump("walk_words")),
        ("block $rw_done\n",
         _bump("walks") + "global.get $walking\ni32.eqz\nif\n"
         + _bump("walked") + "i32.const 1\nglobal.set $walking\nend\n"
         + "block $rw_done\n"),
        ("    ;; Worklist region: gc_stack_limit .. gc_worklist_end.\n",
         "    i32.const 0\n    global.set $walking\n"
         "    ;; Worklist region: gc_stack_limit .. gc_worklist_end.\n"),
    ):
        assert wat.count(label) == 1, label
        wat = wat.replace(label, code)
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    linker = wasmtime.Linker(engine)
    module = wasmtime.Module(engine, wat)

    def refuse(*args: int) -> None:
        raise AssertionError(f"the program called a host import: {args}")

    # A pure program's imports are the signals its checks would call; a
    # run that passes them calls none, so each is a stub that fails.
    for imported in module.imports:
        assert isinstance(imported.type, wasmtime.FuncType), imported.name
        linker.define_func(imported.module, imported.name or "",
                           imported.type, refuse)
    exports = linker.instantiate(store, module).exports(store)
    value = exports["main"](store)
    return value, {name: exports[name].value(store) for name in _COUNTERS}


def test_each_rescan_resumes_where_the_last_one_stopped() -> None:
    """A walk that fills the worklist stops at the word whose push it
    dropped, and the next walk resumes there, so in each collection the
    walks visit each word of the one dirty object, an array of 100,000
    strings (200,000 words), once, plus the dropped word each walk stops
    on and the final exit test.  A walk that started over from the range's
    first word would visit the prefix it had already pushed once per walk,
    about three times as many words at six walks a collection.  The
    iteration counter is the killer: the cost is the defect, not the
    value."""
    from vera.codegen.assembly import GC_WORKLIST_SIZE

    n = 100000
    result = _compile(_program("array", n, CHURN["normal"]), "resume", False,
                      pytest.MonkeyPatch())
    value, counted = _counted_run(result)
    assert value == _expected("array", n, CHURN["normal"])
    # The premise: collections walked, several times each, so a walk that
    # started over would revisit what an earlier walk pushed.
    assert counted["walked"] > 0, counted
    assert counted["walks"] > 2 * counted["walked"], counted
    assert counted["walks"] >= n // (GC_WORKLIST_SIZE // 4), counted
    words = 2 * n  # an `Array<String>` element is a (pointer, length) pair
    bound = counted["walked"] * (words + 1) + counted["walks"]
    assert counted["walk_words"] <= bound, (counted, bound)


def test_the_worklist_holds_every_root_the_seed_can_push() -> None:
    """The seed pushes one 4-byte entry per 4-byte shadow-stack root onto
    an empty worklist and has no object to record a dropped push against,
    so the worklist must be no smaller than the shadow stack."""
    from vera.codegen.assembly import GC_STACK_SIZE, GC_WORKLIST_SIZE

    assert GC_STACK_SIZE % 4 == 0 and GC_WORKLIST_SIZE % 4 == 0
    assert GC_WORKLIST_SIZE // 4 >= GC_STACK_SIZE // 4


def test_a_worklist_smaller_than_the_shadow_stack_is_refused(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Code generation refuses a layout whose worklist is smaller than its
    shadow stack, the edit a layout rework would make, rather than emit a
    seed that could drop a root."""
    from vera.codegen import assembly
    from vera.skip import CodegenInvariantError

    monkeypatch.setattr(assembly, "GC_WORKLIST_SIZE",
                        assembly.GC_STACK_SIZE - 4)
    with pytest.raises(CodegenInvariantError,
                       match="smaller than the shadow stack"):
        pipeline.compile(_program("array", 10, 1), file="small_wl.vera",
                         checked=False).result


def test_a_worklist_the_size_of_the_shadow_stack_still_marks(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The guard's nearest accepted layout, a worklist exactly the size of
    the shadow stack (4,096 entries), compiles, and marks 20,000 strings
    through about five walks a collection."""
    from vera.codegen import assembly

    monkeypatch.setattr(assembly, "GC_WORKLIST_SIZE", assembly.GC_STACK_SIZE)
    _assert_value("array", 20000, CHURN["normal"], False, "native",
                  tmp_path, monkeypatch)
