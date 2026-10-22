"""The collector never marks a block on the free list (#1718).

The sweep links a freed block into the free list through its first payload
word and leaves the rest of the payload as it was; `$alloc` reuses a free
block whole, so an object smaller than the block it reuses keeps the
block's size in its header and the scan reads the old payload behind the
words it wrote; and Phase 1 recorded every block on the allocation chain as
an object base, free ones included.  So a word in a live object that equals
a free block's address (a stale word in a reused block's slack, or an
integer that happens to) marked that free block, its first word, the
free-list link, marked the next one, and the whole free chain behind it was
kept, with every stale graph those blocks still pointed at.  Memory the
program no longer held was retained at every collection that met a free
list.

The class is every collection whose free list is non-empty when it marks:
any program that allocates, frees and allocates again.  The fix is where
the mark candidate is decided: Phase 1b clears the object-base bit of every
block on the free list (`$gc_clear_base`), so `$gc_is_base` refuses a free
block at the shadow-stack seed, the drain's scan and the rescan alike, and
no free block is pushed or marked.  Zeroing a block at the sweep or on
reuse removes the stale words but not the integer that equals a free
block's address, nor the free-list link that carries the mark down the
chain (`test_repro_an_integer_equal_to_a_free_block_marks_nothing`).

The instrument splices counters into the emitted `$gc_collect` (the
module's own collector, not a stand-in) just before the sweep, while the
old free list is intact: the free list's length, the blocks on it that are
marked, the marked blocks off it and their words, the roots, and the
collection's worklist high-water mark.  A collection marks no free block,
and its high-water mark is at most the words of the live objects it
scanned plus its roots (each push is one scanned word of a marked object
or one root, and only objects off the free list are marked).  The spliced
module runs in a child process with its fault signals handled, so a probe
that reads the heap never runs in the test process.

The matrix crosses the container a program builds, drops and builds again
(an `Array<String>`, a `Map<String, Int>` built by `map_insert`, a `String`
built by concatenation, a list of a user `data`) with its width, below the
worklist's 16,384 entries and past them (so drains drop pushes and the
rescan runs), and the collection (`VERA_EAGER_GC=1`, which collects on
every allocation, and the ordinary collector driven by a churn of 4,096-byte
strings).  Each cell asserts its premise (a collection met a non-empty free
list; past the bound, the worklist filled) beside the class.  Products that
are not cells: the string past the bound (a `String` is one block, so its
pending set stays at a few entries at any length: at 20,000 pieces the
high-water mark was 8); eager collection past the bound (each allocation
collects a heap of 20,000 values: with the fix the array took 25 s, the list
70 s and the map more than the stress lane's 600 s; the rescan path is held
by the ordinary collector's cells past the bound, and the trigger by the
eager cells below it).  The browser runtime and the WASI component run the
same core module's collector; the targets differ only in their hosts, which
the collector never calls.
"""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/codegen/assembly.py"])

ROOT = Path(__file__).resolve().parent.parent

# =====================================================================
# The instrument
# =====================================================================

#: The counters the splice exports, each an `i32` global.
COUNTERS = ("colls", "free_seen", "free_marked", "free_marked_max",
            "free_max", "live_max", "hwm", "hwm_over", "hwm_over_max")


def _max(name: str, local: str) -> str:
    return (f"local.get {local}\nglobal.get $dbg_{name}\ni32.gt_u\nif\n"
            f"local.get {local}\nglobal.set $dbg_{name}\nend\n")


def _inc(name: str) -> str:
    return (f"global.get $dbg_{name}\ni32.const 1\ni32.add\n"
            f"global.set $dbg_{name}\n")


#: A block's scanned words from its header at the address on the stack:
#: `(size + 3) >> 2`, the words `_emit_gc_scan` reads.
_WORDS = ("i32.load\ni32.const 1\ni32.shr_u\ni32.const 3\ni32.add\n"
          "i32.const 2\ni32.shr_u\n")


def _splice(wat: str, anchor: str, code: str, after: bool = False) -> str:
    assert wat.count(anchor) == 1, anchor
    return wat.replace(anchor, anchor + code if after else code + anchor)


def instrument(wat: str) -> str:
    """*wat* with the counters threaded through its `$gc_collect`.

    At entry the collection's high-water mark is reset; at every pop it is
    raised to the worklist's depth; before the sweep the free list is
    walked (its length; its marked blocks and their words), then the heap
    (its marked blocks and their words), and the collection's figures
    folded into the exported counters.  `free_marked` sums the free-list
    blocks found marked; `hwm_over` counts the collections whose high-water
    mark exceeded the live words plus the roots."""
    decls = "".join(
        f'  (global $dbg_{n} (export "dbg_{n}") (mut i32) (i32.const 0))\n'
        for n in COUNTERS) + "  (global $dbg_chwm (mut i32) (i32.const 0))\n"
    wat = _splice(wat, "  (global $gc_free_head", decls)
    wat = _splice(wat, "    (local $rs_end i32)\n", "".join(
        f"    (local $dbg_{x} i32)\n" for x in "abcdefgh"), after=True)
    wat = _splice(
        wat, "    ;; Worklist region: gc_stack_limit .. gc_worklist_end.\n",
        "    i32.const 0\n    global.set $dbg_chwm\n")
    wat = _splice(wat, "        ;; Pop from worklist\n", (
        "local.get $wl_ptr\nlocal.get $wl_base\ni32.sub\ni32.const 2\n"
        "i32.shr_u\nlocal.set $dbg_a\n" + _max("chwm", "$dbg_a")))
    count = (
        # a = free-list length, b = its marked blocks, d = their words
        "i32.const 0\nlocal.set $dbg_a\ni32.const 0\nlocal.set $dbg_b\n"
        "i32.const 0\nlocal.set $dbg_d\n"
        "global.get $gc_free_head\nlocal.set $dbg_c\n"
        "block $dbg_fd\nloop $dbg_fl\n"
        "local.get $dbg_c\ni32.eqz\nbr_if $dbg_fd\n"
        "local.get $dbg_a\ni32.const 1\ni32.add\nlocal.set $dbg_a\n"
        "local.get $dbg_c\ni32.const 4\ni32.sub\ni32.load\ni32.const 1\n"
        "i32.and\nif\nlocal.get $dbg_b\ni32.const 1\ni32.add\n"
        "local.set $dbg_b\nlocal.get $dbg_d\nlocal.get $dbg_c\ni32.const 4\n"
        "i32.sub\n" + _WORDS + "i32.add\nlocal.set $dbg_d\nend\n"
        "local.get $dbg_c\ni32.load\nlocal.set $dbg_c\n"
        "br $dbg_fl\nend\nend\n"
        # e = marked blocks, f = their words
        "i32.const 0\nlocal.set $dbg_e\ni32.const 0\nlocal.set $dbg_f\n"
        "global.get $gc_heap_start\nlocal.set $dbg_c\n"
        "block $dbg_hd\nloop $dbg_hl\n"
        "local.get $dbg_c\nglobal.get $heap_ptr\ni32.ge_u\nbr_if $dbg_hd\n"
        "local.get $dbg_c\ni32.load\ni32.const 1\ni32.and\n"
        "if\nlocal.get $dbg_e\ni32.const 1\ni32.add\nlocal.set $dbg_e\n"
        "local.get $dbg_f\nlocal.get $dbg_c\n" + _WORDS
        + "i32.add\nlocal.set $dbg_f\nend\n"
        "local.get $dbg_c\ni32.load\ni32.const 1\ni32.shr_u\ni32.const 11\n"
        "i32.add\ni32.const -8\ni32.and\nlocal.get $dbg_c\ni32.add\n"
        "local.set $dbg_c\nbr $dbg_hl\nend\nend\n"
        # e, f = the live blocks and words; g = f + the roots
        "local.get $dbg_e\nlocal.get $dbg_b\ni32.sub\nlocal.set $dbg_e\n"
        "local.get $dbg_f\nlocal.get $dbg_d\ni32.sub\nlocal.set $dbg_f\n"
        "global.get $gc_sp\nglobal.get $gc_stack_base\ni32.sub\ni32.const 2\n"
        "i32.shr_u\nlocal.get $dbg_f\ni32.add\nlocal.set $dbg_g\n"
        + _inc("colls")
        + "local.get $dbg_a\nif\n" + _inc("free_seen") + "end\n"
        "global.get $dbg_free_marked\nlocal.get $dbg_b\ni32.add\n"
        "global.set $dbg_free_marked\n"
        + _max("free_marked_max", "$dbg_b") + _max("free_max", "$dbg_a")
        + _max("live_max", "$dbg_e")
        + "global.get $dbg_chwm\nlocal.set $dbg_h\n" + _max("hwm", "$dbg_h")
        + "local.get $dbg_h\nlocal.get $dbg_g\ni32.gt_u\nif\n"
        + _inc("hwm_over")
        + "local.get $dbg_h\nlocal.get $dbg_g\ni32.sub\nlocal.set $dbg_h\n"
        + _max("hwm_over_max", "$dbg_h") + "end\n")
    return _splice(
        wat, "    ;; === Phase 3: Sweep — build free list ===\n", count)


# =====================================================================
# The child
# =====================================================================

#: Runs on the WAT it reads from stdin, in a child process whose fault
#: signals exit 200.  Mode `main` calls `main` (with the integer arguments
#: after the mode) and reports its value or trap with the counters; mode
#: `probe` drives the collector directly (`_PROBE`).  A pure program's
#: imports are the signals its checks would call, each a stub that fails,
#: and the `String` hash key, the native host's own.
_CHILD = r'''
import json, os, signal, sys
for _name in ("SIGSEGV", "SIGBUS"):
    _sig = getattr(signal, _name, None)
    if _sig is not None:
        signal.signal(_sig, lambda *_: os._exit(200))
import wasmtime
from vera.codegen.api import HOST_BINDERS

wat = sys.stdin.buffer.read().decode("utf-8")
mode, args = sys.argv[1], [int(a) for a in sys.argv[2:]]
config = wasmtime.Config()
config.wasm_exceptions = True
engine = wasmtime.Engine(config)
store = wasmtime.Store(engine)
module = wasmtime.Module(engine, wat)
linker = wasmtime.Linker(engine)
for imported in module.imports:
    if (imported.module, imported.name) == ("vera", "hash_key"):
        continue
    def refuse(*a, _name=imported.name):
        raise RuntimeError(f"the module called the host import {_name}")
    linker.define_func(imported.module, imported.name, imported.type, refuse)
if any((i.module, i.name) == ("vera", "hash_key") for i in module.imports):
    HOST_BINDERS["hash"](linker, {"hash_key"}, None)
exports = linker.instantiate(store, module).exports(store)
out = {}
if mode == "main":
    try:
        out["value"] = exports["main"](store, *args)
    except Exception as exc:
        out["trap"] = f"{type(exc).__name__}: {exc}"[:400]
else:
    out.update(PROBE(store, exports, args))
out["counts"] = {k[4:]: g.value(store) for k, g in exports.items()
                 if k.startswith("dbg_") and isinstance(g, wasmtime.Global)}
print(json.dumps(out))
'''


@dataclass(frozen=True)
class Outcome:
    """What the child reported: `main`'s value or trap, or the probe's
    record, and the counters."""

    value: object
    trap: str | None
    counts: dict[str, int]
    probe: dict[str, object]


def _child(wat: str, mode: str, args: tuple[int, ...] = (),
           probe: str = "", timeout: float = 600) -> Outcome:
    """Run *wat* in a child process (`_CHILD`), from the repository root so
    it imports this tree's `vera`."""
    script = (probe or "PROBE = None\n") + _CHILD
    proc = subprocess.run(
        [sys.executable, "-c", script, mode, *map(str, args)],
        input=wat, capture_output=True, text=True, encoding="utf-8",
        cwd=ROOT, timeout=timeout, check=False)
    assert proc.returncode == 0, (proc.returncode, proc.stderr[-2000:])
    out = json.loads(proc.stdout)
    return Outcome(out.get("value"), out.get("trap"), out["counts"],
                   {k: v for k, v in out.items()
                    if k not in ("value", "trap", "counts")})


def _wat(source: str, eager: bool, monkeypatch: pytest.MonkeyPatch,
         check_marks: bool = False) -> str:
    """Check and compile *source*; `VERA_EAGER_GC` and `VERA_GC_CHECK_MARKS`
    are read as the collector is emitted, so each is set for the compile
    alone."""
    with monkeypatch.context() as patch:
        for name, on in (("VERA_EAGER_GC", eager),
                         ("VERA_GC_CHECK_MARKS", check_marks)):
            if on:
                patch.setenv(name, "1")
            else:
                patch.delenv(name, raising=False)
        return pipeline.compile(source, file="free_blocks.vera").wat


def _counted(source: str, eager: bool, monkeypatch: pytest.MonkeyPatch,
             args: tuple[int, ...] = ()) -> Outcome:
    """*source*'s `main`, run with the counters threaded into its
    collector."""
    return _child(instrument(_wat(source, eager, monkeypatch)), "main", args)


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

#: `rounds(k, 0)` sums `one(k) + ... + one(1)`: each round builds in the
#: blocks the round before it freed.
_ROUNDS = """\
private fn rounds(@Nat, @Int -> @Int)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { @Int.0 } else {
    rounds(@Nat.0 - 1, @Int.0 + one(nat_to_int(@Nat.0)))
  }
}
"""


def _one(shape: str, n: int, churn: int) -> str:
    """`one(seed)` builds a structure of `n` heap values from *seed*, runs
    the churn while it is live, and reads every value back."""
    if shape == "array":
        return f"""
private fn one(@Int -> @Int)
{_HEAD}{{
  let @Array<String> = array_map(array_range(0, {n}), \
fn(@Int -> @String) effects(pure) {{ int_to_string(@Int.0 + @Int.1) }});
  let @Nat = churn(0, {churn});
  array_fold(@Array<String>.0, nat_to_int(@Nat.0), \
fn(@Int, @String -> @Int) effects(pure) \
{{ @Int.0 + string_char_code(@String.0, 0) }})
}}
"""
    if shape == "map":
        return f"""
private fn one(@Int -> @Int)
{_HEAD}{{
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(array_range(0, {n}), \
@Map<String, Int>.0, fn(@Map<String, Int>, @Int -> @Map<String, Int>) \
effects(pure) {{ map_insert(@Map<String, Int>.0, \
int_to_string(@Int.0 + @Int.1), @Int.0) }});
  let @Nat = churn(0, {churn});
  array_fold(map_keys(@Map<String, Int>.0), \
nat_to_int(@Nat.0) + map_size(@Map<String, Int>.0), \
fn(@Int, @String -> @Int) effects(pure) \
{{ @Int.0 + string_char_code(@String.0, 0) }})
}}
"""
    if shape == "string":
        return f"""
private fn one(@Int -> @Int)
{_HEAD}{{
  let @String = array_fold(array_range(0, {n}), "", \
fn(@String, @Int -> @String) effects(pure) \
{{ string_concat(@String.0, int_to_string(@Int.0 + @Int.1)) }});
  let @Nat = churn(0, {churn});
  nat_to_int(string_length(@String.0) + @Nat.0) \
+ string_char_code(@String.0, 0)
}}
"""
    assert shape == "data"
    return f"""
private data Chain {{ Link(String, Chain), End }}

private fn build(@Nat, @Int, @Chain -> @Chain)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{{
  if @Nat.0 == 0 then {{ @Chain.0 }} else {{
    build(@Nat.0 - 1, @Int.0, \
Link(int_to_string(nat_to_int(@Nat.0) + @Int.0), @Chain.0))
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

private fn one(@Int -> @Int)
{_HEAD}{{
  let @Chain = build({n}, @Int.0, End);
  let @Nat = churn(0, {churn});
  walk(@Chain.0, {n + 1}, nat_to_int(@Nat.0))
}}
"""


ROUNDS = 3


def _program(shape: str, n: int, churn: int) -> str:
    return _CHURN + _ROUNDS + _one(shape, n, churn) + f"""
public fn main(-> @Int)
{_HEAD}{{
  rounds({ROUNDS}, 0)
}}
"""


def _expected(shape: str, n: int, churn: int) -> int:
    """The value `_program(shape, n, churn)` returns."""
    total = 0
    for seed in range(1, ROUNDS + 1):
        total += 4096 * churn
        if shape == "array":
            total += sum(ord(str(i + seed)[0]) for i in range(n))
        elif shape == "map":
            total += n + sum(ord(str(i + seed)[0]) for i in range(n))
        elif shape == "string":
            text = "".join(str(i + seed) for i in range(n))
            total += len(text) + ord(text[0])
        else:
            total += sum(ord(str(i + seed)[0]) for i in range(1, n + 1))
    return total


# =====================================================================
# The matrix
# =====================================================================

#: The worklist's entries (`GC_WORKLIST_SIZE` bytes of `i32`).
WORKLIST_ENTRIES = 16384

#: Below the worklist's entries, and past them: the array's and the list's
#: pending sets are their widths, and the map's is its `map_keys` array.
WIDTHS = {"under": 100, "past": 20000}

#: Strings of 4,096 bytes the churn allocates: eager collection runs on
#: every allocation, so a short churn collects as often as a long one; the
#: ordinary collector runs when the heap must grow, and 12 MB of churn
#: grows it while the structure is live.
CHURN = {"eager": 30, "ordinary": 3000}

SHAPES = ("array", "map", "string", "data")


def _assert_no_free_block_marked(shape: str, width: str, trigger: str,
                                 monkeypatch: pytest.MonkeyPatch) -> None:
    n, churn = WIDTHS[width], CHURN[trigger]
    run = _counted(_program(shape, n, churn), trigger == "eager", monkeypatch)
    counts = run.counts
    assert run.trap is None, run.trap
    assert run.value == _expected(shape, n, churn), (run.value, counts)
    # The premises: a collection met a non-empty free list, and past the
    # bound the worklist filled, so drains dropped pushes and the rescan
    # scanned the objects that dropped them.
    assert counts["free_seen"] > 0, counts
    if width == "past":
        assert counts["hwm"] == WORKLIST_ENTRIES, counts
    assert counts["free_marked"] == 0, counts
    assert counts["hwm_over"] == 0, counts


def _cells(triggers: tuple[str, ...]) -> list[object]:
    return [pytest.param(shape, width, trigger,
                         id=f"{shape}-{width}-{trigger}")
            for shape in SHAPES for width in WIDTHS for trigger in triggers
            if not (shape == "string" and width == "past")
            and not (width == "past" and trigger == "eager")]


@pytest.mark.parametrize(("shape", "width", "trigger"),
                         _cells(("eager", "ordinary")))
def test_a_collection_marks_no_free_block(
    shape: str, width: str, trigger: str, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Each container, built, dropped and built again, keeps every value it
    holds, and no collection marks a block on the free list or holds more
    entries on its worklist than the live words it scanned and its roots.
    At 6141d6ad every eager cell and the ordinary map, list, and array past
    the bound marked free blocks (up to 4,300,544 in one run)."""
    _assert_no_free_block_marked(shape, width, trigger, monkeypatch)


# =====================================================================
# The reported program, and the mechanism's parts
# =====================================================================

#: Issue #1718's program as the issue wrote it.  At c1fc89b2 it trapped in
#: `$gc_collect` (the retained graph overflowed the worklist); #1510's
#: overflow-tolerant marking removed the trap and left the retention.
_ISSUE_PROGRAM = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(array_range(0, 599), \
@Map<String, Int>.0, fn(@Map<String, Int>, @Int -> @Map<String, Int>) \
effects(pure) { map_insert(@Map<String, Int>.0, int_to_string(@Int.0), \
@Int.0) });
  map_size(@Map<String, Int>.0)
}
"""


def test_repro_1718_the_issue_program_marks_no_free_block(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The 599-key map returns 599, and collecting on every allocation no
    collection marks a free block: at 6141d6ad, 24 of its 3,703
    collections marked one."""
    run = _counted(_ISSUE_PROGRAM, True, monkeypatch)
    assert run.value == 599, run
    assert run.counts["free_seen"] > 0, run.counts
    assert run.counts["free_marked"] == 0, run.counts


#: The list `examples/gc_pressure.vera` builds, three times: a `Nil` (8
#: bytes) reuses a freed `Cons` (24 bytes) whole, and the old `next` word in
#: its slack points into the free list.
_GC_PRESSURE = (ROOT / "examples" / "gc_pressure.vera").read_text(
    encoding="utf-8").replace("repeat(30, 0)", "repeat(3, 0)")


def test_repro_a_reused_block_s_stale_word_marks_no_free_chain(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`examples/gc_pressure.vera`'s list, built three times collecting on
    every allocation, marks no free block.  At 6141d6ad the stale `next`
    word in a reused block's slack marked 598 free blocks, the old list
    and the free chain behind it."""
    assert "repeat(3, 0)" in _GC_PRESSURE
    run = _counted(_GC_PRESSURE, True, monkeypatch)
    assert run.value == 3 * 5050, run
    assert run.counts["free_seen"] > 0, run.counts
    assert run.counts["free_marked"] == 0, run.counts


#: Drives the collector directly, on a module compiled to collect on every
#: allocation: a rooted 24-byte block `S`; 64 blocks of 24 bytes and a
#: block of `8 * wide` bytes whose words name them, all rooted while they
#: are built and then unrooted; an allocation that no free block fits, so
#: its collection frees the 65 and it bumps; `S`'s last word set to a free
#: block's address (the `wide` one, or the 18th of the 64 when `wide` is
#: 0), as a stale word; and a second such allocation, whose collection is
#: the one measured.  With `reuse`, a 24-byte block `R` is allocated after
#: the first collection (off the free list: the heap does not grow),
#: filled and rooted, and `S`'s
#: word names it instead.  Reports the free blocks marked, read from their
#: headers, whether `S` stayed marked with its word unchanged, and whether
#: `R` was marked with its words intact.
_PROBE = r'''
def PROBE(store, exports, args):
    import struct
    mem, alloc = exports["vera.memory"], exports["vera.alloc"]
    sp = exports["vera.gc_sp"]
    def rd(a):
        return struct.unpack("<I", mem.read(store, a, a + 4))[0]
    def wr(a, v):
        mem.write(store, struct.pack("<I", v), a)
    def root(v):
        s = sp.value(store)
        wr(s, v)
        sp.set_value(store, s + 4)
    wide_words, reuse = 2 * args[0], args[1]
    s = alloc(store, 24)
    for i in range(6):
        wr(s + 4 * i, 0)
    root(s)
    mark = sp.value(store)
    blocks = []
    for _ in range(64):
        blocks.append(alloc(store, 24))
        root(blocks[-1])
    wide = alloc(store, 4 * wide_words)
    root(wide)
    for i in range(1, wide_words):
        wr(wide + 4 * i, blocks[i % 64])
    sp.set_value(store, mark)
    alloc(store, 4 * wide_words + 64)
    assert len(set(blocks)) == 64
    assert not any(rd(b - 4) & 1 for b in [*blocks, wide])
    target = wide if wide_words else blocks[17]
    r = 0
    if reuse:
        hp = exports["vera.heap_ptr"]
        top = hp.value(store)
        r = alloc(store, 24)
        assert hp.value(store) == top and r < top   # off the free list
        for i in range(6):
            wr(r + 4 * i, 0xA5A5A5A0 + 8 * i)
        root(r)
        target = r
    wr(s + 20, target)
    alloc(store, 4 * wide_words + 64)
    return {"marked": sum(rd(b - 4) & 1 for b in blocks if b != r),
            "wide_marked": rd(wide - 4) & 1, "s_marked": rd(s - 4) & 1,
            "s_word": rd(s + 20) == target,
            "r_marked": rd(r - 4) & 1 if r else None,
            "r_intact": all(rd(r + 4 * i) == 0xA5A5A5A0 + 8 * i
                            for i in range(6)) if r else None}
'''


_HARNESS = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_reverse([1, 2, 3])[0] }
"""


def _probe(wide: int, monkeypatch: pytest.MonkeyPatch,
           reuse: bool = False) -> Outcome:
    wat = instrument(_wat(_HARNESS, True, monkeypatch))
    return _child(wat, "probe", (wide, int(reuse)), probe=_PROBE)


def test_repro_a_stale_word_to_a_free_block_marks_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A live object's word that holds a free block's address marks
    neither that block nor the free chain its first word links on to; the
    object itself stays marked and the word unchanged.  At 6141d6ad the
    word marked the block and the free blocks behind it."""
    run = _probe(0, monkeypatch)
    assert run.probe["s_marked"] == 1 and run.probe["s_word"], run
    assert run.probe["marked"] == 0, run
    assert run.counts["free_marked"] == 0, run.counts


def test_repro_the_high_water_mark_stays_within_the_live_set(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A stale word to a freed block of 4,096 words, each naming one of 64
    freed blocks, pushes none of them: the high-water mark stays within the
    live words and roots.  At 6141d6ad the freed block was marked and its
    4,095 words pushed."""
    run = _probe(2048, monkeypatch)
    assert run.probe["s_marked"] == 1 and run.probe["s_word"], run
    assert run.probe["wide_marked"] == 0 and run.probe["marked"] == 0, run
    assert run.counts["hwm_over"] == 0, run.counts
    # The setup's collections seed the 65 blocks it roots while it builds
    # them; no collection pushes the 4,095 words the freed block names.
    assert run.counts["hwm"] < 4095, run.counts


def test_a_block_reused_from_the_free_list_is_marked(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The nearest neighbour of a free block: one `$alloc` took off the
    free list before the collection.  Rooted, and named by a live word, it
    is marked and keeps its words, and the blocks still free are not
    marked.  A Phase 1b that walked the list the sweep left, rather than
    the list `$alloc` left, would refuse it and sweep it while live."""
    run = _probe(0, monkeypatch, reuse=True)
    assert run.probe["s_marked"] == 1 and run.probe["s_word"], run
    assert run.probe["r_marked"] == 1 and run.probe["r_intact"], run
    assert run.probe["marked"] == 0, run
    assert run.counts["free_marked"] == 0, run.counts


def test_check_marks_traps_on_a_mark_of_a_free_block(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`VERA_GC_CHECK_MARKS` finds a free block by walking the free list,
    not by reading the bitmap Phase 1b clears: with Phase 1b it holds over
    the list `examples/gc_pressure.vera` builds, and dropped into a
    collector without Phase 1b it traps at the first free block marked."""
    from vera.codegen.assembly import AssemblyMixin

    run = _child(_wat(_GC_PRESSURE, True, monkeypatch, check_marks=True),
                 "main")
    assert run.trap is None and run.value == 3 * 5050, run
    monkeypatch.setattr(AssemblyMixin, "_emit_gc_unbase_free",
                        staticmethod(lambda: ""), raising=False)
    run = _child(_wat(_GC_PRESSURE, True, monkeypatch, check_marks=True),
                 "main")
    assert run.trap is not None and "unreachable" in run.trap, run


def _integers_program(span: int) -> str:
    """`main(base)` builds and drops a list of 100 cells three times, then
    holds an `Array<Int>` of the `span` body addresses from *base* on (the
    heap's start plus 4, then every 8 bytes) while it allocates: an
    integer that equals a free block's address, as a program can compute
    one."""
    return f"""\
private data List {{ Nil, Cons(Int, List) }}

private fn build(@Int, @List -> @List)
  requires(true) ensures(true) decreases(@Int.0) effects(pure)
{{
  match @Int.0 <= 0 {{
    true -> @List.0,
    false -> build(@Int.0 - 1, Cons(@Int.0, @List.0))
  }}
}}

private fn sum(@List -> @Int)
  requires(true) ensures(true) decreases(@List.0) effects(pure)
{{
  match @List.0 {{ Nil -> 0, Cons(@Int, @List) -> @Int.0 + sum(@List.0) }}
}}

public fn main(@Int -> @Int)
{_HEAD}{{
  let @Int = sum(build(100, Nil)) + sum(build(100, Nil)) \
+ sum(build(100, Nil));
  let @Array<Int> = array_map(array_range(0, {span}), \
fn(@Int -> @Int) effects(pure) {{ @Int.2 + 4 + 8 * @Int.0 }});
  let @Array<String> = array_map(array_range(0, 50), \
fn(@Int -> @String) effects(pure) {{ int_to_string(@Int.0) }});
  @Int.0 + array_length(@Array<Int>.0) + array_length(@Array<String>.0)
}}
"""


def test_repro_an_integer_equal_to_a_free_block_marks_nothing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An `Array<Int>` whose elements are the heap's body addresses, live
    while the program allocates, marks no free block: the base check
    refuses a free block whatever word names it.  Zeroing a freed block,
    at the sweep or on reuse, leaves this cell red, as it does the free
    blocks' links."""
    import re

    source = _integers_program(4096)
    wat = _wat(source, True, monkeypatch)
    found = re.search(r"\(global \$gc_heap_start i32 \(i32\.const (\d+)\)\)",
                      wat)
    assert found is not None
    run = _child(instrument(wat), "main", (int(found.group(1)),))
    assert run.value == 3 * 5050 + 4096 + 50, run
    assert run.counts["free_seen"] > 0, run.counts
    assert run.counts["free_marked"] == 0, run.counts
