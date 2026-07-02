"""WASI Preview 2 component emitter (#237).

``emit_wasi_component`` turns a compiled Vera module (``CompileResult``)
into a single WebAssembly *component* (text format) whose ``vera.*`` IO +
Random host imports are implemented on top of WASI 0.2 interfaces, so the
emitted artifact runs under any wasip2 host (stock ``wasmtime run``,
wasmtime-py ``component.Linker.add_wasip2()``) with no Vera-specific host
bindings.

Two worlds share this machinery (the ``world=`` parameter):

- ``"cli"`` (default): exports ``wasi:cli/run@0.2.0`` around ``main`` —
  the shipped #237 behavior, byte-identical to before the server world
  existed (pinned by tests).
- ``"server"`` (Stage D): exports ``wasi:http/incoming-handler@0.2.0``
  around the program's public ``handle(Request -> Response)`` so the
  artifact serves HTTP under stock ``wasmtime serve`` with no flags —
  see the Server world section below.

Topology (from the #237 design study, adapted — see PR notes):

    MAIN     — the ordinary Vera core module, post-processed textually:
               each ``(import "vera" "op" ...)`` becomes a same-named
               ``call_indirect`` shim through a 16-slot (cli) / 32-slot
               (server) funcref dispatch table that MAIN itself defines
               and exports (defined after the closure table, so closure
               call sites keep table 0); plus a GC-exempt scratch arena,
               ``cabi_realloc``, and (cli world) the ``__wasi_run``
               entry wrapper.
    LOWERS   — ``canon lower`` of the WASI imports against MAIN's
               memory + realloc (which therefore must come first).
    ADAPTER  — implements every op with the exact ``vera.*`` core
               signature and plants itself into the dispatch table via
               active elem segments at instantiation time — strictly
               before any lifted export can run.

The instantiation order MAIN -> lowers -> ADAPTER is a strict DAG (the
component model forbids instantiation cycles); table slots are only read
at run time.

The scratch arena lives *below* ``gc_heap_start`` so the mark-sweep GC
never scans or sweeps it: host-written data (``cabi_realloc`` results,
retptr scratch) needs no rooting, and repeated realloc calls within one
lowered call cannot be invalidated by a collection (the #593/#695 UAF
class, host-side).  Data crossing back into Vera is copied into GC-heap
blocks with WAT-level shadow-stack rooting mirroring
``vera/runtime/heap.py``.

Import spellings and both entry lifts were validated against wasmtime-py
45.0.0 (``Component`` parse + ``Linker.add_wasip2()`` instantiation) by
the #237 design study; note ``quota`` (not ``disk-quota``) in the
filesystem error-code enum.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera.codegen.api import CompileResult
    from vera.codegen.memory import ConstructorLayout


# =====================================================================
# Constants
# =====================================================================

#: Size of the GC-exempt scratch arena in MAIN linear memory.
_ARENA_SIZE = 65536

#: Retptr slab: fixed scratch slots at the base of the arena for the
#: fixed-size canonical-ABI return areas.  Offsets are relative to
#: ``arena_base`` (8-aligned), sized per the flattening table of the
#: design study §3.
_SLAB: dict[str, int] = {
    "bwf": 0,      # 12 B — blocking-write-and-flush result
    "read": 16,    # 12 B — blocking-read result
    "open": 32,    # 8 B  — descriptor.open-at result
    "stream": 40,  # 8 B  — read/write-via-stream result
    "now": 48,     # 16 B — wall-clock datetime record (8-aligned)
    "dbg": 64,     # 8 B  — error.to-debug-string result
    "env": 80,     # 8 B  — get-environment list header
    "args": 88,    # 8 B  — get-arguments list header
    "dirs": 96,    # 8 B  — get-directories list header
}
_SLAB_SIZE = 128

#: wasi:filesystem/types error-code enum cases, ordinal = index.
#: Case 6 is ``quota`` NOT ``disk-quota`` — pinned by the design study's
#: live ``add_wasip2`` instantiation check.
_ERRNO_NAMES: tuple[str, ...] = (
    "access", "would-block", "already", "bad-descriptor", "busy",
    "deadlock", "quota", "exist", "file-too-large",
    "illegal-byte-sequence", "in-progress", "interrupted", "invalid",
    "io", "is-directory", "loop", "too-many-links", "message-size",
    "name-too-long", "no-device", "no-entry", "no-lock",
    "insufficient-memory", "insufficient-space", "not-directory",
    "not-empty", "not-recoverable", "unsupported", "no-tty",
    "no-such-device", "overflow", "not-permitted", "pipe", "read-only",
    "invalid-seek", "text-file-busy", "cross-device",
)


# =====================================================================
# Per-op specification
# =====================================================================

@dataclass(frozen=True)
class _OpSpec:
    """One ``vera.*`` op: dispatch slot, core signature, WASI needs."""

    slot: int
    params: str            # space-separated core param types ("" = none)
    results: str           # space-separated core result types
    ifaces: frozenset[str] = field(default_factory=frozenset)
    lowers: frozenset[str] = field(default_factory=frozenset)
    drops: frozenset[str] = field(default_factory=frozenset)
    needs_alloc: bool = False


def _op(
    slot: int,
    params: str,
    results: str,
    ifaces: tuple[str, ...] = (),
    lowers: tuple[str, ...] = (),
    drops: tuple[str, ...] = (),
    needs_alloc: bool = False,
) -> _OpSpec:
    return _OpSpec(
        slot, params, results,
        frozenset(ifaces), frozenset(lowers), frozenset(drops),
        needs_alloc,
    )


#: Slot table.  Signatures mirror ``vera/codegen/assembly.py``
#: (`_IO_IMPORTS` + the Random block + contract_fail/overflow_trap) and
#: are cross-checked against the parsed import lines at emit time.
_OPS: dict[str, _OpSpec] = {
    "print": _op(
        0, "i32 i32", "",
        ("io/error", "io/streams", "cli/stdout"),
        ("get-stdout", "bwf"), ("error",),
    ),
    "stderr": _op(
        1, "i32 i32", "",
        ("io/error", "io/streams", "cli/stderr"),
        ("get-stderr", "bwf"), ("error",),
    ),
    "read_line": _op(
        2, "", "i32 i32",
        ("io/error", "io/streams", "cli/stdin"),
        ("get-stdin", "bread"), ("error",), needs_alloc=True,
    ),
    "read_char": _op(
        3, "", "i32",
        ("io/error", "io/streams", "cli/stdin"),
        ("get-stdin", "bread"), ("error",), needs_alloc=True,
    ),
    "read_file": _op(
        4, "i32 i32", "i32",
        ("io/error", "io/streams", "filesystem/types",
         "filesystem/preopens"),
        ("get-directories", "open-at", "read-via", "bread", "err-dbg"),
        ("error", "istream", "desc"), needs_alloc=True,
    ),
    "write_file": _op(
        5, "i32 i32 i32 i32", "i32",
        ("io/error", "io/streams", "filesystem/types",
         "filesystem/preopens"),
        ("get-directories", "open-at", "write-via", "bwf", "err-dbg"),
        ("error", "ostream", "desc"), needs_alloc=True,
    ),
    "args": _op(
        6, "", "i32 i32",
        ("cli/environment",), ("get-arguments",), (), needs_alloc=True,
    ),
    "get_env": _op(
        7, "i32 i32", "i32",
        ("cli/environment",), ("get-environment",), (), needs_alloc=True,
    ),
    "time": _op(8, "", "i64", ("clocks/wall-clock",), ("now",)),
    "sleep": _op(
        9, "i64", "",
        ("io/poll", "clocks/monotonic-clock"),
        ("subscribe-duration", "block"), ("pollable",),
    ),
    "exit": _op(10, "i64", "", ("cli/exit",), ("exit",)),
    "random_int": _op(11, "i64 i64", "i64", ("random/random",), ("rand64",)),
    "random_float": _op(12, "", "f64", ("random/random",), ("rand64",)),
    "random_bool": _op(13, "", "i32", ("random/random",), ("rand64",)),
    "contract_fail": _op(
        14, "i32 i32", "",
        ("io/error", "io/streams", "cli/stderr"),
        ("get-stderr", "bwf"), ("error",),
    ),
    "overflow_trap": _op(15, "", ""),
}

_ALLOC_OPS = frozenset(n for n, s in _OPS.items() if s.needs_alloc)


# =====================================================================
# WASI interface imports (proven spellings, design study §2)
# =====================================================================

#: Emission order (respects alias dependencies between interfaces).
_IFACE_ORDER: tuple[str, ...] = (
    "io/error", "io/poll", "io/streams", "cli/stdout", "cli/stderr",
    "cli/stdin", "cli/environment", "cli/exit", "clocks/wall-clock",
    "clocks/monotonic-clock", "random/random", "filesystem/types",
    "filesystem/preopens",
)

#: Interface -> interfaces it aliases types from (transitive closure is
#: applied at emit time).
_IFACE_DEPS: dict[str, tuple[str, ...]] = {
    "io/streams": ("io/error",),
    "cli/stdout": ("io/streams",),
    "cli/stderr": ("io/streams",),
    "cli/stdin": ("io/streams",),
    "filesystem/types": ("io/streams",),
    "filesystem/preopens": ("filesystem/types",),
    "clocks/monotonic-clock": ("io/poll",),
}

_IFACES: dict[str, str] = {
    "io/error": (
        '  (import "wasi:io/error@0.2.0" (instance $io_error\n'
        '    (export "error" (type $error (sub resource)))\n'
        '    (export "[method]error.to-debug-string" (func\n'
        '      (param "self" (borrow $error)) (result string)))))\n'
        '  (alias export $io_error "error" (type $ERR))'
    ),
    "io/poll": (
        '  (import "wasi:io/poll@0.2.0" (instance $poll\n'
        '    (export "pollable" (type $pollable (sub resource)))\n'
        '    (export "[method]pollable.block" (func\n'
        '      (param "self" (borrow $pollable))))))\n'
        '  (alias export $poll "pollable" (type $PL))'
    ),
    "io/streams": (
        '  (import "wasi:io/streams@0.2.0" (instance $streams\n'
        '    (alias outer $C $ERR (type $err0))\n'
        '    (export "input-stream" (type $istream (sub resource)))\n'
        '    (export "output-stream" (type $ostream (sub resource)))\n'
        '    (type $stream-error\' (variant\n'
        '      (case "last-operation-failed" (own $err0))\n'
        '      (case "closed")))\n'
        '    (export "stream-error" (type $stream-error'
        ' (eq $stream-error\')))\n'
        '    (export "[method]output-stream.blocking-write-and-flush"'
        ' (func\n'
        '      (param "self" (borrow $ostream))\n'
        '      (param "contents" (list u8))\n'
        '      (result (result (error $stream-error)))))\n'
        '    (export "[method]input-stream.blocking-read" (func\n'
        '      (param "self" (borrow $istream))\n'
        '      (param "len" u64)\n'
        '      (result (result (list u8) (error $stream-error)))))))\n'
        '  (alias export $streams "output-stream" (type $OS))\n'
        '  (alias export $streams "input-stream" (type $IS))'
    ),
    "cli/stdout": (
        '  (import "wasi:cli/stdout@0.2.0" (instance $stdout\n'
        '    (alias outer $C $OS (type $os))\n'
        '    (export "get-stdout" (func (result (own $os))))))'
    ),
    "cli/stderr": (
        '  (import "wasi:cli/stderr@0.2.0" (instance $stderri\n'
        '    (alias outer $C $OS (type $os))\n'
        '    (export "get-stderr" (func (result (own $os))))))'
    ),
    "cli/stdin": (
        '  (import "wasi:cli/stdin@0.2.0" (instance $stdini\n'
        '    (alias outer $C $IS (type $is))\n'
        '    (export "get-stdin" (func (result (own $is))))))'
    ),
    "cli/environment": (
        '  (import "wasi:cli/environment@0.2.0" (instance $environ\n'
        '    (export "get-environment" (func\n'
        '      (result (list (tuple string string)))))\n'
        '    (export "get-arguments" (func (result (list string))))))'
    ),
    "cli/exit": (
        '  (import "wasi:cli/exit@0.2.0" (instance $exiti\n'
        '    (export "exit" (func (param "status" (result))))))'
    ),
    "clocks/wall-clock": (
        '  (import "wasi:clocks/wall-clock@0.2.0" (instance $wall\n'
        '    (type $datetime\' (record (field "seconds" u64)'
        ' (field "nanoseconds" u32)))\n'
        '    (export "datetime" (type $datetime (eq $datetime\')))\n'
        '    (export "now" (func (result $datetime)))))'
    ),
    "clocks/monotonic-clock": (
        '  (import "wasi:clocks/monotonic-clock@0.2.0" (instance $mono\n'
        '    (alias outer $C $PL (type $pl))\n'
        '    (export "subscribe-duration" (func\n'
        '      (param "when" u64) (result (own $pl))))))'
    ),
    "random/random": (
        '  (import "wasi:random/random@0.2.0" (instance $random\n'
        '    (export "get-random-u64" (func (result u64)))))'
    ),
    "filesystem/types": (
        '  (import "wasi:filesystem/types@0.2.0" (instance $fstypes\n'
        '    (alias outer $C $IS (type $is))\n'
        '    (alias outer $C $OS (type $os))\n'
        '    (export "descriptor" (type $descriptor (sub resource)))\n'
        '    (type $error-code\' (enum\n'
        '      "access" "would-block" "already" "bad-descriptor" "busy"'
        ' "deadlock"\n'
        '      "quota"\n'
        '      "exist" "file-too-large" "illegal-byte-sequence"\n'
        '      "in-progress" "interrupted" "invalid" "io" "is-directory"'
        ' "loop"\n'
        '      "too-many-links" "message-size" "name-too-long"'
        ' "no-device"\n'
        '      "no-entry" "no-lock" "insufficient-memory"'
        ' "insufficient-space"\n'
        '      "not-directory" "not-empty" "not-recoverable"'
        ' "unsupported"\n'
        '      "no-tty" "no-such-device" "overflow" "not-permitted"'
        ' "pipe"\n'
        '      "read-only" "invalid-seek" "text-file-busy"'
        ' "cross-device"))\n'
        '    (export "error-code" (type $error-code (eq $error-code\')))\n'
        '    (type $path-flags\' (flags "symlink-follow"))\n'
        '    (export "path-flags" (type $path-flags (eq $path-flags\')))\n'
        '    (type $open-flags\' (flags "create" "directory" "exclusive"'
        ' "truncate"))\n'
        '    (export "open-flags" (type $open-flags (eq $open-flags\')))\n'
        '    (type $descriptor-flags\' (flags "read" "write"'
        ' "file-integrity-sync"\n'
        '      "data-integrity-sync" "requested-write-sync"'
        ' "mutate-directory"))\n'
        '    (export "descriptor-flags" (type $descriptor-flags'
        ' (eq $descriptor-flags\')))\n'
        '    (export "[method]descriptor.open-at" (func\n'
        '      (param "self" (borrow $descriptor))\n'
        '      (param "path-flags" $path-flags)\n'
        '      (param "path" string)\n'
        '      (param "open-flags" $open-flags)\n'
        '      (param "flags" $descriptor-flags)\n'
        '      (result (result (own $descriptor) (error $error-code)))))\n'
        '    (export "[method]descriptor.read-via-stream" (func\n'
        '      (param "self" (borrow $descriptor))\n'
        '      (param "offset" u64)\n'
        '      (result (result (own $is) (error $error-code)))))\n'
        '    (export "[method]descriptor.write-via-stream" (func\n'
        '      (param "self" (borrow $descriptor))\n'
        '      (param "offset" u64)\n'
        '      (result (result (own $os) (error $error-code)))))))\n'
        '  (alias export $fstypes "descriptor" (type $DESC))'
    ),
    "filesystem/preopens": (
        '  (import "wasi:filesystem/preopens@0.2.0" (instance $preopens\n'
        '    (alias outer $C $DESC (type $d))\n'
        '    (export "get-directories" (func\n'
        '      (result (list (tuple (own $d) string)))))))'
    ),
}


# =====================================================================
# Canon lowers + resource drops
# =====================================================================

#: key -> (component-level definition, adapter import decl,
#:         with-instance export line)
_LOWERS: dict[str, tuple[str, str, str]] = {
    "get-stdout": (
        '  (core func $l_get_stdout'
        ' (canon lower (func $stdout "get-stdout")))',
        '  (import "wasi" "get-stdout" (func $l_get_stdout (result i32)))',
        '      (export "get-stdout" (func $l_get_stdout))',
    ),
    "get-stderr": (
        '  (core func $l_get_stderr'
        ' (canon lower (func $stderri "get-stderr")))',
        '  (import "wasi" "get-stderr" (func $l_get_stderr (result i32)))',
        '      (export "get-stderr" (func $l_get_stderr))',
    ),
    "get-stdin": (
        '  (core func $l_get_stdin'
        ' (canon lower (func $stdini "get-stdin")))',
        '  (import "wasi" "get-stdin" (func $l_get_stdin (result i32)))',
        '      (export "get-stdin" (func $l_get_stdin))',
    ),
    "bwf": (
        '  (core func $l_bwf (canon lower\n'
        '    (func $streams'
        ' "[method]output-stream.blocking-write-and-flush")\n'
        '    (memory $mem)))',
        '  (import "wasi" "bwf" (func $l_bwf (param i32 i32 i32 i32)))',
        '      (export "bwf" (func $l_bwf))',
    ),
    "bread": (
        '  (core func $l_bread (canon lower\n'
        '    (func $streams "[method]input-stream.blocking-read")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "bread" (func $l_bread (param i32 i64 i32)))',
        '      (export "bread" (func $l_bread))',
    ),
    "err-dbg": (
        '  (core func $l_err_dbg (canon lower\n'
        '    (func $io_error "[method]error.to-debug-string")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "err-dbg" (func $l_err_dbg (param i32 i32)))',
        '      (export "err-dbg" (func $l_err_dbg))',
    ),
    "block": (
        '  (core func $l_block'
        ' (canon lower (func $poll "[method]pollable.block")))',
        '  (import "wasi" "block" (func $l_block (param i32)))',
        '      (export "block" (func $l_block))',
    ),
    "get-environment": (
        '  (core func $l_get_env (canon lower\n'
        '    (func $environ "get-environment")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "get-environment" (func $l_get_env (param i32)))',
        '      (export "get-environment" (func $l_get_env))',
    ),
    "get-arguments": (
        '  (core func $l_get_args (canon lower\n'
        '    (func $environ "get-arguments")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "get-arguments" (func $l_get_args (param i32)))',
        '      (export "get-arguments" (func $l_get_args))',
    ),
    "exit": (
        '  (core func $l_exit (canon lower (func $exiti "exit")))',
        '  (import "wasi" "exit" (func $l_exit (param i32)))',
        '      (export "exit" (func $l_exit))',
    ),
    "get-directories": (
        '  (core func $l_get_dirs (canon lower\n'
        '    (func $preopens "get-directories")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "get-directories" (func $l_get_dirs (param i32)))',
        '      (export "get-directories" (func $l_get_dirs))',
    ),
    "open-at": (
        '  (core func $l_open_at (canon lower\n'
        '    (func $fstypes "[method]descriptor.open-at")\n'
        '    (memory $mem)))',
        '  (import "wasi" "open-at"'
        ' (func $l_open_at (param i32 i32 i32 i32 i32 i32 i32)))',
        '      (export "open-at" (func $l_open_at))',
    ),
    "read-via": (
        '  (core func $l_read_via (canon lower\n'
        '    (func $fstypes "[method]descriptor.read-via-stream")\n'
        '    (memory $mem)))',
        '  (import "wasi" "read-via" (func $l_read_via (param i32 i64 i32)))',
        '      (export "read-via" (func $l_read_via))',
    ),
    "write-via": (
        '  (core func $l_write_via (canon lower\n'
        '    (func $fstypes "[method]descriptor.write-via-stream")\n'
        '    (memory $mem)))',
        '  (import "wasi" "write-via"'
        ' (func $l_write_via (param i32 i64 i32)))',
        '      (export "write-via" (func $l_write_via))',
    ),
    "now": (
        '  (core func $l_now'
        ' (canon lower (func $wall "now") (memory $mem)))',
        '  (import "wasi" "now" (func $l_now (param i32)))',
        '      (export "now" (func $l_now))',
    ),
    "subscribe-duration": (
        '  (core func $l_subdur'
        ' (canon lower (func $mono "subscribe-duration")))',
        '  (import "wasi" "subscribe-duration"'
        ' (func $l_subdur (param i64) (result i32)))',
        '      (export "subscribe-duration" (func $l_subdur))',
    ),
    "rand64": (
        '  (core func $l_rand64'
        ' (canon lower (func $random "get-random-u64")))',
        '  (import "wasi" "rand64" (func $l_rand64 (result i64)))',
        '      (export "rand64" (func $l_rand64))',
    ),
}

_DROPS: dict[str, tuple[str, str, str]] = {
    "error": (
        '  (core func $drop_err (canon resource.drop $ERR))',
        '  (import "wasi" "drop-error" (func $drop_err (param i32)))',
        '      (export "drop-error" (func $drop_err))',
    ),
    "pollable": (
        '  (core func $drop_poll (canon resource.drop $PL))',
        '  (import "wasi" "drop-pollable" (func $drop_poll (param i32)))',
        '      (export "drop-pollable" (func $drop_poll))',
    ),
    "istream": (
        '  (core func $drop_istream (canon resource.drop $IS))',
        '  (import "wasi" "drop-istream" (func $drop_istream (param i32)))',
        '      (export "drop-istream" (func $drop_istream))',
    ),
    "ostream": (
        '  (core func $drop_ostream (canon resource.drop $OS))',
        '  (import "wasi" "drop-ostream" (func $drop_ostream (param i32)))',
        '      (export "drop-ostream" (func $drop_ostream))',
    ),
    "desc": (
        '  (core func $drop_desc (canon resource.drop $DESC))',
        '  (import "wasi" "drop-desc" (func $drop_desc (param i32)))',
        '      (export "drop-desc" (func $drop_desc))',
    ),
}


# =====================================================================
# Family gate
# =====================================================================

#: (family name, CompileResult attribute) for every host family the
#: wasi-p2 target does NOT support in v1.  Kept in lockstep with the
#: ``*_ops_used`` fields of ``CompileResult`` — anything not IO/Random.
_UNSUPPORTED_FAMILIES: tuple[tuple[str, str], ...] = (
    ("http", "http_ops_used"),
    ("inference", "inference_ops_used"),
    ("md", "md_ops_used"),
    ("regex", "regex_ops_used"),
    ("map", "map_ops_used"),
    ("set", "set_ops_used"),
    ("decimal", "decimal_ops_used"),
    ("json", "json_ops_used"),
    ("html", "html_ops_used"),
    ("math", "math_ops_used"),
    ("async", "async_ops_used"),
)


def _gate_families(result: CompileResult) -> None:
    """Reject programs using host families the wasi-p2 target lacks.

    Never a silent fallback: the diagnostic names every offending
    family so the CLI layer can present it verbatim.
    """
    offending: list[str] = []
    for family, attr in _UNSUPPORTED_FAMILIES:
        ops = getattr(result, attr)
        if ops:
            offending.append(f"{family} ({', '.join(sorted(ops))})")
    if result.state_types:
        types = ", ".join(sorted(t for t, _ in result.state_types))
        offending.append(f"state ({types})")
    if offending:
        raise ValueError(
            "--target wasi-p2 does not support the following host "
            f"famil{'ies' if len(offending) > 1 else 'y'}: "
            f"{'; '.join(offending)}. Supported families: IO, Random."
        )


# =====================================================================
# MAIN-module WAT parsing helpers
# =====================================================================

_IMPORT_RE = re.compile(
    r'^  \(import "vera" "([a-z_0-9]+)" \(func \$vera\.[a-z_0-9]+'
    r'((?: \(param(?: (?:i32|i64|f32|f64))+\))?'
    r'(?: \(result(?: (?:i32|i64|f32|f64))+\))?)\)\)$'
)
_MEMORY_RE = re.compile(r'^  \(memory \(export "memory"\) (\d+)\)$')
_HEAP_PTR_RE = re.compile(
    r'^  \(global \$heap_ptr \(export "heap_ptr"\) '
    r'\(mut i32\) \(i32\.const (\d+)\)\)$'
)
_GC_HEAP_START_RE = re.compile(
    r'^  \(global \$gc_heap_start i32 \(i32\.const (\d+)\)\)$'
)
_DATA_RE = re.compile(r'^  \(data \(i32\.const (\d+)\) "(.*)"\)$')
_MAIN_FN_RE = re.compile(r'^  \(func \$main \(export "main"\)(.*)$')


def _expected_sig(spec: _OpSpec) -> str:
    """Signature text as it appears in the ``vera.*`` import decl."""
    sig = ""
    if spec.params:
        sig += f" (param {spec.params})"
    if spec.results:
        sig += f" (result {spec.results})"
    return sig


def _wat_literal_byte_len(escaped: str) -> int:
    """Byte length of a WAT data-segment string literal.

    Mirrors ``CodeGenerator._escape_wat_string``: every escape
    (``\\\\``, ``\\n``, ``\\t``, ``\\XX`` hex) encodes exactly one byte.
    """
    n = 0
    i = 0
    while i < len(escaped):
        if escaped[i] == "\\":
            i += 2 if escaped[i + 1] in ("\\", "n", "t") else 3
        else:
            i += 1
        n += 1
    return n


def _wat_bytes(data: bytes) -> str:
    """Escape raw bytes for a WAT data-segment string literal."""
    out: list[str] = []
    for b in data:
        ch = chr(b)
        if ch == '"':
            out.append("\\22")
        elif ch == "\\":
            out.append("\\\\")
        elif 0x20 <= b < 0x7F:
            out.append(ch)
        else:
            out.append(f"\\{b:02x}")
    return "".join(out)


# =====================================================================
# Layout
# =====================================================================

@dataclass
class _Layout:
    """Numeric memory layout shared between MAIN and the adapter."""

    arena_base: int
    bump_start: int
    arena_end: int
    has_alloc: bool
    statics: dict[str, tuple[int, int]]
    errtab: int                      # 0 when no filesystem ops
    main_results: tuple[str, ...]    # core result types of $main
    #: Retptr-slab offset table.  The cli world uses the module-level
    #: ``_SLAB``; the server world substitutes ``_SERVER_SLAB`` (the
    #: §2.2 request/response slots) without disturbing cli offsets.
    slab_table: dict[str, int] = field(default_factory=lambda: _SLAB)

    def slab(self, key: str) -> int:
        return self.arena_base + self.slab_table[key]


def _build_statics(
    used: set[str], arena_base: int,
) -> tuple[list[str], dict[str, tuple[int, int]], int, int]:
    """Compute the adapter's static-string region.

    Returns (data-segment WAT lines, refs {key: (ptr, len)},
    errtab address or 0, bump_start).  The region sits between the
    retptr slab and the bump region; ``arena_reset`` points the bump
    pointer past it, so statics are immortal and GC-exempt — ``Err``
    ADTs reference them directly with no copy.
    """
    fs = bool(used & {"read_file", "write_file"})
    msgs: dict[str, str] = {}
    if "read_char" in used:
        msgs["eof"] = "EOF"
    if fs:
        msgs["nopre"] = "no preopened directories"
        msgs["unk"] = "unknown filesystem error"
    if "write_file" in used:
        msgs["closed"] = "stream closed"

    cursor = arena_base + _SLAB_SIZE
    errtab = 0
    segments: list[str] = []
    refs: dict[str, tuple[int, int]] = {}

    blob = bytearray()
    blob_base = cursor
    if fs:
        errtab = cursor
        blob_base = cursor + 8 * len(_ERRNO_NAMES)

    names_blob = bytearray()
    name_refs: list[tuple[int, int]] = []
    for name in _ERRNO_NAMES if fs else ():
        encoded = name.encode("ascii")
        name_refs.append((blob_base + len(names_blob), len(encoded)))
        names_blob += encoded
    for key, text in msgs.items():
        encoded = text.encode("ascii")
        refs[key] = (blob_base + len(names_blob), len(encoded))
        names_blob += encoded

    if fs:
        table = bytearray()
        for ptr, length in name_refs:
            table += ptr.to_bytes(4, "little")
            table += length.to_bytes(4, "little")
        blob += table
    blob += names_blob

    if blob:
        segments.append(
            f'  (data (i32.const {cursor}) "{_wat_bytes(bytes(blob))}")'
        )
    bump_start = (cursor + len(blob) + 7) & ~7
    return segments, refs, errtab, bump_start


# =====================================================================
# MAIN-module transformation
# =====================================================================

def _module_body(wat: str) -> list[str]:
    """Strip the outer ``(module`` / ``)`` lines, validating the shape."""
    lines = wat.split("\n")
    if lines[0] != "(module" or lines[-1] != ")":
        raise RuntimeError(
            "unexpected core-module WAT shape from the Vera code "
            "generator; the wasi-p2 post-processor needs updating"
        )
    return lines[1:-1]


def _check_reserved_idents(body: list[str]) -> None:
    """Reserved-identifier collision check (shared by both worlds).

    Scan only non-data lines (a data segment's payload is a string
    literal — a Vera program printing "$wasi_tbl" is not a collision),
    and require an identifier boundary after each exact marker so a
    LONGER identifier like `$wasi_tblish` is not a collision either
    (CR review, PR #849).  `$wasi_sig_` is the one deliberate prefix
    family (the shim type names `$wasi_sig_<op>`).
    """
    ident_lines = "\n".join(
        line for line in body if not line.lstrip().startswith("(data")
    )
    for marker, is_prefix in (
        ("$wasi_tbl", False), ("$wasi_arena_ptr", False),
        ("$cabi_realloc", False), ("$__wasi_run", False),
        ("$wasi_sig_", True),
    ):
        pattern = re.escape(marker)
        if not is_prefix:
            # WAT identifiers extend through [0-9A-Za-z_$.] in the
            # names the Vera code generator emits; anything else
            # (whitespace, parens, quote, end) terminates the id.
            pattern += r"(?![0-9A-Za-z_$.])"
        if re.search(pattern, ident_lines):
            raise ValueError(
                f"program defines the reserved identifier {marker!r}; "
                "--target wasi-p2 cannot compile it"
            )


def _transform_main(
    wat: str, used: dict[str, str],
) -> tuple[list[str], _Layout]:
    """Post-process the compiled core module for the component.

    Replaces every ``(import "vera" ...)`` with a same-named
    ``call_indirect`` shim, defines + exports the dispatch table,
    inserts the GC-exempt arena (shifting ``gc_heap_start`` /
    ``heap_ptr`` up when the GC runtime is present), raises the memory
    min so the arena is addressable at instantiation, and appends
    ``cabi_realloc`` + the ``__wasi_run`` wrapper.

    Returns the module *fields* (no outer ``(module`` / ``)``) and the
    computed layout.
    """
    body = _module_body(wat)
    _check_reserved_idents(body)

    kept: list[str] = []
    mem_idx = -1
    mem_min = 0
    heap_ptr_idx = -1
    gc_start_idx = -1
    gc_start_val = -1
    data_end = 0
    main_fn_line = ""
    for line in body:
        if _IMPORT_RE.match(line):
            continue  # replaced by shims below
        if line.startswith('  (import "vera"'):
            raise RuntimeError(
                f"unrecognized vera host import in WAT: {line.strip()} "
                "— the wasi-p2 emitter op table is out of sync with "
                "vera/codegen/assembly.py"
            )
        m = _MEMORY_RE.match(line)
        if m:
            mem_idx = len(kept)
            mem_min = int(m.group(1))
        m = _HEAP_PTR_RE.match(line)
        if m:
            heap_ptr_idx = len(kept)
        m = _GC_HEAP_START_RE.match(line)
        if m:
            gc_start_idx = len(kept)
            gc_start_val = int(m.group(1))
        m = _DATA_RE.match(line)
        if m:
            end = int(m.group(1)) + _wat_literal_byte_len(m.group(2))
            data_end = max(data_end, end)
        m = _MAIN_FN_RE.match(line)
        if m:
            main_fn_line = line
        if "$gc_wrap_base" in line:
            raise RuntimeError(
                "wrap-table region present despite the family gate — "
                "wasi-p2 arena layout does not handle it"
            )
        kept.append(line)

    # --- arena placement -------------------------------------------
    if gc_start_idx >= 0:
        arena_base = (gc_start_val + 7) & ~7
        new_start = arena_base + _ARENA_SIZE
        kept[heap_ptr_idx] = (
            f'  (global $heap_ptr (export "heap_ptr") '
            f"(mut i32) (i32.const {new_start}))"
        )
        kept[gc_start_idx] = (
            f"  (global $gc_heap_start i32 (i32.const {new_start}))"
        )
    else:
        arena_base = max(65536, (data_end + 65535) & ~65535)
    arena_end = arena_base + _ARENA_SIZE

    pages = (arena_end + 65535) // 65536
    if mem_idx >= 0:
        kept[mem_idx] = (
            f'  (memory (export "memory") {max(mem_min, pages)})'
        )
    else:
        kept.append(f'  (memory (export "memory") {pages})')

    # --- entry-point shape ------------------------------------------
    if not main_fn_line:
        raise ValueError(
            "--target wasi-p2 requires a public zero-argument `main` "
            "entry point"
        )
    if "(param" in main_fn_line:
        raise ValueError(
            "--target wasi-p2 requires `main` to take no parameters"
        )
    rm = re.search(
        r"\(result ((?:i32|i64|f32|f64)(?: (?:i32|i64|f32|f64))*)\)",
        main_fn_line,
    )
    main_results: tuple[str, ...] = (
        tuple(rm.group(1).split(" ")) if rm else ()
    )

    _segments, statics, errtab, bump_start = _build_statics(
        set(used), arena_base,
    )
    has_alloc = bool(set(used) & _ALLOC_OPS)
    layout = _Layout(
        arena_base=arena_base,
        bump_start=bump_start,
        arena_end=arena_end,
        has_alloc=has_alloc,
        statics=statics,
        errtab=errtab,
        main_results=main_results,
    )

    # --- appended machinery -----------------------------------------
    out = list(kept)
    out.append('  (table $wasi_tbl (export "wasi_tbl") 16 16 funcref)')
    out.append(
        f'  (global $wasi_arena_ptr (export "wasi_arena_ptr") '
        f"(mut i32) (i32.const {bump_start}))"
    )
    out.append(_emit_cabi_realloc(arena_end))
    for name in sorted(used, key=lambda n: _OPS[n].slot):
        out.append(_emit_shim(name, _OPS[name]))
    out.append(_emit_wasi_run(len(main_results)))
    return out, layout


def _emit_cabi_realloc(arena_end: int) -> str:
    """Bump allocator over the GC-exempt arena (design study §4.2).

    Lives in MAIN because the canon lowers reference it and MAIN is
    the only memory-owning instance that precedes them.  OOM (bump
    past the fixed arena) traps — the canonical ABI permits realloc
    to trap, and a clean ``unreachable`` beats silent corruption
    (wrap-table precedent, #573).
    """
    return (
        '  (func $cabi_realloc (export "cabi_realloc") '
        "(param $old i32) (param $old_size i32) "
        "(param $align i32) (param $new_size i32) (result i32)\n"
        "    (local $p i32)\n"
        "    global.get $wasi_arena_ptr\n"
        "    local.get $align\n"
        "    i32.add\n"
        "    i32.const 1\n"
        "    i32.sub\n"
        "    local.get $align\n"
        "    i32.const 1\n"
        "    i32.sub\n"
        "    i32.const -1\n"
        "    i32.xor\n"
        "    i32.and\n"
        "    local.set $p\n"
        "    local.get $p\n"
        "    local.get $new_size\n"
        "    i32.add\n"
        f"    i32.const {arena_end}\n"
        "    i32.gt_u\n"
        "    if\n"
        "      unreachable\n"
        "    end\n"
        "    local.get $p\n"
        "    local.get $new_size\n"
        "    i32.add\n"
        "    global.set $wasi_arena_ptr\n"
        "    local.get $old\n"
        "    if\n"
        "      local.get $p\n"
        "      local.get $old\n"
        "      local.get $old_size\n"
        "      memory.copy\n"
        "    end\n"
        "    local.get $p\n"
        "  )"
    )


def _emit_shim(name: str, spec: _OpSpec) -> str:
    """Same-named ``call_indirect`` shim replacing a ``vera.*`` import.

    The shim keeps the ``$vera.<op>`` identifier so every call site in
    the compiled module is untouched; the explicit ``$wasi_tbl`` table
    reference keeps closure ``call_indirect`` sites (implicit table 0)
    unaffected.
    """
    sig = _expected_sig(spec)
    forwards = "".join(
        f"    local.get {i}\n"
        for i in range(len(spec.params.split()) if spec.params else 0)
    )
    return (
        f"  (type $wasi_sig_{spec.slot} (func{sig}))\n"
        f"  (func $vera.{name}{sig}\n"
        f"{forwards}"
        f"    i32.const {spec.slot}\n"
        f"    call_indirect $wasi_tbl (type $wasi_sig_{spec.slot})\n"
        "  )"
    )


def _emit_wasi_run(n_results: int) -> str:
    """``wasi:cli/run`` core wrapper: call main, discard, report ok.

    A Vera ``main`` return value is not an exit status (that is
    ``IO.exit``'s job, matching ``vera run``), so the result is
    dropped and the run result-disc is always ok(0).
    """
    drops = "    drop\n" * n_results
    return (
        '  (func $__wasi_run (export "__wasi_run") (result i32)\n'
        "    call $main\n"
        f"{drops}"
        "    i32.const 0\n"
        "  )"
    )


# =====================================================================
# Adapter module
# =====================================================================

def _adapter_fields(used: set[str], lay: _Layout) -> list[str]:
    """Emit the adapter core module's fields for the used op set."""
    specs = {n: _OPS[n] for n in used}
    lowers = sorted(set().union(*(s.lowers for s in specs.values())))
    drops = sorted(set().union(*(s.drops for s in specs.values())))

    fields: list[str] = [
        '  (import "env" "memory" (memory 1))',
        '  (import "env" "tbl" (table 16 funcref))',
        '  (import "env" "arena_ptr" (global $arena_ptr (mut i32)))',
    ]
    if lay.has_alloc:
        fields += [
            '  (import "env" "alloc" (func $alloc (param i32) (result i32)))',
            '  (import "env" "gc_sp" (global $gc_sp (mut i32)))',
            '  (import "env" "gc_stack_limit" (global $gc_stack_limit i32))',
        ]
    for key in lowers:
        fields.append(_LOWERS[key][1])
    for key in drops:
        fields.append(_DROPS[key][1])

    # Cached process-lifetime std handles (never dropped).
    if "print" in used:
        fields.append("  (global $stdout_h (mut i32) (i32.const -1))")
    if used & {"stderr", "contract_fail"}:
        fields.append("  (global $stderr_h (mut i32) (i32.const -1))")
    if used & {"read_line", "read_char"}:
        fields.append("  (global $stdin_h (mut i32) (i32.const -1))")
    if used & {"read_file", "write_file"}:
        # -2 = not yet fetched; -1 = fetched, no preopens.  The fetched
        # descriptor is cached for the process lifetime — get-directories
        # returns a fresh OWNED descriptor per call, so re-fetching per
        # file op would leak one handle into the instance's resource
        # table on every IO.read_file/write_file (CR review, PR #849).
        fields.append("  (global $preopen_fd (mut i32) (i32.const -2))")

    segments, _refs, _errtab, _bump = _build_statics(used, lay.arena_base)
    fields += segments

    fields += _helper_funcs(used, lay)
    for name in sorted(used, key=lambda n: _OPS[n].slot):
        fields.append(_OP_EMITTERS[name](lay))
    for name in sorted(used, key=lambda n: _OPS[n].slot):
        fields.append(
            f"  (elem (i32.const {_OPS[name].slot}) func $op_{name})"
        )
    return fields


#: Adapter helper bodies shared VERBATIM by both worlds (any drift
#: would silently fork the GC-rooting discipline between them).
_SHADOW_PUSH_FN = (
    "  (func $shadow_push (param $v i32)\n"
    "    global.get $gc_sp\n"
    "    global.get $gc_stack_limit\n"
    "    i32.ge_u\n"
    "    if\n"
    "      unreachable\n"
    "    end\n"
    "    global.get $gc_sp\n"
    "    local.get $v\n"
    "    i32.store\n"
    "    global.get $gc_sp\n"
    "    i32.const 4\n"
    "    i32.add\n"
    "    global.set $gc_sp\n"
    "  )"
)
_SHADOW_POP_FN = (
    "  (func $shadow_pop_n (param $n i32)\n"
    "    global.get $gc_sp\n"
    "    local.get $n\n"
    "    i32.const 4\n"
    "    i32.mul\n"
    "    i32.sub\n"
    "    global.set $gc_sp\n"
    "  )"
)
_BYTES_EQ_FN = (
    "  (func $bytes_eq (param $a i32) (param $b i32) "
    "(param $n i32) (result i32)\n"
    "    (local $i i32)\n"
    "    block $ne\n"
    "    loop $cmp\n"
    "      local.get $i\n"
    "      local.get $n\n"
    "      i32.ge_u\n"
    "      if\n"
    "        i32.const 1\n"
    "        return\n"
    "      end\n"
    "      local.get $a\n"
    "      local.get $i\n"
    "      i32.add\n"
    "      i32.load8_u\n"
    "      local.get $b\n"
    "      local.get $i\n"
    "      i32.add\n"
    "      i32.load8_u\n"
    "      i32.ne\n"
    "      br_if $ne\n"
    "      local.get $i\n"
    "      i32.const 1\n"
    "      i32.add\n"
    "      local.set $i\n"
    "      br $cmp\n"
    "    end\n"
    "    end\n"
    "    i32.const 0\n"
    "  )"
)


def _helper_funcs(used: set[str], lay: _Layout) -> list[str]:
    """Shared adapter helpers, gated by the ops that need them."""
    out: list[str] = []
    fs = bool(used & {"read_file", "write_file"})
    needs_arena_reset = bool(used & _ALLOC_OPS)
    needs_write = bool(used & {"print", "stderr", "contract_fail",
                               "write_file"})

    if needs_arena_reset:
        out.append(
            "  (func $arena_reset\n"
            f"    i32.const {lay.bump_start}\n"
            "    global.set $arena_ptr\n"
            "  )"
        )
    if lay.has_alloc:
        # Mirrors helpers.gc_shadow_push / _ShadowGuard in
        # vera/runtime/heap.py: root GC pointers held only in adapter
        # locals across a subsequent $alloc (#593 class).
        out.append(_SHADOW_PUSH_FN)
        out.append(_SHADOW_POP_FN)
        # 12-byte {tag, ptr, len} Result/Option payload ADT, matching
        # vera/runtime/heap.py layouts.  The payload pointer is rooted
        # across the struct alloc; rooting a GC-exempt pointer (arena
        # static) is harmless — the conservative scan range-checks it.
        out.append(
            "  (func $mk_res_str (param $tag i32) (param $mp i32) "
            "(param $ml i32) (result i32)\n"
            "    (local $adt i32)\n"
            "    local.get $mp\n"
            "    if\n"
            "      local.get $mp\n"
            "      call $shadow_push\n"
            "    end\n"
            "    i32.const 12\n"
            "    call $alloc\n"
            "    local.set $adt\n"
            "    local.get $mp\n"
            "    if\n"
            "      i32.const 1\n"
            "      call $shadow_pop_n\n"
            "    end\n"
            "    local.get $adt\n"
            "    local.get $tag\n"
            "    i32.store\n"
            "    local.get $adt\n"
            "    local.get $mp\n"
            "    i32.store offset=4\n"
            "    local.get $adt\n"
            "    local.get $ml\n"
            "    i32.store offset=8\n"
            "    local.get $adt\n"
            "  )"
        )
        out.append(
            "  (func $mk_tag_only (param $tag i32) (result i32)\n"
            "    (local $adt i32)\n"
            "    i32.const 4\n"
            "    call $alloc\n"
            "    local.set $adt\n"
            "    local.get $adt\n"
            "    local.get $tag\n"
            "    i32.store\n"
            "    local.get $adt\n"
            "  )"
        )
    if "print" in used:
        out.append(_ensure_handle("stdout", "$l_get_stdout"))
    if used & {"stderr", "contract_fail"}:
        out.append(_ensure_handle("stderr", "$l_get_stderr"))
    if used & {"read_line", "read_char"}:
        out.append(_ensure_handle("stdin", "$l_get_stdin"))
    if needs_write:
        out.append(_write_or_trap(lay))
    if used & {"read_line", "read_char"}:
        out.append(_read_byte(lay))
    if "get_env" in used:
        out.append(_BYTES_EQ_FN)
    if fs:
        out.append(_get_preopen(lay))
        out.append(_strip_path())
        out.append(_errno_str(lay))
        out.append(_debug_string(lay))
    return out


def _ensure_handle(which: str, lower: str) -> str:
    return (
        f"  (func $ensure_{which}\n"
        f"    global.get ${which}_h\n"
        "    i32.const -1\n"
        "    i32.eq\n"
        "    if\n"
        f"      call {lower}\n"
        f"      global.set ${which}_h\n"
        "    end\n"
        "  )"
    )


def _write_or_trap(lay: _Layout) -> str:
    """Chunked blocking-write-and-flush loop (4096-byte host cap).

    For Vera's infallible output ops (print/stderr/contract_fail) a
    stream error traps; the owned error resource is dropped first so
    even the trap path leaks nothing.
    """
    bwf = lay.slab("bwf")
    return (
        "  (func $write_or_trap (param $h i32) (param $ptr i32) "
        "(param $len i32)\n"
        "    (local $n i32)\n"
        "    block $done\n"
        "    loop $chunk\n"
        "      local.get $len\n"
        "      i32.eqz\n"
        "      br_if $done\n"
        "      local.get $len\n"
        "      i32.const 4096\n"
        "      i32.lt_u\n"
        "      if (result i32)\n"
        "        local.get $len\n"
        "      else\n"
        "        i32.const 4096\n"
        "      end\n"
        "      local.set $n\n"
        "      local.get $h\n"
        "      local.get $ptr\n"
        "      local.get $n\n"
        f"      i32.const {bwf}\n"
        "      call $l_bwf\n"
        # Variant discriminants are u8 in the canonical-ABI memory
        # representation; a full i32.load would pick up stale slab
        # bytes as "discriminant" (found live: an EOF err(closed)
        # misread as last-operation-failed with a garbage handle).
        f"      i32.const {bwf}\n"
        "      i32.load8_u\n"
        "      if\n"
        f"        i32.const {bwf}\n"
        "        i32.load8_u offset=4\n"
        "        i32.eqz\n"
        "        if\n"
        f"          i32.const {bwf}\n"
        "          i32.load offset=8\n"
        "          call $drop_err\n"
        "        end\n"
        "        unreachable\n"
        "      end\n"
        "      local.get $ptr\n"
        "      local.get $n\n"
        "      i32.add\n"
        "      local.set $ptr\n"
        "      local.get $len\n"
        "      local.get $n\n"
        "      i32.sub\n"
        "      local.set $len\n"
        "      br $chunk\n"
        "    end\n"
        "    end\n"
        "  )"
    )


def _read_byte(lay: _Layout) -> str:
    """One byte from stdin via blocking-read; -1 = EOF (err(closed)).

    Reading one byte at a time means the adapter never over-reads
    bytes that belong to a later read_line/read_char — correct with
    zero persistent state (design study §5.6).  Callers reset the
    arena bump pointer between reads; each 1-byte list is consumed
    before the next request.
    """
    rp = lay.slab("read")
    return (
        "  (func $read_byte (result i32)\n"
        "    loop $rd\n"
        "      global.get $stdin_h\n"
        "      i64.const 1\n"
        f"      i32.const {rp}\n"
        "      call $l_bread\n"
        # u8 discriminant loads — see $write_or_trap.
        f"      i32.const {rp}\n"
        "      i32.load8_u\n"
        "      if\n"
        f"        i32.const {rp}\n"
        "        i32.load8_u offset=4\n"
        "        i32.const 1\n"
        "        i32.eq\n"
        "        if\n"
        "          i32.const -1\n"
        "          return\n"
        "        end\n"
        f"        i32.const {rp}\n"
        "        i32.load offset=8\n"
        "        call $drop_err\n"
        "        unreachable\n"
        "      end\n"
        f"      i32.const {rp}\n"
        "      i32.load offset=8\n"
        "      i32.eqz\n"
        "      br_if $rd\n"
        "    end\n"
        f"    i32.const {rp}\n"
        "    i32.load offset=4\n"
        "    i32.load8_u\n"
        "  )"
    )


def _get_preopen(lay: _Layout) -> str:
    """First preopened directory's descriptor handle, or -1.

    Fetched ONCE and cached in ``$preopen_fd`` (sentinel -2 =
    unfetched): every ``get-directories`` call returns a fresh OWNED
    descriptor list, so fetching per file op would leak one handle
    into the instance's resource table on every ``IO.read_file`` /
    ``write_file`` (CR review, PR #849).  The cached descriptor (and
    any extra preopens in the one fetched list) are process-lifetime
    resources, same as the cached std stream handles.  v1 uses the
    first preopen only (the runner preopens CWD at "/"); multi-preopen
    longest-prefix matching is a tracked follow-up.

    ``$arena_reset`` stays unconditional at the top — callers rely on
    it as their op-entry arena reset.
    """
    dirs = lay.slab("dirs")
    return (
        "  (func $get_preopen (result i32)\n"
        "    call $arena_reset\n"
        "    global.get $preopen_fd\n"
        "    i32.const -2\n"
        "    i32.ne\n"
        "    if\n"
        "      global.get $preopen_fd\n"
        "      return\n"
        "    end\n"
        f"    i32.const {dirs}\n"
        "    call $l_get_dirs\n"
        f"    i32.const {dirs}\n"
        "    i32.load offset=4\n"
        "    i32.eqz\n"
        "    if\n"
        "      i32.const -1\n"
        "      global.set $preopen_fd\n"
        "      i32.const -1\n"
        "      return\n"
        "    end\n"
        f"    i32.const {dirs}\n"
        "    i32.load\n"
        "    i32.load\n"
        "    global.set $preopen_fd\n"
        "    global.get $preopen_fd\n"
        "  )"
    )


def _strip_path() -> str:
    """Normalize a Vera path for open-at: strip leading '/' and './'."""
    phase_slash = (
        "    block $s{n}\n"
        "    loop $l{n}\n"
        "      local.get $l\n"
        "      i32.eqz\n"
        "      br_if $s{n}\n"
        "      local.get $p\n"
        "      i32.load8_u\n"
        "      i32.const 47\n"
        "      i32.ne\n"
        "      br_if $s{n}\n"
        "      local.get $p\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $p\n"
        "      local.get $l\n"
        "      i32.const 1\n"
        "      i32.sub\n"
        "      local.set $l\n"
        "      br $l{n}\n"
        "    end\n"
        "    end\n"
    )
    return (
        "  (func $strip_path (param $p i32) (param $l i32) "
        "(result i32 i32)\n"
        + phase_slash.format(n=1)
        + "    local.get $l\n"
        "    i32.const 2\n"
        "    i32.ge_u\n"
        "    if\n"
        "      local.get $p\n"
        "      i32.load8_u\n"
        "      i32.const 46\n"
        "      i32.eq\n"
        "      if\n"
        "        local.get $p\n"
        "        i32.load8_u offset=1\n"
        "        i32.const 47\n"
        "        i32.eq\n"
        "        if\n"
        "          local.get $p\n"
        "          i32.const 2\n"
        "          i32.add\n"
        "          local.set $p\n"
        "          local.get $l\n"
        "          i32.const 2\n"
        "          i32.sub\n"
        "          local.set $l\n"
        "        end\n"
        "      end\n"
        "    end\n"
        + phase_slash.format(n=2)
        + "    local.get $p\n"
        "    local.get $l\n"
        "  )"
    )


def _errno_str(lay: _Layout) -> str:
    """(ptr, len) of the errno name for a filesystem error ordinal."""
    unk_ptr, unk_len = lay.statics["unk"]
    return (
        "  (func $errno_str (param $e i32) (result i32 i32)\n"
        "    local.get $e\n"
        f"    i32.const {len(_ERRNO_NAMES)}\n"
        "    i32.ge_u\n"
        "    if\n"
        f"      i32.const {unk_ptr}\n"
        f"      i32.const {unk_len}\n"
        "      return\n"
        "    end\n"
        "    local.get $e\n"
        "    i32.const 3\n"
        "    i32.shl\n"
        f"    i32.const {lay.errtab}\n"
        "    i32.add\n"
        "    i32.load\n"
        "    local.get $e\n"
        "    i32.const 3\n"
        "    i32.shl\n"
        f"    i32.const {lay.errtab}\n"
        "    i32.add\n"
        "    i32.load offset=4\n"
        "  )"
    )


def _debug_string(lay: _Layout) -> str:
    """Host error text -> GC-heap string; drops the error resource."""
    dbg = lay.slab("dbg")
    return (
        "  (func $debug_string (param $h i32) (result i32 i32)\n"
        "    (local $p i32)\n"
        "    (local $l i32)\n"
        "    (local $gp i32)\n"
        "    local.get $h\n"
        f"    i32.const {dbg}\n"
        "    call $l_err_dbg\n"
        f"    i32.const {dbg}\n"
        "    i32.load\n"
        "    local.set $p\n"
        f"    i32.const {dbg}\n"
        "    i32.load offset=4\n"
        "    local.set $l\n"
        "    local.get $h\n"
        "    call $drop_err\n"
        "    local.get $l\n"
        "    i32.eqz\n"
        "    if\n"
        "      i32.const 0\n"
        "      i32.const 0\n"
        "      return\n"
        "    end\n"
        "    local.get $l\n"
        "    call $alloc\n"
        "    local.set $gp\n"
        "    local.get $gp\n"
        "    local.get $p\n"
        "    local.get $l\n"
        "    memory.copy\n"
        "    local.get $gp\n"
        "    local.get $l\n"
        "  )"
    )


# ---------------------------------------------------------------------
# Per-op adapter bodies
# ---------------------------------------------------------------------

def _op_print(lay: _Layout) -> str:
    return (
        "  (func $op_print (param $p i32) (param $l i32)\n"
        "    call $ensure_stdout\n"
        "    global.get $stdout_h\n"
        "    local.get $p\n"
        "    local.get $l\n"
        "    call $write_or_trap\n"
        "  )"
    )


def _op_stderr(lay: _Layout) -> str:
    return (
        "  (func $op_stderr (param $p i32) (param $l i32)\n"
        "    call $ensure_stderr\n"
        "    global.get $stderr_h\n"
        "    local.get $p\n"
        "    local.get $l\n"
        "    call $write_or_trap\n"
        "  )"
    )


def _op_contract_fail(lay: _Layout) -> str:
    # Best-effort violation message to stderr, then trap.  The
    # component path loses structured trap frames (spike check 5);
    # the stderr write preserves the message for diagnostics.
    return (
        "  (func $op_contract_fail (param $p i32) (param $l i32)\n"
        "    call $ensure_stderr\n"
        "    global.get $stderr_h\n"
        "    local.get $p\n"
        "    local.get $l\n"
        "    call $write_or_trap\n"
        "    unreachable\n"
        "  )"
    )


def _op_overflow_trap(lay: _Layout) -> str:
    return (
        "  (func $op_overflow_trap\n"
        "    unreachable\n"
        "  )"
    )


def _op_time(lay: _Layout) -> str:
    now = lay.slab("now")
    return (
        "  (func $op_time (result i64)\n"
        f"    i32.const {now}\n"
        "    call $l_now\n"
        f"    i32.const {now}\n"
        "    i64.load\n"
        "    i64.const 1000\n"
        "    i64.mul\n"
        f"    i32.const {now}\n"
        "    i64.load32_u offset=8\n"
        "    i64.const 1000000\n"
        "    i64.div_u\n"
        "    i64.add\n"
        "  )"
    )


def _op_sleep(lay: _Layout) -> str:
    # ms -> ns saturating at u64::MAX (design study §7.6).
    return (
        "  (func $op_sleep (param $ms i64)\n"
        "    (local $p i32)\n"
        "    local.get $ms\n"
        "    i64.const 18446744073709\n"
        "    i64.gt_u\n"
        "    if (result i64)\n"
        "      i64.const -1\n"
        "    else\n"
        "      local.get $ms\n"
        "      i64.const 1000000\n"
        "      i64.mul\n"
        "    end\n"
        "    call $l_subdur\n"
        "    local.set $p\n"
        "    local.get $p\n"
        "    call $l_block\n"
        "    local.get $p\n"
        "    call $drop_poll\n"
        "  )"
    )


def _op_exit(lay: _Layout) -> str:
    # wasi:cli/exit@0.2 encodes only ok/err: 0 -> ok (exit 0),
    # nonzero -> err (exit 1).  Exit codes 2-255 degrade to 1 under a
    # stock wasip2 host — documented v1 limitation (0.3's
    # exit-with-code lifts it).
    return (
        "  (func $op_exit (param $code i64)\n"
        "    local.get $code\n"
        "    i64.const 0\n"
        "    i64.ne\n"
        "    call $l_exit\n"
        "    unreachable\n"
        "  )"
    )


def _op_random_int(lay: _Layout) -> str:
    # Rejection sampling for bias-freedom, matching the host's
    # randint: limit = 2^64 mod range = (0 - range) rem_u range;
    # accept r >= limit; result = low + (r rem range).
    return (
        "  (func $op_random_int (param $low i64) (param $high i64) "
        "(result i64)\n"
        "    (local $range i64)\n"
        "    (local $r i64)\n"
        "    (local $limit i64)\n"
        "    local.get $high\n"
        "    local.get $low\n"
        "    i64.sub\n"
        "    i64.const 1\n"
        "    i64.add\n"
        "    local.set $range\n"
        "    local.get $range\n"
        "    i64.eqz\n"
        "    if\n"
        "      call $l_rand64\n"
        "      return\n"
        "    end\n"
        "    i64.const 0\n"
        "    local.get $range\n"
        "    i64.sub\n"
        "    local.get $range\n"
        "    i64.rem_u\n"
        "    local.set $limit\n"
        "    loop $retry\n"
        "      call $l_rand64\n"
        "      local.set $r\n"
        "      local.get $r\n"
        "      local.get $limit\n"
        "      i64.lt_u\n"
        "      br_if $retry\n"
        "    end\n"
        "    local.get $low\n"
        "    local.get $r\n"
        "    local.get $range\n"
        "    i64.rem_u\n"
        "    i64.add\n"
        "  )"
    )


def _op_random_float(lay: _Layout) -> str:
    # [0,1) via the 53-bit mantissa trick.
    return (
        "  (func $op_random_float (result f64)\n"
        "    call $l_rand64\n"
        "    i64.const 11\n"
        "    i64.shr_u\n"
        "    f64.convert_i64_u\n"
        "    f64.const 0x1p-53\n"
        "    f64.mul\n"
        "  )"
    )


def _op_random_bool(lay: _Layout) -> str:
    return (
        "  (func $op_random_bool (result i32)\n"
        "    call $l_rand64\n"
        "    i64.const 1\n"
        "    i64.and\n"
        "    i32.wrap_i64\n"
        "  )"
    )


def _op_get_env(lay: _Layout) -> str:
    env = lay.slab("env")
    return (
        "  (func $op_get_env (param $np i32) (param $nl i32) "
        "(result i32)\n"
        "    (local $lst i32)\n"
        "    (local $cnt i32)\n"
        "    (local $i i32)\n"
        "    (local $e i32)\n"
        "    (local $vp i32)\n"
        "    (local $vl i32)\n"
        "    (local $sp i32)\n"
        "    call $arena_reset\n"
        f"    i32.const {env}\n"
        "    call $l_get_env\n"
        f"    i32.const {env}\n"
        "    i32.load\n"
        "    local.set $lst\n"
        f"    i32.const {env}\n"
        "    i32.load offset=4\n"
        "    local.set $cnt\n"
        "    block $notfound\n"
        "    loop $scan\n"
        "      local.get $i\n"
        "      local.get $cnt\n"
        "      i32.ge_u\n"
        "      br_if $notfound\n"
        "      local.get $lst\n"
        "      local.get $i\n"
        "      i32.const 4\n"
        "      i32.shl\n"
        "      i32.add\n"
        "      local.set $e\n"
        "      local.get $e\n"
        "      i32.load offset=4\n"
        "      local.get $nl\n"
        "      i32.eq\n"
        "      if\n"
        "        local.get $e\n"
        "        i32.load\n"
        "        local.get $np\n"
        "        local.get $nl\n"
        "        call $bytes_eq\n"
        "        if\n"
        "          local.get $e\n"
        "          i32.load offset=8\n"
        "          local.set $vp\n"
        "          local.get $e\n"
        "          i32.load offset=12\n"
        "          local.set $vl\n"
        "          local.get $vl\n"
        "          if\n"
        "            local.get $vl\n"
        "            call $alloc\n"
        "            local.set $sp\n"
        "            local.get $sp\n"
        "            local.get $vp\n"
        "            local.get $vl\n"
        "            memory.copy\n"
        "          end\n"
        "          i32.const 1\n"
        "          local.get $sp\n"
        "          local.get $vl\n"
        "          call $mk_res_str\n"
        "          return\n"
        "        end\n"
        "      end\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $i\n"
        "      br $scan\n"
        "    end\n"
        "    end\n"
        "    i32.const 0\n"
        "    call $mk_tag_only\n"
        "  )"
    )


def _op_args(lay: _Layout) -> str:
    # Skips argv[0] (program name) to match IO.args semantics; the
    # runner must set WasiConfig.argv = ["<program>", *user_args].
    # The canonical list<string> element layout (8 B {ptr,len}) is
    # identical to Vera's Array<String> backing, so the copy loop is
    # a template walk.
    args = lay.slab("args")
    return (
        "  (func $op_args (result i32 i32)\n"
        "    (local $lst i32)\n"
        "    (local $cnt i32)\n"
        "    (local $n i32)\n"
        "    (local $backing i32)\n"
        "    (local $i i32)\n"
        "    (local $src i32)\n"
        "    (local $len i32)\n"
        "    (local $sp i32)\n"
        "    call $arena_reset\n"
        f"    i32.const {args}\n"
        "    call $l_get_args\n"
        f"    i32.const {args}\n"
        "    i32.load\n"
        "    local.set $lst\n"
        f"    i32.const {args}\n"
        "    i32.load offset=4\n"
        "    local.set $cnt\n"
        "    local.get $cnt\n"
        "    i32.const 1\n"
        "    i32.le_u\n"
        "    if\n"
        "      i32.const 0\n"
        "      i32.const 0\n"
        "      return\n"
        "    end\n"
        "    local.get $cnt\n"
        "    i32.const 1\n"
        "    i32.sub\n"
        "    local.set $n\n"
        "    local.get $n\n"
        "    i32.const 3\n"
        "    i32.shl\n"
        "    call $alloc\n"
        "    local.set $backing\n"
        "    local.get $backing\n"
        "    call $shadow_push\n"
        "    block $done\n"
        "    loop $each\n"
        "      local.get $i\n"
        "      local.get $n\n"
        "      i32.ge_u\n"
        "      br_if $done\n"
        "      local.get $lst\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      i32.const 3\n"
        "      i32.shl\n"
        "      i32.add\n"
        "      local.set $src\n"
        "      local.get $src\n"
        "      i32.load offset=4\n"
        "      local.set $len\n"
        "      i32.const 0\n"
        "      local.set $sp\n"
        "      local.get $len\n"
        "      if\n"
        "        local.get $len\n"
        "        call $alloc\n"
        "        local.set $sp\n"
        "        local.get $sp\n"
        "        local.get $src\n"
        "        i32.load\n"
        "        local.get $len\n"
        "        memory.copy\n"
        "      end\n"
        "      local.get $backing\n"
        "      local.get $i\n"
        "      i32.const 3\n"
        "      i32.shl\n"
        "      i32.add\n"
        "      local.get $sp\n"
        "      i32.store\n"
        "      local.get $backing\n"
        "      local.get $i\n"
        "      i32.const 3\n"
        "      i32.shl\n"
        "      i32.add\n"
        "      local.get $len\n"
        "      i32.store offset=4\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $i\n"
        "      br $each\n"
        "    end\n"
        "    end\n"
        "    i32.const 1\n"
        "    call $shadow_pop_n\n"
        "    local.get $backing\n"
        "    local.get $n\n"
        "  )"
    )


def _op_read_line(lay: _Layout) -> str:
    # Grow-by-doubling GC buffer; the old buffer is rooted across the
    # doubled alloc.  Strips the trailing newline AND a trailing \r
    # before it (host parity: the core path reads stdin through
    # Python's universal-newlines text layer, so CRLF input never
    # yields a trailing \r there, on any platform — surfaced by the
    # windows-latest CI matrix).  A lone \r line *separator* is not
    # treated as a terminator (that would need cross-call byte
    # pushback); documented divergence in spec section 13.6.  EOF
    # with no bytes returns the empty string (0,0).
    return (
        "  (func $op_read_line (result i32 i32)\n"
        "    (local $buf i32)\n"
        "    (local $cap i32)\n"
        "    (local $n i32)\n"
        "    (local $b i32)\n"
        "    (local $new i32)\n"
        "    call $ensure_stdin\n"
        "    i32.const 64\n"
        "    call $alloc\n"
        "    local.set $buf\n"
        "    i32.const 64\n"
        "    local.set $cap\n"
        "    block $done\n"
        "    loop $rd\n"
        "      call $arena_reset\n"
        "      call $read_byte\n"
        "      local.tee $b\n"
        "      i32.const -1\n"
        "      i32.eq\n"
        "      br_if $done\n"
        "      local.get $b\n"
        "      i32.const 10\n"
        "      i32.eq\n"
        "      br_if $done\n"
        "      local.get $n\n"
        "      local.get $cap\n"
        "      i32.eq\n"
        "      if\n"
        "        local.get $buf\n"
        "        call $shadow_push\n"
        "        local.get $cap\n"
        "        i32.const 1\n"
        "        i32.shl\n"
        "        call $alloc\n"
        "        local.set $new\n"
        "        i32.const 1\n"
        "        call $shadow_pop_n\n"
        "        local.get $new\n"
        "        local.get $buf\n"
        "        local.get $n\n"
        "        memory.copy\n"
        "        local.get $new\n"
        "        local.set $buf\n"
        "        local.get $cap\n"
        "        i32.const 1\n"
        "        i32.shl\n"
        "        local.set $cap\n"
        "      end\n"
        "      local.get $buf\n"
        "      local.get $n\n"
        "      i32.add\n"
        "      local.get $b\n"
        "      i32.store8\n"
        "      local.get $n\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $n\n"
        "      br $rd\n"
        "    end\n"
        "    end\n"
        "    local.get $n\n"
        "    if\n"
        "      local.get $buf\n"
        "      local.get $n\n"
        "      i32.add\n"
        "      i32.const 1\n"
        "      i32.sub\n"
        "      i32.load8_u\n"
        "      i32.const 13\n"
        "      i32.eq\n"
        "      if\n"
        "        local.get $n\n"
        "        i32.const 1\n"
        "        i32.sub\n"
        "        local.set $n\n"
        "      end\n"
        "    end\n"
        "    local.get $n\n"
        "    i32.eqz\n"
        "    if\n"
        "      i32.const 0\n"
        "      i32.const 0\n"
        "      return\n"
        "    end\n"
        "    local.get $buf\n"
        "    local.get $n\n"
        "  )"
    )


def _op_read_char(lay: _Layout) -> str:
    # UTF-8 sequence length from the lead byte; continuation bytes are
    # stored into the (already-allocated) GC string — no GC allocs
    # while $sp is unrooted.  EOF before/inside a char -> Err("EOF"),
    # matching host_read_char.
    eof_ptr, eof_len = lay.statics["eof"]
    err_eof = (
        "      i32.const 1\n"
        f"      i32.const {eof_ptr}\n"
        f"      i32.const {eof_len}\n"
        "      call $mk_res_str\n"
        "      return\n"
    )
    return (
        "  (func $op_read_char (result i32)\n"
        "    (local $b i32)\n"
        "    (local $need i32)\n"
        "    (local $have i32)\n"
        "    (local $sp i32)\n"
        "    call $ensure_stdin\n"
        "    call $arena_reset\n"
        "    call $read_byte\n"
        "    local.tee $b\n"
        "    i32.const -1\n"
        "    i32.eq\n"
        "    if\n"
        + err_eof +
        "    end\n"
        "    i32.const 1\n"
        "    local.set $need\n"
        "    local.get $b\n"
        "    i32.const 224\n"
        "    i32.and\n"
        "    i32.const 192\n"
        "    i32.eq\n"
        "    if\n"
        "      i32.const 2\n"
        "      local.set $need\n"
        "    end\n"
        "    local.get $b\n"
        "    i32.const 240\n"
        "    i32.and\n"
        "    i32.const 224\n"
        "    i32.eq\n"
        "    if\n"
        "      i32.const 3\n"
        "      local.set $need\n"
        "    end\n"
        "    local.get $b\n"
        "    i32.const 248\n"
        "    i32.and\n"
        "    i32.const 240\n"
        "    i32.eq\n"
        "    if\n"
        "      i32.const 4\n"
        "      local.set $need\n"
        "    end\n"
        "    local.get $need\n"
        "    call $alloc\n"
        "    local.set $sp\n"
        "    local.get $sp\n"
        "    local.get $b\n"
        "    i32.store8\n"
        "    i32.const 1\n"
        "    local.set $have\n"
        "    block $filled\n"
        "    loop $fill\n"
        "      local.get $have\n"
        "      local.get $need\n"
        "      i32.ge_u\n"
        "      br_if $filled\n"
        "      call $arena_reset\n"
        "      call $read_byte\n"
        "      local.tee $b\n"
        "      i32.const -1\n"
        "      i32.eq\n"
        "      if\n"
        + err_eof +
        "      end\n"
        "      local.get $sp\n"
        "      local.get $have\n"
        "      i32.add\n"
        "      local.get $b\n"
        "      i32.store8\n"
        "      local.get $have\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $have\n"
        "      br $fill\n"
        "    end\n"
        "    end\n"
        "    i32.const 0\n"
        "    local.get $sp\n"
        "    local.get $need\n"
        "    call $mk_res_str\n"
        "  )"
    )


def _op_read_file(lay: _Layout) -> str:
    nopre_ptr, nopre_len = lay.statics["nopre"]
    op = lay.slab("open")
    st = lay.slab("stream")
    rd = lay.slab("read")
    return (
        "  (func $op_read_file (param $pp i32) (param $pl i32) "
        "(result i32)\n"
        "    (local $dfd i32)\n"
        "    (local $fd i32)\n"
        "    (local $s i32)\n"
        "    (local $buf i32)\n"
        "    (local $cap i32)\n"
        "    (local $n i32)\n"
        "    (local $lptr i32)\n"
        "    (local $llen i32)\n"
        "    (local $new i32)\n"
        "    (local $mp i32)\n"
        "    (local $ml i32)\n"
        "    call $get_preopen\n"
        "    local.tee $dfd\n"
        "    i32.const -1\n"
        "    i32.eq\n"
        "    if\n"
        "      i32.const 1\n"
        f"      i32.const {nopre_ptr}\n"
        f"      i32.const {nopre_len}\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        "    local.get $pp\n"
        "    local.get $pl\n"
        "    call $strip_path\n"
        "    local.set $pl\n"
        "    local.set $pp\n"
        "    local.get $dfd\n"
        "    i32.const 1\n"
        "    local.get $pp\n"
        "    local.get $pl\n"
        "    i32.const 0\n"
        "    i32.const 1\n"
        f"    i32.const {op}\n"
        "    call $l_open_at\n"
        # u8 discriminant loads — see $write_or_trap.  The err payload
        # (error-code enum, 37 cases) is also a u8; the ok payload
        # (own descriptor handle) is a full i32.
        f"    i32.const {op}\n"
        "    i32.load8_u\n"
        "    if\n"
        f"      i32.const {op}\n"
        "      i32.load8_u offset=4\n"
        "      call $errno_str\n"
        "      local.set $ml\n"
        "      local.set $mp\n"
        "      i32.const 1\n"
        "      local.get $mp\n"
        "      local.get $ml\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        f"    i32.const {op}\n"
        "    i32.load offset=4\n"
        "    local.set $fd\n"
        "    local.get $fd\n"
        "    i64.const 0\n"
        f"    i32.const {st}\n"
        "    call $l_read_via\n"
        f"    i32.const {st}\n"
        "    i32.load8_u\n"
        "    if\n"
        "      local.get $fd\n"
        "      call $drop_desc\n"
        f"      i32.const {st}\n"
        "      i32.load8_u offset=4\n"
        "      call $errno_str\n"
        "      local.set $ml\n"
        "      local.set $mp\n"
        "      i32.const 1\n"
        "      local.get $mp\n"
        "      local.get $ml\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        f"    i32.const {st}\n"
        "    i32.load offset=4\n"
        "    local.set $s\n"
        "    i32.const 4096\n"
        "    call $alloc\n"
        "    local.set $buf\n"
        "    i32.const 4096\n"
        "    local.set $cap\n"
        "    block $eof\n"
        "    loop $chunk\n"
        "      call $arena_reset\n"
        "      local.get $s\n"
        "      i64.const 16384\n"
        f"      i32.const {rd}\n"
        "      call $l_bread\n"
        # u8 discriminant loads — see $write_or_trap.
        f"      i32.const {rd}\n"
        "      i32.load8_u\n"
        "      if\n"
        f"        i32.const {rd}\n"
        "        i32.load8_u offset=4\n"
        "        i32.const 1\n"
        "        i32.eq\n"
        "        br_if $eof\n"
        f"        i32.const {rd}\n"
        "        i32.load offset=8\n"
        "        call $debug_string\n"
        "        local.set $ml\n"
        "        local.set $mp\n"
        "        local.get $s\n"
        "        call $drop_istream\n"
        "        local.get $fd\n"
        "        call $drop_desc\n"
        "        i32.const 1\n"
        "        local.get $mp\n"
        "        local.get $ml\n"
        "        call $mk_res_str\n"
        "        return\n"
        "      end\n"
        f"      i32.const {rd}\n"
        "      i32.load offset=4\n"
        "      local.set $lptr\n"
        f"      i32.const {rd}\n"
        "      i32.load offset=8\n"
        "      local.set $llen\n"
        "      local.get $llen\n"
        "      i32.eqz\n"
        "      br_if $chunk\n"
        "      block $capok\n"
        "      loop $grow\n"
        "        local.get $n\n"
        "        local.get $llen\n"
        "        i32.add\n"
        "        local.get $cap\n"
        "        i32.le_u\n"
        "        br_if $capok\n"
        "        local.get $buf\n"
        "        call $shadow_push\n"
        "        local.get $cap\n"
        "        i32.const 1\n"
        "        i32.shl\n"
        "        call $alloc\n"
        "        local.set $new\n"
        "        i32.const 1\n"
        "        call $shadow_pop_n\n"
        "        local.get $new\n"
        "        local.get $buf\n"
        "        local.get $n\n"
        "        memory.copy\n"
        "        local.get $new\n"
        "        local.set $buf\n"
        "        local.get $cap\n"
        "        i32.const 1\n"
        "        i32.shl\n"
        "        local.set $cap\n"
        "        br $grow\n"
        "      end\n"
        "      end\n"
        "      local.get $buf\n"
        "      local.get $n\n"
        "      i32.add\n"
        "      local.get $lptr\n"
        "      local.get $llen\n"
        "      memory.copy\n"
        "      local.get $n\n"
        "      local.get $llen\n"
        "      i32.add\n"
        "      local.set $n\n"
        "      br $chunk\n"
        "    end\n"
        "    end\n"
        "    local.get $s\n"
        "    call $drop_istream\n"
        "    local.get $fd\n"
        "    call $drop_desc\n"
        "    local.get $n\n"
        "    i32.eqz\n"
        "    if\n"
        "      i32.const 0\n"
        "      i32.const 0\n"
        "      i32.const 0\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        "    i32.const 0\n"
        "    local.get $buf\n"
        "    local.get $n\n"
        "    call $mk_res_str\n"
        "  )"
    )


def _op_write_file(lay: _Layout) -> str:
    nopre_ptr, nopre_len = lay.statics["nopre"]
    closed_ptr, closed_len = lay.statics["closed"]
    op = lay.slab("open")
    st = lay.slab("stream")
    bwf = lay.slab("bwf")
    return (
        "  (func $op_write_file (param $pp i32) (param $pl i32) "
        "(param $dp i32) (param $dl i32) (result i32)\n"
        "    (local $dfd i32)\n"
        "    (local $fd i32)\n"
        "    (local $s i32)\n"
        "    (local $n i32)\n"
        "    (local $mp i32)\n"
        "    (local $ml i32)\n"
        "    call $get_preopen\n"
        "    local.tee $dfd\n"
        "    i32.const -1\n"
        "    i32.eq\n"
        "    if\n"
        "      i32.const 1\n"
        f"      i32.const {nopre_ptr}\n"
        f"      i32.const {nopre_len}\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        "    local.get $pp\n"
        "    local.get $pl\n"
        "    call $strip_path\n"
        "    local.set $pl\n"
        "    local.set $pp\n"
        "    local.get $dfd\n"
        "    i32.const 1\n"
        "    local.get $pp\n"
        "    local.get $pl\n"
        "    i32.const 9\n"
        "    i32.const 2\n"
        f"    i32.const {op}\n"
        "    call $l_open_at\n"
        f"    i32.const {op}\n"
        # u8 discriminant loads — see $write_or_trap / $op_read_file.
        "    i32.load8_u\n"
        "    if\n"
        f"      i32.const {op}\n"
        "      i32.load8_u offset=4\n"
        "      call $errno_str\n"
        "      local.set $ml\n"
        "      local.set $mp\n"
        "      i32.const 1\n"
        "      local.get $mp\n"
        "      local.get $ml\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        f"    i32.const {op}\n"
        "    i32.load offset=4\n"
        "    local.set $fd\n"
        "    local.get $fd\n"
        "    i64.const 0\n"
        f"    i32.const {st}\n"
        "    call $l_write_via\n"
        f"    i32.const {st}\n"
        "    i32.load8_u\n"
        "    if\n"
        "      local.get $fd\n"
        "      call $drop_desc\n"
        f"      i32.const {st}\n"
        "      i32.load8_u offset=4\n"
        "      call $errno_str\n"
        "      local.set $ml\n"
        "      local.set $mp\n"
        "      i32.const 1\n"
        "      local.get $mp\n"
        "      local.get $ml\n"
        "      call $mk_res_str\n"
        "      return\n"
        "    end\n"
        f"    i32.const {st}\n"
        "    i32.load offset=4\n"
        "    local.set $s\n"
        "    block $done\n"
        "    loop $chunk\n"
        "      local.get $dl\n"
        "      i32.eqz\n"
        "      br_if $done\n"
        "      local.get $dl\n"
        "      i32.const 4096\n"
        "      i32.lt_u\n"
        "      if (result i32)\n"
        "        local.get $dl\n"
        "      else\n"
        "        i32.const 4096\n"
        "      end\n"
        "      local.set $n\n"
        "      local.get $s\n"
        "      local.get $dp\n"
        "      local.get $n\n"
        f"      i32.const {bwf}\n"
        "      call $l_bwf\n"
        # u8 discriminant loads — see $write_or_trap.
        f"      i32.const {bwf}\n"
        "      i32.load8_u\n"
        "      if\n"
        f"        i32.const {bwf}\n"
        "        i32.load8_u offset=4\n"
        "        i32.eqz\n"
        "        if (result i32 i32)\n"
        f"          i32.const {bwf}\n"
        "          i32.load offset=8\n"
        "          call $debug_string\n"
        "        else\n"
        f"          i32.const {closed_ptr}\n"
        f"          i32.const {closed_len}\n"
        "        end\n"
        "        local.set $ml\n"
        "        local.set $mp\n"
        "        local.get $s\n"
        "        call $drop_ostream\n"
        "        local.get $fd\n"
        "        call $drop_desc\n"
        "        i32.const 1\n"
        "        local.get $mp\n"
        "        local.get $ml\n"
        "        call $mk_res_str\n"
        "        return\n"
        "      end\n"
        "      local.get $dp\n"
        "      local.get $n\n"
        "      i32.add\n"
        "      local.set $dp\n"
        "      local.get $dl\n"
        "      local.get $n\n"
        "      i32.sub\n"
        "      local.set $dl\n"
        "      br $chunk\n"
        "    end\n"
        "    end\n"
        "    local.get $s\n"
        "    call $drop_ostream\n"
        "    local.get $fd\n"
        "    call $drop_desc\n"
        "    i32.const 0\n"
        "    call $mk_tag_only\n"
        "  )"
    )


_OP_EMITTERS: dict[str, Callable[[_Layout], str]] = {
    "print": _op_print,
    "stderr": _op_stderr,
    "read_line": _op_read_line,
    "read_char": _op_read_char,
    "read_file": _op_read_file,
    "write_file": _op_write_file,
    "args": _op_args,
    "get_env": _op_get_env,
    "time": _op_time,
    "sleep": _op_sleep,
    "exit": _op_exit,
    "random_int": _op_random_int,
    "random_float": _op_random_float,
    "random_bool": _op_random_bool,
    "contract_fail": _op_contract_fail,
    "overflow_trap": _op_overflow_trap,
}


# =====================================================================
# Component assembly
# =====================================================================

def _iface_closure(ifaces: set[str]) -> list[str]:
    """Dependency-close and order the interface import set."""
    closed = set(ifaces)
    changed = True
    while changed:
        changed = False
        for iface in tuple(closed):
            for dep in _IFACE_DEPS.get(iface, ()):
                if dep not in closed:
                    closed.add(dep)
                    changed = True
    return [i for i in _IFACE_ORDER if i in closed]


def _assemble_component(
    main_fields: list[str], used: set[str], lay: _Layout,
) -> str:
    specs = {n: _OPS[n] for n in used}
    ifaces = _iface_closure(
        set().union(*(s.ifaces for s in specs.values())) if specs else set()
    )
    lowers = sorted(
        set().union(*(s.lowers for s in specs.values())) if specs else set()
    )
    drops = sorted(
        set().union(*(s.drops for s in specs.values())) if specs else set()
    )

    parts: list[str] = ["(component $C"]
    for iface in ifaces:
        parts.append(_IFACES[iface])

    parts.append("  (core module $Main")
    parts.extend("  " + line if line else line for line in main_fields)
    parts.append("  )")
    parts.append("  (core instance $main (instantiate $Main))")
    parts.append('  (alias core export $main "memory" (core memory $mem))')
    parts.append(
        '  (alias core export $main "cabi_realloc" (core func $realloc))'
    )
    parts.append(
        '  (alias core export $main "wasi_tbl" (core table $tbl))'
    )
    parts.append(
        '  (alias core export $main "wasi_arena_ptr" '
        "(core global $g_arena))"
    )
    if lay.has_alloc:
        parts.append(
            '  (alias core export $main "alloc" (core func $f_alloc))'
        )
        parts.append(
            '  (alias core export $main "gc_sp" (core global $g_sp))'
        )
        parts.append(
            '  (alias core export $main "gc_stack_limit" '
            "(core global $g_lim))"
        )

    for key in lowers:
        parts.append(_LOWERS[key][0])
    for key in drops:
        parts.append(_DROPS[key][0])

    if used:
        parts.append("  (core module $Adapter")
        parts.extend(
            "  " + line if line else line
            for line in _adapter_fields(used, lay)
        )
        parts.append("  )")
        env_exports = [
            '      (export "memory" (memory $mem))',
            '      (export "tbl" (table $tbl))',
            '      (export "arena_ptr" (global $g_arena))',
        ]
        if lay.has_alloc:
            env_exports += [
                '      (export "alloc" (func $f_alloc))',
                '      (export "gc_sp" (global $g_sp))',
                '      (export "gc_stack_limit" (global $g_lim))',
            ]
        parts.append("  (core instance $adapter (instantiate $Adapter")
        parts.append('    (with "env" (instance')
        parts.extend(env_exports)
        parts.append("    ))")
        if lowers or drops:
            parts.append('    (with "wasi" (instance')
            for key in lowers:
                parts.append(_LOWERS[key][2])
            for key in drops:
                parts.append(_DROPS[key][2])
            parts.append("    ))")
        parts.append("  ))")

    parts.append(
        "  (func $run_l (result (result)) "
        '(canon lift (core func $main "__wasi_run")))'
    )
    parts.append('  (instance $run_inst (export "run" (func $run_l)))')
    parts.append('  (export "wasi:cli/run@0.2.0" (instance $run_inst))')

    lift_result = {
        (): "",
        ("i64",): " (result s64)",
        ("f64",): " (result float64)",
    }.get(lay.main_results)
    if lift_result is not None:
        parts.append(
            f"  (func $main_l{lift_result} "
            '(canon lift (core func $main "main")))'
        )
        parts.append('  (export "main" (func $main_l))')

    parts.append(")")
    return "\n".join(parts)


# =====================================================================
# Public API
# =====================================================================

def emit_wasi_component(result: CompileResult, world: str = "cli") -> str:
    """Emit a WASI Preview 2 component (text format) for ``result``.

    ``world`` selects the entry-point surface:

    - ``"cli"`` (default, the shipped #237 behavior): the component
      exports ``wasi:cli/run@0.2.0`` (stock ``wasmtime run``
      compatible) and, when ``main`` returns a scalar (or Unit), a
      plain lifted ``main`` for the Python runner.
    - ``"server"`` (Stage D): the component exports
      ``wasi:http/incoming-handler@0.2.0`` around the program's public
      ``handle(Request -> Response)`` and runs under stock
      ``wasmtime serve`` unmodified.

    Raises ``ValueError`` with a clean diagnostic when the program
    uses a host family the selected world does not support, when the
    required entry point is missing (zero-parameter ``main`` for cli,
    #305-shaped ``handle`` for server), or when a reserved identifier
    collides.  Never silently falls back.
    """
    if world not in ("cli", "server"):
        raise ValueError(
            f"unknown wasi-p2 world {world!r}; expected 'cli' or 'server'"
        )
    if not result.ok:
        raise ValueError(
            "cannot emit a wasi-p2 component from a failed compilation"
        )
    if world == "server":
        return _emit_server_component(result)
    _gate_families(result)

    used: dict[str, str] = {}
    for line in result.wat.split("\n"):
        m = _IMPORT_RE.match(line)
        if not m:
            continue
        name, sig = m.group(1), m.group(2)
        spec = _OPS.get(name)
        if spec is None:
            raise ValueError(
                f"--target wasi-p2 does not support the host import "
                f"'{name}'"
            )
        if sig != _expected_sig(spec):
            raise RuntimeError(
                f"host import '{name}' signature {sig!r} does not match "
                f"the wasi-p2 op table ({_expected_sig(spec)!r}); "
                "vera/codegen/assembly.py and vera/codegen/wasi.py are "
                "out of sync"
            )
        used[name] = sig

    main_fields, layout = _transform_main(result.wat, used)
    return _assemble_component(main_fields, set(used), layout)


# =====================================================================
# Server world (Stage D, #305/#237): wasi:http/incoming-handler@0.2.0
# =====================================================================
#
# The server world wraps the program's verified public
# ``handle(Request -> Response)`` in an adapter-resident serve wrapper
# that marshals wasi:http resources into the prelude Request ADT and
# drives the response half from the returned Response ADT.  Every
# import spelling, flattened core signature, and retptr layout below
# was validated live against wasmtime-py 45 (Component parse) and
# wasmtime CLI 46 (`wasmtime serve` + HTTP round-trips) by the Stage-D
# design study, including a full compiled-handler echo prototype.
#
# Topology: identical to the cli world (MAIN owns memory/GC/arena/
# cabi_realloc; adapter plants dispatch-table ops), extended with:
#   - the String-keyed Map ops emulated IN-GUEST in the adapter
#     (post-#706 Maps are guest-memory bucket arrays — no host store),
#   - the serve wrapper ``$serve_handle`` in the adapter, importing
#     the wasi:http lowers directly (never through the dispatch
#     table) plus MAIN's exported ``handle``/``alloc``/GC globals,
#   - a 32-slot dispatch table (map family at slots 16+),
#   - the wrap-table region accepted (map programs carry it), arena
#     placed above it exactly as the cli world places it above the
#     GC statics.

#: Map wrapper tag word — must equal ``vera.runtime.heap._MAP_HANDLE_TAG``
#: (pinned by a drift test in tests/test_wasi_target.py; not imported
#: here to keep this module free of runtime deps).
_MAP_WRAPPER_TAG = 0xFEEDC001

_SERVER_TABLE_SIZE = 32

#: Server retptr slab (design §2.2).  Distinct from the cli ``_SLAB``
#: so cli offsets stay byte-identical; "bwf"/"now" keys let the shared
#: Stage-C op emitters (print/stderr/time/...) work unchanged.
_SERVER_SLAB: dict[str, int] = {
    "mth": 0,        # 12 B — method variant result
    "path": 16,      # 12 B — path-with-query option
    "ents": 32,      # 8 B  — entries list header
    "consume": 40,   # 8 B  — consume result
    "stream": 48,    # 8 B  — incoming-body.stream result
    "bread": 56,     # 12 B — blocking-read result
    "flist": 72,     # 8 B  — from-list result
    "finish": 80,    # 40 B — outgoing-body.finish result (8-aligned)
    "bwf": 120,      # 12 B — blocking-write-and-flush result
    "rb": 136,       # 8 B  — outgoing-response.body / outgoing-body.write
    "now": 144,      # 16 B — wall-clock datetime record (8-aligned)
}
_SERVER_SLAB_SIZE = 160

_METHOD_NAMES: tuple[str, ...] = (
    "GET", "HEAD", "POST", "PUT", "DELETE", "CONNECT", "OPTIONS",
    "TRACE", "PATCH",
)

#: wasi:http error-code variant case index of ``internal-error`` (the
#: 39-case variant in ``_HTTP_TYPES_IFACE`` below; 0-based).
_ERRCODE_INTERNAL_ERROR = 38

#: In-guest Map ops (String/String only) + the two wrapper stubs.
#: Slots extend the cli table (0-15); pure guest code — no WASI
#: interfaces, lowers, or drops.
_MAP_OPS: dict[str, _OpSpec] = {
    "map_new": _op(16, "", "i32", needs_alloc=True),
    "map_insert$ks_vs": _op(17, "i32 i32 i32 i32 i32", "i32",
                            needs_alloc=True),
    "map_get$ks_vs": _op(18, "i32 i32 i32", "i32", needs_alloc=True),
    "map_contains$ks": _op(19, "i32 i32 i32", "i32"),
    "map_size": _op(20, "i32", "i64"),
    "map_remove$ks": _op(21, "i32 i32 i32", "i32", needs_alloc=True),
    "map_keys$ks": _op(22, "i32", "i32 i32", needs_alloc=True),
    "map_values$vs": _op(23, "i32", "i32 i32", needs_alloc=True),
    "host_decref_handle": _op(24, "i32 i32", ""),
    "attach_bucket_to_wrapper": _op(25, "i32 i32 i32", ""),
}

#: Stage-C ops the server world keeps (proxy-world-linkable; design
#: §1.3 verdict table).
_SERVER_IO_OPS = frozenset({
    "print", "stderr", "time", "sleep",
    "random_int", "random_float", "random_bool",
    "contract_fail", "overflow_trap",
})

#: Stage-C ops the server world REJECTS, with the family/reason named
#: in the diagnostic (design §1.3: filesystem/environment/exit are not
#: in the wasmtime-serve proxy world; stdin links but is a closed
#: stream — degenerate in a request handler).
_SERVER_REJECTED_OPS: dict[str, str] = {
    "read_line": "IO.read_line (stdin is a closed stream under"
                 " wasmtime serve)",
    "read_char": "IO.read_char (stdin is a closed stream under"
                 " wasmtime serve)",
    "read_file": "IO.read_file (wasi:filesystem is not in the"
                 " wasmtime serve proxy world)",
    "write_file": "IO.write_file (wasi:filesystem is not in the"
                  " wasmtime serve proxy world)",
    "args": "IO.args (wasi:cli/environment is not in the wasmtime"
            " serve proxy world)",
    "get_env": "IO.get_env (wasi:cli/environment is not in the"
               " wasmtime serve proxy world)",
    "exit": "IO.exit (wasi:cli/exit is not in the wasmtime serve"
            " proxy world)",
}

#: Generalized ``vera.*`` import matcher for the server world: accepts
#: BOTH the compact param form (``(param i32 i32)``, the IO family)
#: and the per-param form with ``$``-suffixed names
#: (``map_insert$ks_vs (param i32) (param i32) ...``, the map family).
_SERVER_IMPORT_RE = re.compile(
    r'^  \(import "vera" "([A-Za-z0-9_$]+)" \(func \$\S+'
    r'((?:\s\(param(?: (?:i32|i64|f32|f64))+\))*)'
    # Multivalue results are spelled as REPEATED single-type groups
    # ("(result i32) (result i32)", e.g. map_keys$ks) — hence * here.
    r'((?:\s\(result(?: (?:i32|i64|f32|f64))+\))*)\)\)$'
)
_CORE_TYPE_RE = re.compile(r"i32|i64|f32|f64")


# ---------------------------------------------------------------------
# Server family gate + handler validation
# ---------------------------------------------------------------------

def _map_op_is_string_string(op: str) -> bool:
    """True for ``$ks``/``$vs``-only instantiation suffixes."""
    suffix = op.split("$", 1)[1]
    return all(
        (tok == "ks") if tok.startswith("k") else (tok == "vs")
        for tok in suffix.split("_")
    )


def _gate_families_server(result: CompileResult) -> None:
    """Server-world family gate (design §3.1/§5.1).

    Same shape as the cli gate but Map<String, String> is allowed
    (in-guest emulation); any other Map instantiation is rejected
    naming the offending op.  Never a silent fallback.
    """
    offending: list[str] = []
    for family, attr in _UNSUPPORTED_FAMILIES:
        if family == "map":
            continue
        ops = getattr(result, attr)
        if ops:
            offending.append(f"{family} ({', '.join(sorted(ops))})")
    if result.state_types:
        types = ", ".join(sorted(t for t, _ in result.state_types))
        offending.append(f"state ({types})")
    if offending:
        raise ValueError(
            "--target wasi-p2 --world server does not support the "
            f"following host famil{'ies' if len(offending) > 1 else 'y'}: "
            f"{'; '.join(offending)}. Supported families: IO (print, "
            "stderr, time, sleep), Random, Map<String, String>."
        )
    bad_maps = sorted(
        op for op in result.map_ops_used
        if "$" in op and not _map_op_is_string_string(op)
    )
    if bad_maps:
        raise ValueError(
            "--target wasi-p2 --world server supports Map host ops "
            "only at the Map<String, String> instantiation "
            f"(map_*$ks_vs); unsupported instantiation"
            f"{'s' if len(bad_maps) > 1 else ''}: {', '.join(bad_maps)}"
        )


def _server_adt_layouts(
    result: CompileResult,
) -> tuple[ConstructorLayout, ConstructorLayout]:
    """Fetch + shape-check the Request/Response constructor layouts.

    Same tripwires as ``build_request_adt`` / ``decode_response_adt``
    (vera/runtime/heap.py): if the prelude shapes move, the emitter
    must fail loudly, not emit a desynced wrapper.
    """
    req = result.adt_layouts["Request"]["Request"]
    req_shape = tuple(ty for _, ty in req.field_offsets)
    if req_shape != ("i32_pair", "i32_pair", "i32", "i32_pair"):
        raise ValueError(
            f"unexpected Request layout {req.field_offsets!r}; the "
            "prelude Request shape and the wasi-p2 server wrapper "
            "must move together"
        )
    resp = result.adt_layouts["Response"]["Response"]
    resp_shape = tuple(ty for _, ty in resp.field_offsets)
    if resp_shape != ("i64", "i32", "i32_pair"):
        raise ValueError(
            f"unexpected Response layout {resp.field_offsets!r}; the "
            "prelude Response shape and the wasi-p2 server wrapper "
            "must move together"
        )
    return req, resp


def _parse_server_imports(wat: str) -> dict[str, _OpSpec]:
    """Collect + validate the ``vera.*`` imports for the server world.

    Returns ``{op name: spec}``.  Rejected ops raise ``ValueError``
    naming the op and its family; unknown ops or signature mismatches
    raise (the op tables and vera/codegen/assembly.py are out of sync).
    """
    used: dict[str, _OpSpec] = {}
    for line in wat.split("\n"):
        m = _SERVER_IMPORT_RE.match(line)
        if not m:
            if line.startswith('  (import "vera"'):
                raise RuntimeError(
                    f"unrecognized vera host import in WAT: {line.strip()} "
                    "— the wasi-p2 emitter op table is out of sync with "
                    "vera/codegen/assembly.py"
                )
            continue
        name = m.group(1)
        params = " ".join(_CORE_TYPE_RE.findall(m.group(2)))
        results = " ".join(_CORE_TYPE_RE.findall(m.group(3)))
        if name in _SERVER_REJECTED_OPS:
            raise ValueError(
                "--target wasi-p2 --world server does not support "
                f"{_SERVER_REJECTED_OPS[name]}. Supported ops: IO.print, "
                "IO.stderr, IO.time, IO.sleep, Random, and "
                "Map<String, String>."
            )
        spec = _MAP_OPS.get(name)
        if spec is None and name in _SERVER_IO_OPS:
            spec = _OPS[name]
        if spec is None:
            raise ValueError(
                "--target wasi-p2 --world server does not support the "
                f"host import '{name}'"
            )
        if (params, results) != (spec.params, spec.results):
            raise RuntimeError(
                f"host import '{name}' signature "
                f"{(params, results)!r} does not match the wasi-p2 "
                f"server op table ({(spec.params, spec.results)!r}); "
                "vera/codegen/assembly.py and vera/codegen/wasi.py "
                "are out of sync"
            )
        used[name] = spec
    return used


# ---------------------------------------------------------------------
# Server MAIN transformation
# ---------------------------------------------------------------------

def _build_server_statics(arena_base: int) -> tuple[list[str], int, int]:
    """Method-name blob + the "/" fallback path, immortal in the arena.

    Returns (data-segment lines, statics base address, bump_start).
    """
    blob = "".join(_METHOD_NAMES) + "/"
    base = arena_base + _SERVER_SLAB_SIZE
    bump_start = (base + len(blob) + 7) & ~7
    return [f'  (data (i32.const {base}) "{blob}")'], base, bump_start


def _transform_main_server(
    wat: str, used: dict[str, _OpSpec],
) -> tuple[list[str], _Layout]:
    """Post-process the compiled core module for the server world.

    Differences from the cli ``_transform_main`` (design §1.4): no
    ``main`` requirement and no ``__wasi_run`` (the entry is the
    exported ``handle``, already validated on the CompileResult); the
    wrap-table region is ACCEPTED (map programs carry it — arena
    placement is unchanged, ``align8(gc_heap_start)`` sits above the
    wrap region); the dispatch table is 32 slots; the extended import
    grammar (``$``-suffixed names, per-param decls) is handled by the
    caller's ``_parse_server_imports``; memory min gets +1 page of
    GC-heap headroom past the arena (live-validated by the prototype).
    """
    body = _module_body(wat)
    _check_reserved_idents(body)

    kept: list[str] = []
    mem_idx = -1
    mem_min = 0
    heap_ptr_idx = -1
    gc_start_idx = -1
    gc_start_val = -1
    for line in body:
        if _SERVER_IMPORT_RE.match(line):
            continue  # replaced by shims below
        if line.startswith('  (import "vera"'):
            raise RuntimeError(
                f"unrecognized vera host import in WAT: {line.strip()} "
                "— the wasi-p2 emitter op table is out of sync with "
                "vera/codegen/assembly.py"
            )
        m = _MEMORY_RE.match(line)
        if m:
            mem_idx = len(kept)
            mem_min = int(m.group(1))
        m = _HEAP_PTR_RE.match(line)
        if m:
            heap_ptr_idx = len(kept)
        m = _GC_HEAP_START_RE.match(line)
        if m:
            gc_start_idx = len(kept)
            gc_start_val = int(m.group(1))
        kept.append(line)

    if gc_start_idx < 0 or heap_ptr_idx < 0 or mem_idx < 0:
        raise RuntimeError(
            "--target wasi-p2 --world server requires the GC runtime "
            "(a handle(Request -> Response) program always allocates); "
            "the compiled module lacks it — the emitter and the code "
            "generator are out of sync"
        )

    arena_base = (gc_start_val + 7) & ~7
    new_start = arena_base + _ARENA_SIZE
    arena_end = new_start
    kept[heap_ptr_idx] = (
        f'  (global $heap_ptr (export "heap_ptr") '
        f"(mut i32) (i32.const {new_start}))"
    )
    kept[gc_start_idx] = (
        f"  (global $gc_heap_start i32 (i32.const {new_start}))"
    )
    pages = (arena_end + 65535) // 65536 + 1
    kept[mem_idx] = (
        f'  (memory (export "memory") {max(mem_min, pages)})'
    )

    _segments, statics_base, bump_start = _build_server_statics(arena_base)
    layout = _Layout(
        arena_base=arena_base,
        bump_start=bump_start,
        arena_end=arena_end,
        has_alloc=True,
        statics={"mtab": (statics_base, 0)},
        errtab=0,
        main_results=(),
        slab_table=_SERVER_SLAB,
    )

    out = list(kept)
    out.append(
        f'  (table $wasi_tbl (export "wasi_tbl") '
        f"{_SERVER_TABLE_SIZE} {_SERVER_TABLE_SIZE} funcref)"
    )
    out.append(
        f'  (global $wasi_arena_ptr (export "wasi_arena_ptr") '
        f"(mut i32) (i32.const {bump_start}))"
    )
    out.append(_emit_cabi_realloc(arena_end))
    for name in sorted(used, key=lambda n: used[n].slot):
        out.append(_emit_shim(name, used[name]))
    return out, layout


# ---------------------------------------------------------------------
# Server adapter: in-guest Map ops (String/String, bucket-as-truth #706)
# ---------------------------------------------------------------------
#
# Semantics mirrored from vera/runtime/map.py + vera/runtime/heap.py:
# byte-wise key equality (SameValueZero == bytewise for Strings),
# position-preserving update (existing key keeps its slot order, new
# key appends — Python-dict parity, observable via map_keys), copy-on-
# write (fresh wrapper + bucket per insert/remove), capacity = the
# smallest power of two >= max(8, 2*count) (``_bkt_capacity``), and
# new buckets SHARING the immutable key/value string bytes of the
# source (the host ``_encode_raw`` precedent; the conservative GC
# traces bucket words, so shared strings stay live via the new
# bucket).
#
# GC discipline (#593 class, mirroring the host callbacks which read
# everything into Python BEFORE allocating): each op shadow-pushes its
# raw pointer arguments at entry (rooting a string-pool/null pointer
# is harmless — the scan range-checks), pushes the new wrapper across
# the bucket alloc, links bucket into wrapper+8 immediately after the
# bucket alloc, then does pure memory writes; pops on exit.  Compiled
# callers do NOT root their arguments across the call — the host path
# never needed them to.

def _op_ident(name: str) -> str:
    """Adapter function identifier for op ``name`` (strips ``$kX_vX``)."""
    return "$op_" + name.split("$")[0]


def _mk_wrapper() -> str:
    """12-byte Map wrapper {tag, vestigial 0, bucket_ptr 0}."""
    return (
        "  (func $mk_wrapper (result i32)\n"
        "    (local $w i32)\n"
        "    i32.const 12\n"
        "    call $alloc\n"
        "    local.set $w\n"
        "    local.get $w\n"
        f"    i32.const {_MAP_WRAPPER_TAG}\n"
        "    i32.store\n"
        "    local.get $w\n"
        "    i32.const 0\n"
        "    i32.store offset=4\n"
        "    local.get $w\n"
        "    i32.const 0\n"
        "    i32.store offset=8\n"
        "    local.get $w\n"
        "  )"
    )


def _bkt_find() -> str:
    """(bucket, key ptr, key len) -> occupied slot ptr, or 0."""
    return (
        "  (func $bkt_find (param $b i32) (param $kp i32) "
        "(param $kl i32) (result i32)\n"
        "    (local $cap i32)\n"
        "    (local $i i32)\n"
        "    (local $slot i32)\n"
        "    local.get $b\n"
        "    i32.eqz\n"
        "    if\n"
        "      i32.const 0\n"
        "      return\n"
        "    end\n"
        "    local.get $b\n"
        "    i32.load\n"
        "    local.set $cap\n"
        "    block $done\n"
        "    loop $scan\n"
        "      local.get $i\n"
        "      local.get $cap\n"
        "      i32.ge_u\n"
        "      br_if $done\n"
        "      local.get $b\n"
        "      i32.const 8\n"
        "      i32.add\n"
        "      local.get $i\n"
        "      i32.const 20\n"
        "      i32.mul\n"
        "      i32.add\n"
        "      local.set $slot\n"
        "      local.get $slot\n"
        "      i32.load\n"
        "      if\n"
        "        local.get $slot\n"
        "        i32.load offset=8\n"
        "        local.get $kl\n"
        "        i32.eq\n"
        "        if\n"
        "          local.get $slot\n"
        "          i32.load offset=4\n"
        "          local.get $kp\n"
        "          local.get $kl\n"
        "          call $bytes_eq\n"
        "          if\n"
        "            local.get $slot\n"
        "            return\n"
        "          end\n"
        "        end\n"
        "      end\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $i\n"
        "      br $scan\n"
        "    end\n"
        "    end\n"
        "    i32.const 0\n"
        "  )"
    )


def _bkt_cap() -> str:
    """Capacity for N entries: pow2 >= max(8, 2*N) (``_bkt_capacity``)."""
    return (
        "  (func $bkt_cap (param $n i32) (result i32)\n"
        "    (local $cap i32)\n"
        "    i32.const 8\n"
        "    local.set $cap\n"
        "    loop $grow\n"
        "      local.get $cap\n"
        "      local.get $n\n"
        "      i32.const 1\n"
        "      i32.shl\n"
        "      i32.lt_u\n"
        "      if\n"
        "        local.get $cap\n"
        "        i32.const 1\n"
        "        i32.shl\n"
        "        local.set $cap\n"
        "        br $grow\n"
        "      end\n"
        "    end\n"
        "    local.get $cap\n"
        "  )"
    )


def _op_map_new(lay: _Layout) -> str:
    return (
        "  (func $op_map_new (result i32)\n"
        "    call $mk_wrapper\n"
        "  )"
    )


def _op_map_insert(lay: _Layout) -> str:
    # Position-preserving copy: occupied slots are copied in slot
    # order; the matched slot gets the new value in place; a new key
    # appends after the copy.
    return (
        "  (func $op_map_insert (param $wp i32) (param $kp i32) "
        "(param $kl i32) (param $vp i32) (param $vl i32) (result i32)\n"
        "    (local $ob i32)\n"
        "    (local $ocap i32)\n"
        "    (local $ocnt i32)\n"
        "    (local $found i32)\n"
        "    (local $w i32)\n"
        "    (local $b i32)\n"
        "    (local $cap i32)\n"
        "    (local $ncnt i32)\n"
        "    (local $i i32)\n"
        "    (local $j i32)\n"
        "    (local $slot i32)\n"
        "    (local $dst i32)\n"
        "    local.get $wp\n"
        "    call $shadow_push\n"
        "    local.get $kp\n"
        "    call $shadow_push\n"
        "    local.get $vp\n"
        "    call $shadow_push\n"
        "    local.get $wp\n"
        "    i32.load offset=8\n"
        "    local.set $ob\n"
        "    local.get $ob\n"
        "    if\n"
        "      local.get $ob\n"
        "      i32.load\n"
        "      local.set $ocap\n"
        "      local.get $ob\n"
        "      i32.load offset=4\n"
        "      local.set $ocnt\n"
        "    end\n"
        "    local.get $ob\n"
        "    local.get $kp\n"
        "    local.get $kl\n"
        "    call $bkt_find\n"
        "    local.set $found\n"
        "    local.get $ocnt\n"
        "    local.get $found\n"
        "    i32.eqz\n"
        "    i32.add\n"
        "    local.set $ncnt\n"
        "    local.get $ncnt\n"
        "    call $bkt_cap\n"
        "    local.set $cap\n"
        "    call $mk_wrapper\n"
        "    local.set $w\n"
        "    local.get $w\n"
        "    call $shadow_push\n"
        "    local.get $cap\n"
        "    i32.const 20\n"
        "    i32.mul\n"
        "    i32.const 8\n"
        "    i32.add\n"
        "    call $alloc\n"
        "    local.set $b\n"
        "    local.get $b\n"
        "    i32.const 0\n"
        "    local.get $cap\n"
        "    i32.const 20\n"
        "    i32.mul\n"
        "    i32.const 8\n"
        "    i32.add\n"
        "    memory.fill\n"
        "    local.get $b\n"
        "    local.get $cap\n"
        "    i32.store\n"
        "    local.get $w\n"
        "    local.get $b\n"
        "    i32.store offset=8\n"
        "    block $copied\n"
        "    loop $cp\n"
        "      local.get $i\n"
        "      local.get $ocap\n"
        "      i32.ge_u\n"
        "      br_if $copied\n"
        "      local.get $ob\n"
        "      i32.const 8\n"
        "      i32.add\n"
        "      local.get $i\n"
        "      i32.const 20\n"
        "      i32.mul\n"
        "      i32.add\n"
        "      local.set $slot\n"
        "      local.get $slot\n"
        "      i32.load\n"
        "      if\n"
        "        local.get $b\n"
        "        i32.const 8\n"
        "        i32.add\n"
        "        local.get $j\n"
        "        i32.const 20\n"
        "        i32.mul\n"
        "        i32.add\n"
        "        local.set $dst\n"
        "        local.get $dst\n"
        "        local.get $slot\n"
        "        i32.const 20\n"
        "        memory.copy\n"
        "        local.get $slot\n"
        "        local.get $found\n"
        "        i32.eq\n"
        "        if\n"
        "          local.get $dst\n"
        "          local.get $vp\n"
        "          i32.store offset=12\n"
        "          local.get $dst\n"
        "          local.get $vl\n"
        "          i32.store offset=16\n"
        "        end\n"
        "        local.get $j\n"
        "        i32.const 1\n"
        "        i32.add\n"
        "        local.set $j\n"
        "      end\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $i\n"
        "      br $cp\n"
        "    end\n"
        "    end\n"
        "    local.get $found\n"
        "    i32.eqz\n"
        "    if\n"
        "      local.get $b\n"
        "      i32.const 8\n"
        "      i32.add\n"
        "      local.get $j\n"
        "      i32.const 20\n"
        "      i32.mul\n"
        "      i32.add\n"
        "      local.set $dst\n"
        "      local.get $dst\n"
        "      i32.const 1\n"
        "      i32.store\n"
        "      local.get $dst\n"
        "      local.get $kp\n"
        "      i32.store offset=4\n"
        "      local.get $dst\n"
        "      local.get $kl\n"
        "      i32.store offset=8\n"
        "      local.get $dst\n"
        "      local.get $vp\n"
        "      i32.store offset=12\n"
        "      local.get $dst\n"
        "      local.get $vl\n"
        "      i32.store offset=16\n"
        "    end\n"
        "    local.get $b\n"
        "    local.get $ncnt\n"
        "    i32.store offset=4\n"
        "    i32.const 4\n"
        "    call $shadow_pop_n\n"
        "    local.get $w\n"
        "  )"
    )


def _op_map_get(lay: _Layout) -> str:
    # Option<String>: Some = 12 B {1, ptr, len}; None = 4 B {0}.
    # The Option shares the bucket's value bytes (immutable strings);
    # wp is rooted across the Option alloc so the bucket stays live.
    return (
        "  (func $op_map_get (param $wp i32) (param $kp i32) "
        "(param $kl i32) (result i32)\n"
        "    (local $slot i32)\n"
        "    (local $adt i32)\n"
        "    local.get $wp\n"
        "    call $shadow_push\n"
        "    local.get $wp\n"
        "    i32.load offset=8\n"
        "    local.get $kp\n"
        "    local.get $kl\n"
        "    call $bkt_find\n"
        "    local.set $slot\n"
        "    local.get $slot\n"
        "    if\n"
        "      i32.const 12\n"
        "      call $alloc\n"
        "      local.set $adt\n"
        "      local.get $adt\n"
        "      i32.const 1\n"
        "      i32.store\n"
        "      local.get $adt\n"
        "      local.get $slot\n"
        "      i32.load offset=12\n"
        "      i32.store offset=4\n"
        "      local.get $adt\n"
        "      local.get $slot\n"
        "      i32.load offset=16\n"
        "      i32.store offset=8\n"
        "    else\n"
        "      i32.const 4\n"
        "      call $alloc\n"
        "      local.set $adt\n"
        "      local.get $adt\n"
        "      i32.const 0\n"
        "      i32.store\n"
        "    end\n"
        "    i32.const 1\n"
        "    call $shadow_pop_n\n"
        "    local.get $adt\n"
        "  )"
    )


def _op_map_contains(lay: _Layout) -> str:
    return (
        "  (func $op_map_contains (param $wp i32) (param $kp i32) "
        "(param $kl i32) (result i32)\n"
        "    local.get $wp\n"
        "    i32.load offset=8\n"
        "    local.get $kp\n"
        "    local.get $kl\n"
        "    call $bkt_find\n"
        "    i32.const 0\n"
        "    i32.ne\n"
        "  )"
    )


def _op_map_size(lay: _Layout) -> str:
    return (
        "  (func $op_map_size (param $wp i32) (result i64)\n"
        "    (local $b i32)\n"
        "    local.get $wp\n"
        "    i32.load offset=8\n"
        "    local.tee $b\n"
        "    if (result i64)\n"
        "      local.get $b\n"
        "      i32.load offset=4\n"
        "      i64.extend_i32_u\n"
        "    else\n"
        "      i64.const 0\n"
        "    end\n"
        "  )"
    )


def _op_map_remove(lay: _Layout) -> str:
    # Structural rebuild minus the matched slot (host ``map_remove``
    # parity: survivors keep slot order; capacity resized for the new
    # count).
    return (
        "  (func $op_map_remove (param $wp i32) (param $kp i32) "
        "(param $kl i32) (result i32)\n"
        "    (local $ob i32)\n"
        "    (local $ocap i32)\n"
        "    (local $ocnt i32)\n"
        "    (local $found i32)\n"
        "    (local $w i32)\n"
        "    (local $b i32)\n"
        "    (local $cap i32)\n"
        "    (local $ncnt i32)\n"
        "    (local $i i32)\n"
        "    (local $j i32)\n"
        "    (local $slot i32)\n"
        "    local.get $wp\n"
        "    call $shadow_push\n"
        "    local.get $kp\n"
        "    call $shadow_push\n"
        "    local.get $wp\n"
        "    i32.load offset=8\n"
        "    local.set $ob\n"
        "    local.get $ob\n"
        "    if\n"
        "      local.get $ob\n"
        "      i32.load\n"
        "      local.set $ocap\n"
        "      local.get $ob\n"
        "      i32.load offset=4\n"
        "      local.set $ocnt\n"
        "    end\n"
        "    local.get $ob\n"
        "    local.get $kp\n"
        "    local.get $kl\n"
        "    call $bkt_find\n"
        "    local.set $found\n"
        "    local.get $ocnt\n"
        "    local.get $found\n"
        "    i32.const 0\n"
        "    i32.ne\n"
        "    i32.sub\n"
        "    local.set $ncnt\n"
        "    local.get $ncnt\n"
        "    call $bkt_cap\n"
        "    local.set $cap\n"
        "    call $mk_wrapper\n"
        "    local.set $w\n"
        "    local.get $w\n"
        "    call $shadow_push\n"
        "    local.get $cap\n"
        "    i32.const 20\n"
        "    i32.mul\n"
        "    i32.const 8\n"
        "    i32.add\n"
        "    call $alloc\n"
        "    local.set $b\n"
        "    local.get $b\n"
        "    i32.const 0\n"
        "    local.get $cap\n"
        "    i32.const 20\n"
        "    i32.mul\n"
        "    i32.const 8\n"
        "    i32.add\n"
        "    memory.fill\n"
        "    local.get $b\n"
        "    local.get $cap\n"
        "    i32.store\n"
        "    local.get $w\n"
        "    local.get $b\n"
        "    i32.store offset=8\n"
        "    block $copied\n"
        "    loop $cp\n"
        "      local.get $i\n"
        "      local.get $ocap\n"
        "      i32.ge_u\n"
        "      br_if $copied\n"
        "      local.get $ob\n"
        "      i32.const 8\n"
        "      i32.add\n"
        "      local.get $i\n"
        "      i32.const 20\n"
        "      i32.mul\n"
        "      i32.add\n"
        "      local.set $slot\n"
        "      local.get $slot\n"
        "      i32.load\n"
        "      if\n"
        "        local.get $slot\n"
        "        local.get $found\n"
        "        i32.ne\n"
        "        if\n"
        "          local.get $b\n"
        "          i32.const 8\n"
        "          i32.add\n"
        "          local.get $j\n"
        "          i32.const 20\n"
        "          i32.mul\n"
        "          i32.add\n"
        "          local.get $slot\n"
        "          i32.const 20\n"
        "          memory.copy\n"
        "          local.get $j\n"
        "          i32.const 1\n"
        "          i32.add\n"
        "          local.set $j\n"
        "        end\n"
        "      end\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $i\n"
        "      br $cp\n"
        "    end\n"
        "    end\n"
        "    local.get $b\n"
        "    local.get $ncnt\n"
        "    i32.store offset=4\n"
        "    i32.const 3\n"
        "    call $shadow_pop_n\n"
        "    local.get $w\n"
        "  )"
    )


def _map_column_op(fn_name: str, val_offset: int) -> str:
    """Shared body of map_keys (offset 4) / map_values (offset 12).

    Returns the Array<String> (backing, count) pair; element strings
    are SHARED with the bucket (immutable), so the only alloc is the
    backing — wp is rooted across it and the fill loop is alloc-free.
    """
    return (
        f"  (func {fn_name} (param $wp i32) (result i32 i32)\n"
        "    (local $b i32)\n"
        "    (local $cap i32)\n"
        "    (local $cnt i32)\n"
        "    (local $backing i32)\n"
        "    (local $i i32)\n"
        "    (local $j i32)\n"
        "    (local $slot i32)\n"
        "    local.get $wp\n"
        "    i32.load offset=8\n"
        "    local.set $b\n"
        "    local.get $b\n"
        "    if\n"
        "      local.get $b\n"
        "      i32.load offset=4\n"
        "      local.set $cnt\n"
        "    end\n"
        "    local.get $cnt\n"
        "    i32.eqz\n"
        "    if\n"
        "      i32.const 0\n"
        "      i32.const 0\n"
        "      return\n"
        "    end\n"
        "    local.get $b\n"
        "    i32.load\n"
        "    local.set $cap\n"
        "    local.get $wp\n"
        "    call $shadow_push\n"
        "    local.get $cnt\n"
        "    i32.const 3\n"
        "    i32.shl\n"
        "    call $alloc\n"
        "    local.set $backing\n"
        "    i32.const 1\n"
        "    call $shadow_pop_n\n"
        "    block $done\n"
        "    loop $scan\n"
        "      local.get $i\n"
        "      local.get $cap\n"
        "      i32.ge_u\n"
        "      br_if $done\n"
        "      local.get $b\n"
        "      i32.const 8\n"
        "      i32.add\n"
        "      local.get $i\n"
        "      i32.const 20\n"
        "      i32.mul\n"
        "      i32.add\n"
        "      local.set $slot\n"
        "      local.get $slot\n"
        "      i32.load\n"
        "      if\n"
        "        local.get $backing\n"
        "        local.get $j\n"
        "        i32.const 3\n"
        "        i32.shl\n"
        "        i32.add\n"
        "        local.get $slot\n"
        f"        i32.load offset={val_offset}\n"
        "        i32.store\n"
        "        local.get $backing\n"
        "        local.get $j\n"
        "        i32.const 3\n"
        "        i32.shl\n"
        "        i32.add\n"
        "        local.get $slot\n"
        f"        i32.load offset={val_offset + 4}\n"
        "        i32.store offset=4\n"
        "        local.get $j\n"
        "        i32.const 1\n"
        "        i32.add\n"
        "        local.set $j\n"
        "      end\n"
        "      local.get $i\n"
        "      i32.const 1\n"
        "      i32.add\n"
        "      local.set $i\n"
        "      br $scan\n"
        "    end\n"
        "    end\n"
        "    local.get $backing\n"
        "    local.get $cnt\n"
        "  )"
    )


def _op_map_keys(lay: _Layout) -> str:
    return _map_column_op("$op_map_keys", 4)


def _op_map_values(lay: _Layout) -> str:
    return _map_column_op("$op_map_values", 12)


def _op_host_decref_handle(lay: _Layout) -> str:
    # No-op for Map (kind 1) / Set (kind 2); Decimal (kind 3) is
    # family-gated out of the server world — host parity (#706).
    return (
        "  (func $op_host_decref_handle (param $kind i32) "
        "(param $h i32)\n"
        "  )"
    )


def _op_attach_bucket_to_wrapper(lay: _Layout) -> str:
    # #706 tripwire parity: only Decimal (kind=3) may reach this
    # no-op; a Map/Set wrapper routed back through _emit_wrap_handle
    # violates the bucket-as-truth invariant -> trap.
    return (
        "  (func $op_attach_bucket_to_wrapper (param $w i32) "
        "(param $kind i32) (param $h i32)\n"
        "    local.get $kind\n"
        "    i32.const 3\n"
        "    i32.ne\n"
        "    if\n"
        "      unreachable\n"
        "    end\n"
        "  )"
    )


_MAP_OP_EMITTERS: dict[str, Callable[[_Layout], str]] = {
    "map_new": _op_map_new,
    "map_insert$ks_vs": _op_map_insert,
    "map_get$ks_vs": _op_map_get,
    "map_contains$ks": _op_map_contains,
    "map_size": _op_map_size,
    "map_remove$ks": _op_map_remove,
    "map_keys$ks": _op_map_keys,
    "map_values$vs": _op_map_values,
    "host_decref_handle": _op_host_decref_handle,
    "attach_bucket_to_wrapper": _op_attach_bucket_to_wrapper,
}


# ---------------------------------------------------------------------
# Server adapter: the serve wrapper
# ---------------------------------------------------------------------

def _method_src(statics_base: int) -> str:
    """Method discriminant -> (static ptr, len); disc 9 handled by the
    caller (its string arrives via the arena, not the static table)."""
    out: list[str] = [
        "  (func $method_src (param $d i32) (result i32 i32)",
    ]
    off = 0
    for disc, mname in enumerate(_METHOD_NAMES):
        out.append(
            "    local.get $d\n"
            f"    i32.const {disc}\n"
            "    i32.eq\n"
            "    if\n"
            f"      i32.const {statics_base + off}\n"
            f"      i32.const {len(mname)}\n"
            "      return\n"
            "    end"
        )
        off += len(mname)
    out.append("    i32.const 0\n    i32.const 0\n  )")
    return "\n".join(out)


def _respond_err() -> str:
    """``response-outparam.set(err(internal-error(none)))`` (§4.3).

    Flat args per the validated 9-param lowering: outparam handle,
    result disc = 1 (err), error-code disc = internal-error, the
    option<string> payload's none disc, then joined-flat zeros (the
    i64 slot is position 1 of the joined case payloads).
    """
    return (
        "  (func $respond_err (param $outp i32)\n"
        "    local.get $outp\n"
        "    i32.const 1\n"
        f"    i32.const {_ERRCODE_INTERNAL_ERROR}\n"
        "    i32.const 0\n"
        "    i64.const 0\n"
        "    i32.const 0\n"
        "    i32.const 0\n"
        "    i32.const 0\n"
        "    i32.const 0\n"
        "    call $l_outparam_set\n"
        "  )"
    )


def _serve_handle(
    lay: _Layout,
    req: ConstructorLayout,
    resp: ConstructorLayout,
    statics_base: int,
) -> str:
    """The adapter serve wrapper (design §3.2, validated pseudocode).

    Lifted as ``handle(request: own<incoming-request>, response-out:
    own<response-outparam>)``.  Request/Response field offsets come
    from ``CompileResult.adt_layouts`` (shape-checked by
    ``_server_adt_layouts``) — never hardcoded.

    Rooting: mp/pp/w/buf are shadow-pushed across the allocation
    window and popped together after the Request ADT is built (the
    ADT itself needs no push — ``handle``'s own GC prologue roots its
    parameter, and no allocation happens in between).  The
    ``;; root:`` markers are load-bearing for the mutation-validation
    test (string surgery strips one and the GC-stress test must go
    RED).

    No allocations happen after ``vera_handle`` returns (the Response
    decode is read-only; from-list entries go to the arena), so
    ``resp`` and everything it references need no rooting — the same
    argument as host-side ``decode_response_adt``.
    """
    s = {k: lay.slab(k) for k in _SERVER_SLAB}
    slash_ptr = statics_base + sum(len(m) for m in _METHOD_NAMES)
    (m_off, _), (p_off, _), (h_off, _), (b_off, _) = req.field_offsets
    (s_off, _), (rh_off, _), (rb_off, _) = resp.field_offsets
    return f"""  (func $serve_handle (param $req i32) (param $outp i32)
    (local $mdisc i32)
    (local $ms i32)
    (local $ml i32)
    (local $mp i32)
    (local $ps i32)
    (local $pl i32)
    (local $pp i32)
    (local $hdrs i32)
    (local $ents i32)
    (local $ecnt i32)
    (local $i i32)
    (local $e i32)
    (local $kp0 i32)
    (local $kl i32)
    (local $vp0 i32)
    (local $vl i32)
    (local $kc i32)
    (local $vc i32)
    (local $t i32)
    (local $ch i32)
    (local $w i32)
    (local $b i32)
    (local $cap i32)
    (local $cnt i32)
    (local $slot i32)
    (local $dup i32)
    (local $body i32)
    (local $sh i32)
    (local $buf i32)
    (local $bcap i32)
    (local $bn i32)
    (local $lptr i32)
    (local $llen i32)
    (local $new i32)
    (local $adt i32)
    (local $resp i32)
    (local $status i64)
    (local $rw i32)
    (local $rb i32)
    (local $rcap i32)
    (local $ep i32)
    (local $rcnt i32)
    (local $rfields i32)
    (local $orsp i32)
    (local $ob i32)
    (local $os i32)
    (local $wp2 i32)
    (local $wn i32)
    (local $wleft i32)
    call $arena_reset
    ;; ---- method -> GC string ----
    local.get $req
    i32.const {s["mth"]}
    call $l_method
    i32.const {s["mth"]}
    i32.load8_u
    local.set $mdisc
    local.get $mdisc
    i32.const 9
    i32.eq
    if (result i32 i32)
      i32.const {s["mth"] + 4}
      i32.load
      i32.const {s["mth"] + 8}
      i32.load
    else
      local.get $mdisc
      call $method_src
    end
    local.set $ml
    local.set $ms
    i32.const 0
    local.set $mp
    local.get $ml
    if
      local.get $ml
      call $alloc
      local.set $mp
      local.get $mp
      local.get $ms
      local.get $ml
      memory.copy
    end
    local.get $mp
    call $shadow_push ;; root: method
    ;; ---- path-with-query -> GC string ----
    local.get $req
    i32.const {s["path"]}
    call $l_pathq
    i32.const {s["path"]}
    i32.load8_u
    if (result i32 i32)
      i32.const {s["path"] + 4}
      i32.load
      i32.const {s["path"] + 8}
      i32.load
    else
      i32.const {slash_ptr}
      i32.const 1
    end
    local.set $pl
    local.set $ps
    i32.const 0
    local.set $pp
    local.get $pl
    if
      local.get $pl
      call $alloc
      local.set $pp
      local.get $pp
      local.get $ps
      local.get $pl
      memory.copy
    end
    local.get $pp
    call $shadow_push ;; root: path
    ;; ---- headers -> in-guest Map<String, String> ----
    local.get $req
    call $l_headers
    local.set $hdrs
    local.get $hdrs
    i32.const {s["ents"]}
    call $l_entries
    i32.const {s["ents"]}
    i32.load
    local.set $ents
    i32.const {s["ents"] + 4}
    i32.load
    local.set $ecnt
    call $mk_wrapper
    local.set $w
    local.get $w
    call $shadow_push ;; root: headers
    local.get $ecnt
    call $bkt_cap
    local.set $cap
    local.get $cap
    i32.const 20
    i32.mul
    i32.const 8
    i32.add
    call $alloc
    local.set $b
    local.get $b
    i32.const 0
    local.get $cap
    i32.const 20
    i32.mul
    i32.const 8
    i32.add
    memory.fill
    local.get $b
    local.get $cap
    i32.store
    local.get $w
    local.get $b
    i32.store offset=8
    i32.const 0
    local.set $cnt
    i32.const 0
    local.set $i
    block $hdone
    loop $hdr
      local.get $i
      local.get $ecnt
      i32.ge_u
      br_if $hdone
      local.get $ents
      local.get $i
      i32.const 4
      i32.shl
      i32.add
      local.set $e
      local.get $e
      i32.load
      local.set $kp0
      local.get $e
      i32.load offset=4
      local.set $kl
      local.get $e
      i32.load offset=8
      local.set $vp0
      local.get $e
      i32.load offset=12
      local.set $vl
      ;; ASCII-lowercase key copy -> GC (#305 driver parity: k.lower())
      i32.const 0
      local.set $kc
      local.get $kl
      if
        local.get $kl
        call $alloc
        local.set $kc
        i32.const 0
        local.set $t
        block $lcdone
        loop $lc
          local.get $t
          local.get $kl
          i32.ge_u
          br_if $lcdone
          local.get $kp0
          local.get $t
          i32.add
          i32.load8_u
          local.set $ch
          local.get $ch
          i32.const 65
          i32.ge_u
          if
            local.get $ch
            i32.const 90
            i32.le_u
            if
              local.get $ch
              i32.const 32
              i32.add
              local.set $ch
            end
          end
          local.get $kc
          local.get $t
          i32.add
          local.get $ch
          i32.store8
          local.get $t
          i32.const 1
          i32.add
          local.set $t
          br $lc
        end
        end
      end
      ;; dedup: later header wins (#305 dict(headers) parity)
      local.get $b
      local.get $kc
      local.get $kl
      call $bkt_find
      local.set $dup
      local.get $dup
      if
        i32.const 0
        local.set $vc
        local.get $vl
        if
          local.get $vl
          call $alloc
          local.set $vc
          local.get $vc
          local.get $vp0
          local.get $vl
          memory.copy
        end
        local.get $dup
        local.get $vc
        i32.store offset=12
        local.get $dup
        local.get $vl
        i32.store offset=16
      else
        local.get $b
        i32.const 8
        i32.add
        local.get $cnt
        i32.const 20
        i32.mul
        i32.add
        local.set $slot
        local.get $slot
        i32.const 1
        i32.store
        local.get $slot
        local.get $kc
        i32.store offset=4
        local.get $slot
        local.get $kl
        i32.store offset=8
        i32.const 0
        local.set $vc
        local.get $vl
        if
          local.get $vl
          call $alloc
          local.set $vc
          local.get $vc
          local.get $vp0
          local.get $vl
          memory.copy
        end
        local.get $slot
        local.get $vc
        i32.store offset=12
        local.get $slot
        local.get $vl
        i32.store offset=16
        local.get $cnt
        i32.const 1
        i32.add
        local.set $cnt
      end
      local.get $i
      i32.const 1
      i32.add
      local.set $i
      br $hdr
    end
    end
    local.get $b
    local.get $cnt
    i32.store offset=4
    ;; ---- body -> GC buffer (grow-by-doubling, 16 KiB chunks) ----
    local.get $req
    i32.const {s["consume"]}
    call $l_consume
    i32.const {s["consume"]}
    i32.load8_u
    if
      unreachable
    end
    i32.const {s["consume"] + 4}
    i32.load
    local.set $body
    local.get $body
    i32.const {s["stream"]}
    call $l_bstream
    i32.const {s["stream"]}
    i32.load8_u
    if
      unreachable
    end
    i32.const {s["stream"] + 4}
    i32.load
    local.set $sh
    i32.const 4096
    call $alloc
    local.set $buf
    i32.const 4096
    local.set $bcap
    block $beof
    loop $brd
      call $arena_reset
      local.get $sh
      i64.const 16384
      i32.const {s["bread"]}
      call $l_bread
      i32.const {s["bread"]}
      i32.load8_u
      if
        i32.const {s["bread"]}
        i32.load8_u offset=4
        i32.const 1
        i32.eq
        br_if $beof
        i32.const {s["bread"]}
        i32.load offset=8
        call $drop_err
        unreachable
      end
      i32.const {s["bread"]}
      i32.load offset=4
      local.set $lptr
      i32.const {s["bread"]}
      i32.load offset=8
      local.set $llen
      local.get $llen
      i32.eqz
      br_if $brd
      block $capok
      loop $grow
        local.get $bn
        local.get $llen
        i32.add
        local.get $bcap
        i32.le_u
        br_if $capok
        local.get $buf
        call $shadow_push ;; root: body-grow
        local.get $bcap
        i32.const 1
        i32.shl
        call $alloc
        local.set $new
        i32.const 1
        call $shadow_pop_n
        local.get $new
        local.get $buf
        local.get $bn
        memory.copy
        local.get $new
        local.set $buf
        local.get $bcap
        i32.const 1
        i32.shl
        local.set $bcap
        br $grow
      end
      end
      local.get $buf
      local.get $bn
      i32.add
      local.get $lptr
      local.get $llen
      memory.copy
      local.get $bn
      local.get $llen
      i32.add
      local.set $bn
      br $brd
    end
    end
    ;; request-side resources dropped before the handler runs — all
    ;; request data has been copied out (order invariant, §3.2)
    local.get $sh
    call $drop_istream
    local.get $body
    call $drop_inbody
    local.get $hdrs
    call $drop_fields
    local.get $req
    call $drop_inreq
    local.get $buf
    call $shadow_push ;; root: body
    ;; ---- Request ADT (offsets from adt_layouts) ----
    i32.const {req.total_size}
    call $alloc
    local.set $adt
    local.get $adt
    i32.const {req.tag}
    i32.store
    local.get $adt
    local.get $mp
    i32.store offset={m_off}
    local.get $adt
    local.get $ml
    i32.store offset={m_off + 4}
    local.get $adt
    local.get $pp
    i32.store offset={p_off}
    local.get $adt
    local.get $pl
    i32.store offset={p_off + 4}
    local.get $adt
    local.get $w
    i32.store offset={h_off}
    local.get $adt
    local.get $buf
    i32.store offset={b_off}
    local.get $adt
    local.get $bn
    i32.store offset={b_off + 4}
    i32.const 4
    call $shadow_pop_n
    ;; ---- the verified handler ----
    local.get $adt
    call $vera_handle
    local.set $resp
    ;; ---- decode Response {{status i64, headers i32, body pair}} ----
    local.get $resp
    i64.load offset={s_off}
    local.set $status
    local.get $resp
    i32.load offset={rh_off}
    local.set $rw
    ;; response headers Map -> from-list entries in the arena
    call $arena_reset
    global.get $arena_ptr
    local.set $ep
    i32.const 0
    local.set $rcnt
    i32.const 0
    local.set $rb
    local.get $rw
    if
      local.get $rw
      i32.load offset=8
      local.set $rb
    end
    local.get $rb
    if
      local.get $rb
      i32.load
      local.set $rcap
      i32.const 0
      local.set $i
      block $rdone
      loop $rslot
        local.get $i
        local.get $rcap
        i32.ge_u
        br_if $rdone
        local.get $rb
        i32.const 8
        i32.add
        local.get $i
        i32.const 20
        i32.mul
        i32.add
        local.set $slot
        local.get $slot
        i32.load
        if
          ;; arena bound: a header section past the arena would
          ;; silently overrun the GC heap — trap instead (same class
          ;; as the cabi_realloc OOM trap, §4.1)
          local.get $ep
          local.get $rcnt
          i32.const 4
          i32.shl
          i32.add
          i32.const 16
          i32.add
          i32.const {lay.arena_end}
          i32.gt_u
          if
            unreachable
          end
          local.get $ep
          local.get $rcnt
          i32.const 4
          i32.shl
          i32.add
          local.set $e
          local.get $e
          local.get $slot
          i32.load offset=4
          i32.store
          local.get $e
          local.get $slot
          i32.load offset=8
          i32.store offset=4
          local.get $e
          local.get $slot
          i32.load offset=12
          i32.store offset=8
          local.get $e
          local.get $slot
          i32.load offset=16
          i32.store offset=12
          local.get $rcnt
          i32.const 1
          i32.add
          local.set $rcnt
        end
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $rslot
      end
      end
    end
    local.get $ep
    local.get $rcnt
    i32.const {s["flist"]}
    call $l_from_list
    i32.const {s["flist"]}
    i32.load8_u
    if
      ;; forbidden/invalid response header -> graceful 500 (§4.3)
      local.get $outp
      call $respond_err
      return
    end
    i32.const {s["flist"] + 4}
    i32.load
    local.set $rfields
    ;; ---- drive the response half ----
    local.get $rfields
    call $l_new_resp
    local.set $orsp
    ;; status outside u16 would trap in the set-status lift -> pre-
    ;; check and take the graceful path instead (§4.3)
    local.get $status
    i64.const 65535
    i64.gt_u
    if
      local.get $outp
      call $respond_err
      return
    end
    local.get $orsp
    local.get $status
    i32.wrap_i64
    call $l_set_status
    if
      ;; invalid HTTP status -> graceful 500 (§4.3)
      local.get $outp
      call $respond_err
      return
    end
    local.get $orsp
    i32.const {s["rb"]}
    call $l_resp_body
    i32.const {s["rb"]}
    i32.load8_u
    if
      unreachable
    end
    i32.const {s["rb"] + 4}
    i32.load
    local.set $ob
    ;; borrow-before-transfer: .body() done -> outparam.set(ok)
    local.get $outp
    i32.const 0
    local.get $orsp
    i32.const 0
    i64.const 0
    i32.const 0
    i32.const 0
    i32.const 0
    i32.const 0
    call $l_outparam_set
    local.get $ob
    i32.const {s["rb"]}
    call $l_body_write
    i32.const {s["rb"]}
    i32.load8_u
    if
      unreachable
    end
    i32.const {s["rb"] + 4}
    i32.load
    local.set $os
    local.get $resp
    i32.load offset={rb_off}
    local.set $wp2
    local.get $resp
    i32.load offset={rb_off + 4}
    local.set $wleft
    block $wdone
    loop $wchunk
      local.get $wleft
      i32.eqz
      br_if $wdone
      local.get $wleft
      i32.const 4096
      i32.lt_u
      if (result i32)
        local.get $wleft
      else
        i32.const 4096
      end
      local.set $wn
      local.get $os
      local.get $wp2
      local.get $wn
      i32.const {s["bwf"]}
      call $l_bwf
      i32.const {s["bwf"]}
      i32.load8_u
      if
        unreachable
      end
      local.get $wp2
      local.get $wn
      i32.add
      local.set $wp2
      local.get $wleft
      local.get $wn
      i32.sub
      local.set $wleft
      br $wchunk
    end
    end
    ;; child output-stream dropped before finish (order invariant)
    local.get $os
    call $drop_ostream
    local.get $ob
    i32.const 0
    i32.const 0
    i32.const {s["finish"]}
    call $l_finish
  )"""


# ---------------------------------------------------------------------
# Server component assembly
# ---------------------------------------------------------------------

#: wasi:http/types@0.2.0 import block (design §2.1) — every type,
#: function spelling, and the full 39-case error-code variant were
#: validated by the Stage-D echo.wat probe (parse first try + live
#: serve).  Aliases `$OS`/`$IS` come from the always-present
#: io/streams import.  The trailing aliases feed the resource drops
#: and the incoming-handler lift.
_HTTP_TYPES_IFACE = """\
  (import "wasi:http/types@0.2.0" (instance $types
    (alias outer $C $OS (type $os0))
    (alias outer $C $IS (type $is0))
    (export "fields" (type $fields (sub resource)))
    (export "incoming-request" (type $inreq (sub resource)))
    (export "incoming-body" (type $inbody (sub resource)))
    (export "response-outparam" (type $outparam (sub resource)))
    (export "outgoing-response" (type $outresp (sub resource)))
    (export "outgoing-body" (type $outbody (sub resource)))
    (type $method' (variant
      (case "get") (case "head") (case "post") (case "put")
      (case "delete") (case "connect") (case "options") (case "trace")
      (case "patch") (case "other" string)))
    (export "method" (type $method (eq $method')))
    (type $header-error' (variant
      (case "invalid-syntax") (case "forbidden") (case "immutable")))
    (export "header-error" (type $header-error (eq $header-error')))
    (type $dns-error-payload' (record
      (field "rcode" (option string))
      (field "info-code" (option u16))))
    (export "DNS-error-payload" (type $dns-error-payload (eq $dns-error-payload')))
    (type $tls-alert-received-payload' (record
      (field "alert-id" (option u8))
      (field "alert-message" (option string))))
    (export "TLS-alert-received-payload" (type $tls-alert-received-payload (eq $tls-alert-received-payload')))
    (type $field-size-payload' (record
      (field "field-name" (option string))
      (field "field-size" (option u32))))
    (export "field-size-payload" (type $field-size-payload (eq $field-size-payload')))
    (type $error-code' (variant
      (case "DNS-timeout")
      (case "DNS-error" $dns-error-payload)
      (case "destination-not-found")
      (case "destination-unavailable")
      (case "destination-IP-prohibited")
      (case "destination-IP-unroutable")
      (case "connection-refused")
      (case "connection-terminated")
      (case "connection-timeout")
      (case "connection-read-timeout")
      (case "connection-write-timeout")
      (case "connection-limit-reached")
      (case "TLS-protocol-error")
      (case "TLS-certificate-error")
      (case "TLS-alert-received" $tls-alert-received-payload)
      (case "HTTP-request-denied")
      (case "HTTP-request-length-required")
      (case "HTTP-request-body-size" (option u64))
      (case "HTTP-request-method-invalid")
      (case "HTTP-request-URI-invalid")
      (case "HTTP-request-URI-too-long")
      (case "HTTP-request-header-section-size" (option u32))
      (case "HTTP-request-header-size" (option $field-size-payload))
      (case "HTTP-request-trailer-section-size" (option u32))
      (case "HTTP-request-trailer-size" $field-size-payload)
      (case "HTTP-response-incomplete")
      (case "HTTP-response-header-section-size" (option u32))
      (case "HTTP-response-header-size" $field-size-payload)
      (case "HTTP-response-body-size" (option u64))
      (case "HTTP-response-trailer-section-size" (option u32))
      (case "HTTP-response-trailer-size" $field-size-payload)
      (case "HTTP-response-transfer-coding" (option string))
      (case "HTTP-response-content-coding" (option string))
      (case "HTTP-response-timeout")
      (case "HTTP-upgrade-failed")
      (case "HTTP-protocol-error")
      (case "loop-detected")
      (case "configuration-error")
      (case "internal-error" (option string))))
    (export "error-code" (type $error-code (eq $error-code')))
    (export "[method]incoming-request.method" (func
      (param "self" (borrow $inreq)) (result $method)))
    (export "[method]incoming-request.path-with-query" (func
      (param "self" (borrow $inreq)) (result (option string))))
    (export "[method]incoming-request.headers" (func
      (param "self" (borrow $inreq)) (result (own $fields))))
    (export "[method]incoming-request.consume" (func
      (param "self" (borrow $inreq)) (result (result (own $inbody)))))
    (export "[method]incoming-body.stream" (func
      (param "self" (borrow $inbody)) (result (result (own $is0)))))
    (export "[method]fields.entries" (func
      (param "self" (borrow $fields))
      (result (list (tuple string (list u8))))))
    (export "[static]fields.from-list" (func
      (param "entries" (list (tuple string (list u8))))
      (result (result (own $fields) (error $header-error)))))
    (export "[constructor]outgoing-response" (func
      (param "headers" (own $fields)) (result (own $outresp))))
    (export "[method]outgoing-response.set-status-code" (func
      (param "self" (borrow $outresp)) (param "status-code" u16)
      (result (result))))
    (export "[method]outgoing-response.body" (func
      (param "self" (borrow $outresp)) (result (result (own $outbody)))))
    (export "[method]outgoing-body.write" (func
      (param "self" (borrow $outbody)) (result (result (own $os0)))))
    (export "[static]outgoing-body.finish" (func
      (param "this" (own $outbody)) (param "trailers" (option (own $fields)))
      (result (result (error $error-code)))))
    (export "[static]response-outparam.set" (func
      (param "param" (own $outparam))
      (param "response" (result (own $outresp) (error $error-code)))))))
  (alias export $types "incoming-request" (type $IR))
  (alias export $types "response-outparam" (type $RO))
  (alias export $types "incoming-body" (type $IB))
  (alias export $types "fields" (type $FLDS))"""

#: wasi:http canon lowers (design §2.2 flattening table): key ->
#: (component-level definition, adapter import decl, with-instance
#: export line) — same triple shape as ``_LOWERS``.
_SERVER_LOWERS: dict[str, tuple[str, str, str]] = {
    "req-method": (
        '  (core func $l_method (canon lower\n'
        '    (func $types "[method]incoming-request.method")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "req-method" (func $l_method (param i32 i32)))',
        '      (export "req-method" (func $l_method))',
    ),
    "req-path": (
        '  (core func $l_pathq (canon lower\n'
        '    (func $types "[method]incoming-request.path-with-query")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "req-path" (func $l_pathq (param i32 i32)))',
        '      (export "req-path" (func $l_pathq))',
    ),
    "req-headers": (
        '  (core func $l_headers (canon lower\n'
        '    (func $types "[method]incoming-request.headers")))',
        '  (import "wasi" "req-headers"'
        ' (func $l_headers (param i32) (result i32)))',
        '      (export "req-headers" (func $l_headers))',
    ),
    "req-consume": (
        '  (core func $l_consume (canon lower\n'
        '    (func $types "[method]incoming-request.consume")\n'
        '    (memory $mem)))',
        '  (import "wasi" "req-consume" (func $l_consume (param i32 i32)))',
        '      (export "req-consume" (func $l_consume))',
    ),
    "body-stream": (
        '  (core func $l_bstream (canon lower\n'
        '    (func $types "[method]incoming-body.stream")\n'
        '    (memory $mem)))',
        '  (import "wasi" "body-stream" (func $l_bstream (param i32 i32)))',
        '      (export "body-stream" (func $l_bstream))',
    ),
    "fields-entries": (
        '  (core func $l_entries (canon lower\n'
        '    (func $types "[method]fields.entries")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "fields-entries"'
        ' (func $l_entries (param i32 i32)))',
        '      (export "fields-entries" (func $l_entries))',
    ),
    "fields-from-list": (
        '  (core func $l_from_list (canon lower\n'
        '    (func $types "[static]fields.from-list")\n'
        '    (memory $mem)))',
        '  (import "wasi" "fields-from-list"'
        ' (func $l_from_list (param i32 i32 i32)))',
        '      (export "fields-from-list" (func $l_from_list))',
    ),
    "new-response": (
        '  (core func $l_new_resp (canon lower\n'
        '    (func $types "[constructor]outgoing-response")))',
        '  (import "wasi" "new-response"'
        ' (func $l_new_resp (param i32) (result i32)))',
        '      (export "new-response" (func $l_new_resp))',
    ),
    "set-status": (
        '  (core func $l_set_status (canon lower\n'
        '    (func $types "[method]outgoing-response.set-status-code")))',
        '  (import "wasi" "set-status"'
        ' (func $l_set_status (param i32 i32) (result i32)))',
        '      (export "set-status" (func $l_set_status))',
    ),
    "response-body": (
        '  (core func $l_resp_body (canon lower\n'
        '    (func $types "[method]outgoing-response.body")\n'
        '    (memory $mem)))',
        '  (import "wasi" "response-body"'
        ' (func $l_resp_body (param i32 i32)))',
        '      (export "response-body" (func $l_resp_body))',
    ),
    "body-write": (
        '  (core func $l_body_write (canon lower\n'
        '    (func $types "[method]outgoing-body.write")\n'
        '    (memory $mem)))',
        '  (import "wasi" "body-write"'
        ' (func $l_body_write (param i32 i32)))',
        '      (export "body-write" (func $l_body_write))',
    ),
    "body-finish": (
        '  (core func $l_finish (canon lower\n'
        '    (func $types "[static]outgoing-body.finish")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "body-finish"'
        ' (func $l_finish (param i32 i32 i32 i32)))',
        '      (export "body-finish" (func $l_finish))',
    ),
    "outparam-set": (
        '  (core func $l_outparam_set (canon lower\n'
        '    (func $types "[static]response-outparam.set")\n'
        '    (memory $mem) (realloc $realloc)))',
        '  (import "wasi" "outparam-set" (func $l_outparam_set'
        ' (param i32 i32 i32 i32 i64 i32 i32 i32 i32)))',
        '      (export "outparam-set" (func $l_outparam_set))',
    ),
}
_SERVER_LOWER_ORDER: tuple[str, ...] = (
    "req-method", "req-path", "req-headers", "req-consume",
    "body-stream", "fields-entries", "fields-from-list", "new-response",
    "set-status", "response-body", "body-write", "body-finish",
    "outparam-set",
)

_SERVER_DROPS: dict[str, tuple[str, str, str]] = {
    "inreq": (
        '  (core func $drop_inreq (canon resource.drop $IR))',
        '  (import "wasi" "drop-inreq" (func $drop_inreq (param i32)))',
        '      (export "drop-inreq" (func $drop_inreq))',
    ),
    "inbody": (
        '  (core func $drop_inbody (canon resource.drop $IB))',
        '  (import "wasi" "drop-inbody" (func $drop_inbody (param i32)))',
        '      (export "drop-inbody" (func $drop_inbody))',
    ),
    "fields": (
        '  (core func $drop_fields (canon resource.drop $FLDS))',
        '  (import "wasi" "drop-fields" (func $drop_fields (param i32)))',
        '      (export "drop-fields" (func $drop_fields))',
    ),
}
_SERVER_DROP_ORDER: tuple[str, ...] = ("inreq", "inbody", "fields")

#: Lowers/drops the serve wrapper itself needs regardless of the
#: program's op set (body read, response write, error drop, stream
#: drops).
_SERVER_BASE_LOWERS = frozenset({"bwf", "bread"})
_SERVER_BASE_DROPS = frozenset({"error", "istream", "ostream"})


def _server_helper_funcs(
    used: dict[str, _OpSpec], lay: _Layout, statics_base: int,
) -> list[str]:
    """Adapter helpers for the server world (always-on rooting + map
    machinery; IO helpers gated by the op set)."""
    names = set(used)
    out = [
        "  (func $arena_reset\n"
        f"    i32.const {lay.bump_start}\n"
        "    global.set $arena_ptr\n"
        "  )",
        _SHADOW_PUSH_FN,
        _SHADOW_POP_FN,
        _BYTES_EQ_FN,
        _mk_wrapper(),
        _bkt_find(),
        _bkt_cap(),
        _method_src(statics_base),
        _respond_err(),
    ]
    if "print" in names:
        out.append(_ensure_handle("stdout", "$l_get_stdout"))
    if names & {"stderr", "contract_fail"}:
        out.append(_ensure_handle("stderr", "$l_get_stderr"))
    if names & {"print", "stderr", "contract_fail"}:
        out.append(_write_or_trap(lay))
    return out


def _server_adapter_fields(
    used: dict[str, _OpSpec],
    lay: _Layout,
    req: ConstructorLayout,
    resp: ConstructorLayout,
) -> list[str]:
    """Emit the server adapter core module's fields."""
    lowers = sorted(
        _SERVER_BASE_LOWERS.union(*(s.lowers for s in used.values()))
        if used else _SERVER_BASE_LOWERS
    )
    drops = sorted(
        _SERVER_BASE_DROPS.union(*(s.drops for s in used.values()))
        if used else _SERVER_BASE_DROPS
    )

    fields: list[str] = [
        '  (import "env" "memory" (memory 1))',
        f'  (import "env" "tbl" (table {_SERVER_TABLE_SIZE} funcref))',
        '  (import "env" "arena_ptr" (global $arena_ptr (mut i32)))',
        '  (import "env" "alloc" (func $alloc (param i32) (result i32)))',
        '  (import "env" "gc_sp" (global $gc_sp (mut i32)))',
        '  (import "env" "gc_stack_limit" (global $gc_stack_limit i32))',
        '  (import "env" "vera_handle"'
        ' (func $vera_handle (param i32) (result i32)))',
    ]
    for key in lowers:
        fields.append(_LOWERS[key][1])
    for key in _SERVER_LOWER_ORDER:
        fields.append(_SERVER_LOWERS[key][1])
    for key in drops:
        fields.append(_DROPS[key][1])
    for key in _SERVER_DROP_ORDER:
        fields.append(_SERVER_DROPS[key][1])

    names = set(used)
    if "print" in names:
        fields.append("  (global $stdout_h (mut i32) (i32.const -1))")
    if names & {"stderr", "contract_fail"}:
        fields.append("  (global $stderr_h (mut i32) (i32.const -1))")

    segments, statics_base, _bump = _build_server_statics(lay.arena_base)
    fields += segments
    fields += _server_helper_funcs(used, lay, statics_base)

    for name in sorted(used, key=lambda n: used[n].slot):
        emitter = _MAP_OP_EMITTERS.get(name) or _OP_EMITTERS[name]
        fields.append(emitter(lay))
    fields.append(_serve_handle(lay, req, resp, statics_base))
    for name in sorted(used, key=lambda n: used[n].slot):
        fields.append(
            f"  (elem (i32.const {used[name].slot}) "
            f"func {_op_ident(name)})"
        )
    fields.append('  (export "handle" (func $serve_handle))')
    return fields


def _assemble_server_component(
    main_fields: list[str],
    used: dict[str, _OpSpec],
    lay: _Layout,
    req: ConstructorLayout,
    resp: ConstructorLayout,
) -> str:
    """Assemble the server-world component text (design §1.1)."""
    ifaces = _iface_closure(
        {"io/error", "io/streams"}.union(
            *(s.ifaces for s in used.values()),
        ) if used else {"io/error", "io/streams"}
    )
    lowers = sorted(
        _SERVER_BASE_LOWERS.union(*(s.lowers for s in used.values()))
        if used else _SERVER_BASE_LOWERS
    )
    drops = sorted(
        _SERVER_BASE_DROPS.union(*(s.drops for s in used.values()))
        if used else _SERVER_BASE_DROPS
    )

    parts: list[str] = ["(component $C"]
    for iface in ifaces:
        parts.append(_IFACES[iface])
    parts.append(_HTTP_TYPES_IFACE)

    parts.append("  (core module $Main")
    parts.extend("  " + line if line else line for line in main_fields)
    parts.append("  )")
    parts.append("  (core instance $main (instantiate $Main))")
    parts.append('  (alias core export $main "memory" (core memory $mem))')
    parts.append(
        '  (alias core export $main "cabi_realloc" (core func $realloc))'
    )
    parts.append('  (alias core export $main "wasi_tbl" (core table $tbl))')
    parts.append(
        '  (alias core export $main "wasi_arena_ptr" '
        "(core global $g_arena))"
    )
    parts.append('  (alias core export $main "alloc" (core func $f_alloc))')
    parts.append('  (alias core export $main "gc_sp" (core global $g_sp))')
    parts.append(
        '  (alias core export $main "gc_stack_limit" '
        "(core global $g_lim))"
    )
    parts.append('  (alias core export $main "handle" (core func $f_handle))')

    for key in lowers:
        parts.append(_LOWERS[key][0])
    for key in _SERVER_LOWER_ORDER:
        parts.append(_SERVER_LOWERS[key][0])
    for key in drops:
        parts.append(_DROPS[key][0])
    for key in _SERVER_DROP_ORDER:
        parts.append(_SERVER_DROPS[key][0])

    parts.append("  (core module $Adapter")
    parts.extend(
        "  " + line if line else line
        for line in _server_adapter_fields(used, lay, req, resp)
    )
    parts.append("  )")
    parts.append("  (core instance $adapter (instantiate $Adapter")
    parts.append('    (with "env" (instance')
    parts.append('      (export "memory" (memory $mem))')
    parts.append('      (export "tbl" (table $tbl))')
    parts.append('      (export "arena_ptr" (global $g_arena))')
    parts.append('      (export "alloc" (func $f_alloc))')
    parts.append('      (export "gc_sp" (global $g_sp))')
    parts.append('      (export "gc_stack_limit" (global $g_lim))')
    parts.append('      (export "vera_handle" (func $f_handle))')
    parts.append("    ))")
    parts.append('    (with "wasi" (instance')
    for key in lowers:
        parts.append(_LOWERS[key][2])
    for key in _SERVER_LOWER_ORDER:
        parts.append(_SERVER_LOWERS[key][2])
    for key in drops:
        parts.append(_DROPS[key][2])
    for key in _SERVER_DROP_ORDER:
        parts.append(_SERVER_DROPS[key][2])
    parts.append("    ))")
    parts.append("  ))")

    parts.append(
        '  (func $handle_l (param "request" (own $IR)) '
        '(param "response-out" (own $RO))\n'
        '    (canon lift (core func $adapter "handle")))'
    )
    parts.append('  (instance $ih (export "handle" (func $handle_l)))')
    parts.append(
        '  (export "wasi:http/incoming-handler@0.2.0" (instance $ih))'
    )
    parts.append(")")
    return "\n".join(parts)


def _emit_server_component(result: CompileResult) -> str:
    """Server-world emission pipeline (validate -> gate -> transform ->
    assemble); see ``emit_wasi_component``."""
    # Local import: the shared #305 handler validator lives with the
    # host serve driver (single source of truth for both serving
    # surfaces); importing it lazily keeps this module free of
    # wasmtime-loading deps for cli-world emission.
    from vera.runtime.server import validate_handler

    validate_handler(result, context="--target wasi-p2 --world server")
    _gate_families_server(result)
    req, resp = _server_adt_layouts(result)
    used = _parse_server_imports(result.wat)
    main_fields, layout = _transform_main_server(result.wat, used)
    return _assemble_server_component(main_fields, used, layout, req, resp)
