"""WASM heap marshalling helpers for the Vera runtime.

Memory read/write, shadow-stack GC rooting, wrapper-ADT handle tagging,
the Map/Set bucket codec, and Result/Option/Array allocation -- all
parameterised by the `wasmtime.Caller` (memory is reached via
`caller["memory"]` / `caller["alloc"]`), so they are plain module-level
functions.  Extracted from `execute()` in `vera/codegen/api.py` (#421).
"""

from __future__ import annotations

import struct
from typing import Any

import wasmtime

from vera.runtime.text import safe_utf8_decode


def _read_wasm_string(
    caller: wasmtime.Caller, ptr: int, length: int,
) -> str:
    """Read a UTF-8 string from WASM memory.

    Uses ``errors="replace"`` so that a corrupt (ptr, len) pair from
    an upstream codegen bug surfaces as U+FFFD replacement characters
    rather than a raw ``UnicodeDecodeError`` escaping through
    wasmtime's trampoline (#589).  Path / env-var / file-content
    consumers downstream may then surface their own "file not found"
    / "value not set" errors when the replacement chars don't match
    anything, which is a strict improvement over a Python traceback.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    buf = memory.data_ptr(caller)
    return safe_utf8_decode(bytes(buf[ptr:ptr + length]))

def _read_string_export(
    memory: wasmtime.Memory,
    store: wasmtime.Store,
    ptr: int,
    length: int,
) -> str | None:
    """Read a String ``(ptr, len)`` from a module's exported memory after a run.

    Post-execution sibling of :func:`_read_wasm_string`: the return value of a
    String-typed ``main`` is a ``(ptr, len)`` pair into the exported ``memory``,
    read via the ``store`` (there is no live ``caller`` once the call has
    returned).  Returns the safe-decoded string, or ``None`` when ``(ptr, len)``
    is out of bounds or ``length`` is negative -- the caller then falls back to
    surfacing the raw pointer.  Decoding goes through :func:`safe_utf8_decode`,
    so corrupt return bytes surface as U+FFFD rather than a ``UnicodeDecodeError``
    escaping wasmtime's trampoline (#589 / #592); ``errors="replace"`` also keeps
    the value typed ``str`` instead of the old try/except -> pointer fallback
    that silently mutated ``str`` into ``int`` on invalid UTF-8.
    """
    if length < 0:
        return None
    mem_size = memory.data_len(store)
    if not (0 <= ptr and ptr + length <= mem_size):
        return None
    buf = memory.data_ptr(store)
    return safe_utf8_decode(bytes(buf[ptr:ptr + length]))

def _write_bytes(
    caller: wasmtime.Caller, offset: int, data: bytes,
) -> None:
    """Write raw bytes into WASM linear memory.

    Uses wasmtime's batched ``Memory.write`` (one bounds-checked
    copy) rather than a per-byte ``data_ptr`` loop: the old loop was
    O(n) Python-level assignments and turned bucket-array writes into
    an O(N²) hot path on large Map / Set chains (#706).
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    memory.write(caller, data, offset)

def _write_i32(
    caller: wasmtime.Caller, offset: int, value: int,
) -> None:
    """Write a little-endian i32 into WASM memory."""
    _write_bytes(caller, offset, struct.pack("<I", value & 0xFFFF_FFFF))

def _call_alloc(caller: wasmtime.Caller, size: int) -> int:
    """Call the exported $alloc to allocate WASM heap memory."""
    alloc_fn = caller["alloc"]
    assert isinstance(alloc_fn, wasmtime.Func)  # noqa: S101
    ptr = alloc_fn(caller, size)
    assert isinstance(ptr, int)  # noqa: S101
    return ptr

def _read_i32_at(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i32 from WASM memory at `offset`.

    Module-factory-level counterpart to ``_write_i32`` (line ~944).
    A nested ``_read_i32`` exists later inside the decimal closures;
    this version is shared by all module-level helpers that need
    to inspect linear memory (e.g. the bucket-array
    helpers added below for #695/#705).
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    buf = memory.data_ptr(caller)
    return int(struct.unpack_from("<I", bytes(buf[offset:offset + 4]))[0])

def _read_bytes_at(
    caller: wasmtime.Caller, offset: int, length: int,
) -> bytes:
    """Read `length` raw bytes from WASM linear memory at `offset`."""
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    buf = memory.data_ptr(caller)
    return bytes(buf[offset:offset + length])

# ------------------------------------------------------------------
# #706: Map / Set bucket-array sizing
# ------------------------------------------------------------------
# The bucket codec itself (header + 20-byte slots) lives further
# down near the wrapper helpers; this is just the shared minimum-
# capacity constant.

# Minimum bucket-array capacity.  Small enough to keep memory
# footprint reasonable for empty / tiny maps; large enough that
# parser-built maps with up to 4 keys avoid an immediate grow.
# Caller is responsible for sizing up (typically ``max(_BUCKET_
# INITIAL_CAPACITY, len(d) * 2)`` to keep linear-probe scans
# short).
_BUCKET_INITIAL_CAPACITY = 8

# ------------------------------------------------------------------
# #692: Host-side shadow-stack rooting for multi-alloc walkers
# ------------------------------------------------------------------
#
# The conservative GC scan in ``$gc_collect`` (Phase 2a) only walks
# the WASM shadow stack (``$gc_sp`` .. ``$gc_stack_limit``) when
# tracing roots.  Host code that holds WASM heap pointers in
# Python locals across multiple ``_call_alloc`` calls is therefore
# invisible to GC — if one of those allocs triggers
# ``$gc_collect`` (because bump-alloc would overflow current
# memory), the Python-held pointers are reclaimed and the next
# write scribbles into freed memory → free-list corruption →
# ``Out-of-bounds memory access`` trap from inside ``$alloc``.
# Same #570/#515/#593 bug class but on the host side.
#
# ``_ShadowGuard`` provides exception-safe push/pop discipline.
# Used by ``write_html`` / ``write_json`` / markdown serde to
# root intermediate ``arr_ptr`` / ``name_ptr`` / ``wrapper_ptr``
# across sub-tree recursion and the final Result wrapper alloc.
#
# Design: ``__enter__`` snapshots the current ``$gc_sp``;
# ``__exit__`` resets ``$gc_sp`` to that snapshot, atomically
# popping every entry pushed within the ``with`` block — on both
# success and exception paths.  Callers push freely without
# counting; the outer ``with`` is the unwind boundary.

class _ShadowGuard:
    """Push intermediate WASM heap pointers onto the GC shadow
    stack so they survive any ``$gc_collect`` that fires during
    a multi-alloc host walker.  Exception-safe — ``__exit__``
    resets ``$gc_sp`` to the entry value on both success and
    exception paths.  See #692."""

    __slots__ = ("_caller", "_sp_global", "_limit_global", "_initial_sp")

    def __init__(self, caller: wasmtime.Caller) -> None:
        self._caller = caller
        # Lookup-failure path: a host walker should never run
        # against a module that didn't export ``$gc_sp`` /
        # ``$gc_stack_limit`` (assembly.py exports both whenever
        # ``$gc_collect`` is emitted, and any host walker
        # requires the GC).  But hand-crafted ``.wat`` fixtures
        # or future host imports that bypass the codegen flow
        # could trigger the KeyError below.  Re-raise as a
        # clearer ``RuntimeError`` so the wasmtime trampoline
        # surfaces a diagnostic that names the missing exports
        # rather than a bare ``KeyError`` becoming a generic
        # "python exception" trap.
        try:
            sp_global = caller["gc_sp"]
            limit_global = caller["gc_stack_limit"]
        except KeyError as exc:
            raise RuntimeError(
                "#692: host walker requires the module to "
                "export `$gc_sp` and `$gc_stack_limit` (missing "
                f"{exc}); the calling module was built without "
                "GC support",
            ) from exc
        assert isinstance(sp_global, wasmtime.Global)  # noqa: S101
        self._sp_global = sp_global
        assert isinstance(limit_global, wasmtime.Global)  # noqa: S101
        self._limit_global = limit_global
        self._initial_sp: int | None = None

    def __enter__(self) -> "_ShadowGuard":
        sp = self._sp_global.value(self._caller)
        assert isinstance(sp, int)  # noqa: S101
        self._initial_sp = sp
        return self

    def push(self, ptr: int) -> int:
        """Push ``ptr`` onto the shadow stack.  Returns ``ptr``
        for chaining inside an assignment expression."""
        sp = self._sp_global.value(self._caller)
        limit = self._limit_global.value(self._caller)
        assert isinstance(sp, int)  # noqa: S101
        assert isinstance(limit, int)  # noqa: S101
        if sp >= limit:
            # Same diagnostic shape as the WAT-side overflow path
            # (``unreachable`` in ``gc_shadow_push``) — surface
            # as a host-side error rather than a wasmtime trap.
            raise RuntimeError(
                f"#692: host shadow-stack overflow "
                f"(sp={sp}, limit={limit})",
            )
        # Write i32 little-endian at [gc_sp].  Re-acquire
        # ``data_ptr`` each push because ``memory.grow`` (which
        # can fire inside ``_call_alloc``) can move the buffer.
        # Byte-by-byte indexing through the ctypes pointer
        # matches ``_write_bytes`` — ``struct.pack_into`` does
        # NOT work here because wasmtime-py's ``data_ptr``
        # returns an LP_c_ubyte, which lacks the buffer
        # protocol that ``pack_into`` requires.
        memory = self._caller["memory"]
        assert isinstance(memory, wasmtime.Memory)  # noqa: S101
        buf = memory.data_ptr(self._caller)
        packed = struct.pack("<I", ptr & 0xFFFF_FFFF)
        for i, b in enumerate(packed):
            buf[sp + i] = b
        # Advance gc_sp by 4 (i32 width).
        self._sp_global.set_value(self._caller, sp + 4)
        return ptr

    def __exit__(
        self,
        exc_type: object,
        exc_val: object,
        exc_tb: object,
    ) -> None:
        # Restore gc_sp to its entry value — atomically pops
        # everything pushed within the ``with`` block, regardless
        # of whether we're exiting normally or via exception.
        # ``__enter__`` always sets ``_initial_sp`` before
        # returning, so ``__exit__`` should always have a
        # snapshot to restore.  The assert pins the invariant —
        # if it ever fails, someone is calling ``__exit__``
        # without going through ``__enter__`` (i.e. misuse of
        # the context manager outside a ``with`` block).
        assert self._initial_sp is not None  # noqa: S101
        self._sp_global.set_value(
            self._caller, self._initial_sp,
        )

# #573: wrapper-ADT layout constants (must match
# ``vera/wasm/calls_containers.py``).  Tag values are picked
# well outside the user-ADT tag range as a debugging aid; the
# wrap-table is the source of truth for "is this object a
# wrapper", so a tag collision wouldn't cause incorrect
# destructor firing.
_WRAP_KIND_MAP = 1
_WRAP_KIND_SET = 2
_WRAP_KIND_DECIMAL = 3
_MAP_HANDLE_TAG = 0xFEEDC001
_SET_HANDLE_TAG = 0xFEEDC002
_DECIMAL_HANDLE_TAG = 0xFEEDC003
_KIND_TO_TAG_API = {
    _WRAP_KIND_MAP: _MAP_HANDLE_TAG,
    _WRAP_KIND_SET: _SET_HANDLE_TAG,
    _WRAP_KIND_DECIMAL: _DECIMAL_HANDLE_TAG,
}
# #695/#706: 12-byte wrapper with a ``bucket_ptr`` field at +8.
# Layout depends on the type:
#   +0  tag (i32)                                 [#573]
#   +4  Decimal: handle | 0x80000000 (bit-31)     [#578]
#       Map / Set: vestigial (0) — no handle post-#706
#   +8  bucket_ptr (i32, real heap pointer or 0)  [#695/#706]
#
# #706: for Map / Set the ``bucket_ptr`` points to the WASM-side
# bucket that IS the map / set (see ``_alloc_bucket`` and the codec
# below); the host imports read and rebuild it directly — there is
# no ``_map_store`` / ``_set_store`` mirror.  Decimal leaves it 0
# (value-typed) and the conservative scan skips 0 as
# out-of-heap-range.  Must agree with ``_WRAPPER_BODY_SIZE`` in
# ``vera/wasm/calls_containers.py``.
_WRAPPER_BODY_SIZE = 12

def _call_register_wrapper(
    caller: wasmtime.Caller, ptr: int, kind: int, handle: int,
) -> None:
    """Register a wrapper ADT with the WASM-side wrap table.

    Calls the exported ``$register_wrapper`` so Phase 2c of
    ``$gc_collect`` will fire ``host_decref_handle(kind, handle)``
    when ``ptr`` becomes unreachable.  No-op when the WAT
    module didn't enable the wrap table (i.e. no Map / Set /
    Decimal use); host-side JSON / HTML parsers can call this
    unconditionally and it'll just skip.
    """
    register_fn = caller["register_wrapper"]
    if register_fn is None:  # pragma: no cover — wrap table disabled
        return
    assert isinstance(register_fn, wasmtime.Func)  # noqa: S101
    register_fn(caller, ptr, kind, handle)

def _validate_wrap_handle(
    raw_handle: object, kind: int, body_ptr: int,
) -> None:
    """#578 invariant: raw_handle must fit in 31 unsigned bits.

    Wrapper ADTs store ``raw_handle | 0x80000000`` at body offset 4 so
    the in-heap field is structurally outside the conservative-scan
    heap-range check (`heap_ptr` is hard-capped at 0x80000000 by the
    `$alloc` heap-ceiling guard).  The unwrap site recovers the raw
    handle with ``& 0x7FFFFFFF``.  Both directions break silently
    outside ``[0, 0x80000000)``:

    - Negative ints have bit 31 set in two's complement.
      ``raw_handle | 0x80000000`` is a no-op and the unwrap mask
      returns the WRONG handle.
    - Values ``>= 0x80000000`` alias into the top half and collide
      with the tag-bit pattern.
    - Values ``>= 0x100000000`` truncate on ``_write_i32`` and
      silently lose information.
    - Non-int values would ``TypeError`` deeper in the stack;
      catching them here makes the diagnostic actionable.
    - ``bool`` values: Python's ``bool`` subclasses ``int``, so
      ``isinstance(True, int)`` is ``True`` and the value would
      pass an ``isinstance``-only check, silently aliasing to
      handles 1 and 0.  The strict ``type(raw_handle) is int``
      check rejects bools without accepting any int subclass.

    Practical alloc counters are bounded well below 2^31 — a 2B-handle
    session is wall-clock infeasible — but a silent round-trip
    failure is exactly the corruption class #578 sought to eliminate.
    Fail fast.

    Module-level helper so it can be unit-tested directly without
    standing up a wasmtime instance (``_wrap_handle`` is nested
    inside ``execute()`` and not importable on its own).
    """
    # ``type(x) is int`` rather than ``isinstance(x, int)`` so we
    # reject ``bool`` (which would otherwise pass — bool subclasses
    # int in Python and silently aliases to handles 0 / 1).
    if not (
        type(raw_handle) is int
        and 0 <= raw_handle < 0x80000000
    ):
        raise RuntimeError(
            f"#578: raw_handle={raw_handle!r} (kind={kind!r}, "
            f"body_ptr={body_ptr!r}) is outside the valid "
            f"range [0, 0x80000000); cannot tag for the "
            f"conservative-scan disjointness invariant.  "
            f"Host-store handle counters must be unsigned "
            f"31-bit integers.  Either a counter overflowed, "
            f"a negative sentinel flowed in, or a non-integer "
            f"value flowed into _wrap_handle."
        )


def _wrap_handle(
    caller: wasmtime.Caller, kind: int, raw_handle: int,
) -> int:
    """Wrap an existing host handle into a GC-tracked ADT (#573;
    Decimal-only post-#706).

    Allocates a 12-byte wrapper ADT in WASM memory (tag at
    body[0], handle at body[4]), registers with the wrap
    table, and returns the wrapper pointer.  Used by host
    helpers that have already allocated their store entry
    and need to lift the resulting handle to a wrapper
    pointer before storing in a user-visible structure (e.g.
    ``decimal_from_string`` wrapping its Decimal handle
    inside an ``Option<Decimal>``'s Some payload).
    """
    tag = _KIND_TO_TAG_API.get(kind)
    if tag is None:  # pragma: no cover
        raise ValueError(f"#573: unknown wrap kind {kind}")
    body_ptr = _call_alloc(caller, _WRAPPER_BODY_SIZE)
    _write_i32(caller, body_ptr, tag)
    # #578: validate raw_handle is in the unsigned-31-bit range
    # before tagging.  See ``_validate_wrap_handle`` at module
    # scope (extracted so unit tests can exercise the 5 failure
    # modes without standing up a wasmtime instance).
    _validate_wrap_handle(raw_handle, kind, body_ptr)
    # #578: store the handle ORed with 0x80000000 so the
    # in-heap field can't be mistaken for a heap pointer by
    # the conservative GC scan.  Mirrors the WAT-side
    # ``_emit_wrap_handle`` in
    # ``vera/wasm/calls_containers.py``.  ``$register_wrapper``
    # still gets the RAW handle — the wrap table uses it for
    # ``host_decref_handle`` calls.
    _write_i32(caller, body_ptr + 4, raw_handle | 0x80000000)
    # Decimal wrappers carry no bucket (value-typed), so
    # bucket_ptr stays 0.  (``_wrap_handle`` is Decimal-only
    # post-#706; Map / Set wrappers come from ``_alloc_wrapper``
    # with a real bucket_ptr.)
    _write_i32(caller, body_ptr + 8, 0)
    _call_register_wrapper(caller, body_ptr, kind, raw_handle)
    return body_ptr

# ------------------------------------------------------------------
# #706: bucket-as-truth codec for Map / Set
# ------------------------------------------------------------------
#
# The WASM-resident bucket array is now the SOLE source of truth
# for Map / Set contents (``_map_store`` / ``_set_store`` deleted).
# Host imports take the wrapper pointer, decode the bucket into a
# transient Python dict / set, run the operation, and (for the
# copy-on-write ops) encode a fresh wrapper + bucket.  The wrapper
# IS the map / set value.
#
# Bucket region layout (grown from the 12-byte write-only mirror):
#   header (8 bytes):  capacity (i32 @+0), count (i32 @+4)
#   slot i at HEADER + i*20:
#     +0  occupancy (i32: 1 = live, 0 = empty)
#     +4  key_lo / +8  key_hi   — i64 (``<q``) / f64 (``<d``) /
#                                  (ptr,len) for String / i32 in lo
#     +12 val_lo / +16 val_hi   — same encoding by value tag
#
# The explicit occupancy flag (rather than ``key_word_0 == 0``)
# distinguishes an empty slot from a legitimate ``0`` Int key or an
# empty-string key (``_alloc_string("")`` → ``(0, 0)``), closing the
# collision flagged in the #707 review.
_BKT_HEADER = 8
_BKT_SLOT = 20

def _bkt_region_size(capacity: int) -> int:
    return _BKT_HEADER + capacity * _BKT_SLOT

def _alloc_bucket(caller: wasmtime.Caller, capacity: int) -> int:
    """Allocate a zero-filled bucket region; write capacity, count=0."""
    total = _bkt_region_size(capacity)
    bucket_ptr = _call_alloc(caller, total)
    _write_bytes(caller, bucket_ptr, b"\x00" * total)
    _write_i32(caller, bucket_ptr, capacity)
    return bucket_ptr

def _alloc_wrapper(
    caller: wasmtime.Caller, kind: int, bucket_ptr: int = 0,
) -> int:
    """Allocate a Map / Set wrapper ADT (#706).

    Body: tag @+0, 0 @+4 (vestigial — the host handle is gone),
    bucket_ptr @+8 (the GC-traced pointer to the bucket region).
    No wrap-table registration: Map / Set wrappers and their
    buckets are now plain heap objects reclaimed by ordinary
    mark-sweep, so the Phase 2c destructor path is Decimal-only.
    """
    body_ptr = _call_alloc(caller, _WRAPPER_BODY_SIZE)
    _write_i32(caller, body_ptr, _KIND_TO_TAG_API[kind])
    _write_i32(caller, body_ptr + 4, 0)
    _write_i32(caller, body_ptr + 8, bucket_ptr)
    return body_ptr

def _encode_field(tag: str, value: Any) -> bytes:
    """Encode an inline (non-String) key/val into its 8-byte field."""
    if tag == "i":
        return struct.pack("<q", int(value))  # signed i64
    if tag == "f":
        return struct.pack("<d", float(value))
    # "b": Bool / Byte / ADT / heap pointer — i32 in lo, 0 in hi.
    return struct.pack("<II", int(value) & 0xFFFF_FFFF, 0)

def _decode_field(
    caller: wasmtime.Caller, tag: str, buf: bytes, off: int,
) -> object:
    """Decode an 8-byte field at ``off`` within ``buf`` per tag."""
    if tag == "i":
        return int(struct.unpack_from("<q", buf, off)[0])
    if tag == "f":
        return float(struct.unpack_from("<d", buf, off)[0])
    if tag == "s":
        ptr, ln = struct.unpack_from("<II", buf, off)
        return _read_wasm_string(caller, ptr, ln) if ln else ""
    return int(struct.unpack_from("<I", buf, off)[0])

# ------------------------------------------------------------------
# #706: SameValueZero key/element comparison.
# ------------------------------------------------------------------
# Float64 keys / Set elements compare under SameValueZero (the
# semantics native JS Map/Set use): NaN equals NaN, and +0.0 == -0.0.
# Python's ``==`` and dict / set / list membership all treat NaN as
# unequal to itself, so without this a NaN key can never be found,
# removed, or deduped.  The browser runtime carries the parallel
# ``sameValueZero`` helper.  These collapse to plain ``==`` / dict
# ops for every non-float key, so the Int-keyed hot paths (e.g. the
# 10K insert chain) are unaffected.
def _is_nan(v: object) -> bool:
    return isinstance(v, float) and v != v

def _same_value_zero(a: object, b: object) -> bool:
    return a is b or a == b or (_is_nan(a) and _is_nan(b))

def _map_lookup(d: dict[object, object], k: object) -> object:
    """``d.get(k)`` with SameValueZero (finds a NaN key); O(1) for
    the common non-NaN case."""
    if _is_nan(k):
        return next((vv for kk, vv in d.items() if _is_nan(kk)), None)
    return d.get(k)

def _map_put(d: dict[object, object], k: object, v: object) -> None:
    """``d[k] = v`` with SameValueZero key dedup (NaN keys collapse
    to one entry; a plain dict cannot dedup NaN)."""
    if _is_nan(k):
        for existing in [kk for kk in d if _is_nan(kk)]:
            del d[existing]
    d[k] = v

def _set_add_svz(s: set[object], e: object) -> None:
    """``s.add(e)`` with SameValueZero dedup (at most one NaN)."""
    if _is_nan(e) and any(_is_nan(x) for x in s):
        return
    s.add(e)

def _decode_map(
    caller: wasmtime.Caller, wrapper_ptr: int, kt: str, vt: str,
) -> dict[object, object]:
    """Decode a Map wrapper's bucket into a Python dict."""
    bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
    if bucket_ptr == 0:
        return {}
    cap, count = struct.unpack(
        "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
    )
    if count == 0:
        return {}
    slots = _read_bytes_at(
        caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
    )
    d: dict[object, object] = {}
    for i in range(cap):
        base = i * _BKT_SLOT
        if struct.unpack_from("<I", slots, base)[0] == 0:
            continue
        k = _decode_field(caller, kt, slots, base + 4)
        v = _decode_field(caller, vt, slots, base + 12)
        d[k] = v
        if len(d) == count:
            break
    return d

def _decode_set(
    caller: wasmtime.Caller, wrapper_ptr: int, et: str,
) -> set[object]:
    """Decode a Set wrapper's bucket into a Python set."""
    bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
    if bucket_ptr == 0:
        return set()
    cap, count = struct.unpack(
        "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
    )
    if count == 0:
        return set()
    slots = _read_bytes_at(
        caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
    )
    s: set[object] = set()
    for i in range(cap):
        base = i * _BKT_SLOT
        if struct.unpack_from("<I", slots, base)[0] == 0:
            continue
        s.add(_decode_field(caller, et, slots, base + 4))
        if len(s) == count:
            break
    return s

def _bkt_capacity(count: int) -> int:
    """Slot capacity for ``count`` entries, rounded UP to a power of
    two (min ``_BUCKET_INITIAL_CAPACITY``).

    Power-of-two sizing keeps the heap bounded under copy-on-write:
    consecutive inserts that land in the same size class reuse the
    just-freed bucket from the GC free list instead of bumping the
    heap frontier, so an N-element insert chain's high-water mark
    grows ~O(N) rather than ~O(N^2) (a flat ``count * 2`` produces a
    distinct, never-reused size on every insert).
    """
    want = max(_BUCKET_INITIAL_CAPACITY, count * 2)
    cap = _BUCKET_INITIAL_CAPACITY
    while cap < want:
        cap *= 2
    return cap

def _decode_column(
    caller: wasmtime.Caller, wrapper_ptr: int, tag: str, off: int,
) -> list[object]:
    """Decode one field column (keys at off=4, vals at off=12).

    Returns occupied-slot values in insertion order — used by
    ``map_keys`` / ``map_values`` / ``set_to_array``, which need only
    one side of each slot and don't have both type tags in scope.
    """
    bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
    if bucket_ptr == 0:
        return []
    cap, count = struct.unpack(
        "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
    )
    if count == 0:
        return []
    slots = _read_bytes_at(
        caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
    )
    out: list[object] = []
    for i in range(cap):
        base = i * _BKT_SLOT
        if struct.unpack_from("<I", slots, base)[0] == 0:
            continue
        out.append(_decode_field(caller, tag, slots, base + off))
        if len(out) == count:
            break
    return out

def _bkt_count(caller: wasmtime.Caller, wrapper_ptr: int) -> int:
    """O(1) live-entry count from the bucket header (0 if empty)."""
    bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
    if bucket_ptr == 0:
        return 0
    return _read_i32_at(caller, bucket_ptr + 4)

def _bkt_raw_entries(
    caller: wasmtime.Caller, wrapper_ptr: int,
) -> "list[tuple[bytes, bytes]]":
    """Occupied slots as verbatim (key_field, val_field) byte pairs.

    Used by ``map_remove`` / ``set_remove``, which rebuild the
    collection without interpreting the value type: the 8-byte key
    and val fields are copied as-is, so String / heap-pointer blocks
    are SHARED with the source (immutable, so sharing is safe) and
    no re-encode tag is needed.
    """
    bucket_ptr = _read_i32_at(caller, wrapper_ptr + 8)
    if bucket_ptr == 0:
        return []
    cap, count = struct.unpack(
        "<II", _read_bytes_at(caller, bucket_ptr, _BKT_HEADER),
    )
    if count == 0:
        return []
    slots = _read_bytes_at(
        caller, bucket_ptr + _BKT_HEADER, cap * _BKT_SLOT,
    )
    out: list[tuple[bytes, bytes]] = []
    for i in range(cap):
        base = i * _BKT_SLOT
        if struct.unpack_from("<I", slots, base)[0] == 0:
            continue
        out.append((slots[base + 4:base + 12], slots[base + 12:base + 20]))
        if len(out) == count:
            break
    return out

def _encode_raw(
    caller: wasmtime.Caller,
    kind: int,
    raws: "list[tuple[bytes, bytes]]",
) -> int:
    """Encode verbatim (key_field, val_field) pairs into a wrapper.

    No string re-allocation (fields copied as-is), so always the
    single-batched-write fast path.  Survivor heap blocks stay live
    via the source wrapper across the wrapper / bucket allocs, then
    via the new bucket after the write.
    """
    count = len(raws)
    capacity = _bkt_capacity(count)
    wrapper_ptr = _alloc_wrapper(caller, kind, 0)
    with _ShadowGuard(caller) as guard:
        guard.push(wrapper_ptr)
        bucket_ptr = _alloc_bucket(caller, capacity)
        guard.push(bucket_ptr)
        buf = bytearray(capacity * _BKT_SLOT)
        for i, (kb, vb) in enumerate(raws):
            base = i * _BKT_SLOT
            struct.pack_into("<I", buf, base, 1)
            buf[base + 4:base + 12] = kb
            buf[base + 12:base + 20] = vb
        _write_bytes(caller, bucket_ptr + _BKT_HEADER, bytes(buf))
        _write_i32(caller, bucket_ptr + 4, count)
        _write_i32(caller, wrapper_ptr + 8, bucket_ptr)  # link
    return wrapper_ptr

def _encode_entries(
    caller: wasmtime.Caller,
    kind: int,
    entries: "list[tuple[object, object]]",
    kt: str,
    vt: str | None,
) -> int:
    """Encode (key, val) entries into a fresh wrapper + bucket (#706).

    ``vt`` is None for Sets (val field stays zero).  Returns the new
    wrapper pointer.  GC discipline: the new wrapper and bucket are
    shadow-rooted across the whole encode; incoming heap-pointer
    keys / values stay live via their own source's rooting for the
    duration of this synchronous host call (the #695 / #705
    reachability tests pin this).  FAST path
    (no String key / val) builds the whole bucket as one ``bytes``
    and emits a single ``memory.write``; SLOW path (String present)
    writes each slot in place, val-first, allocating key / val
    strings into the already-rooted bucket.
    """
    needs_string = kt == "s" or vt == "s"
    count = len(entries)
    capacity = _bkt_capacity(count)
    wrapper_ptr = _alloc_wrapper(caller, kind, 0)
    with _ShadowGuard(caller) as guard:
        guard.push(wrapper_ptr)
        bucket_ptr = _alloc_bucket(caller, capacity)
        guard.push(bucket_ptr)
        slots_base = bucket_ptr + _BKT_HEADER
        if not needs_string:
            buf = bytearray(capacity * _BKT_SLOT)
            for i, (k, v) in enumerate(entries):
                base = i * _BKT_SLOT
                struct.pack_into("<I", buf, base, 1)
                buf[base + 4:base + 12] = _encode_field(kt, k)
                if vt is not None:
                    buf[base + 12:base + 20] = _encode_field(vt, v)
            _write_bytes(caller, slots_base, bytes(buf))
        else:
            for i, (k, v) in enumerate(entries):
                slot = slots_base + i * _BKT_SLOT
                _write_i32(caller, slot, 1)
                # Val first: roots a heap-pointer value before the
                # key-string alloc can fire GC.
                if vt == "s":
                    vp, vl = _alloc_string(caller, str(v))
                    _write_i32(caller, slot + 12, vp)
                    _write_i32(caller, slot + 16, vl)
                elif vt is not None:
                    _write_bytes(caller, slot + 12, _encode_field(vt, v))
                if kt == "s":
                    kp, kl = _alloc_string(caller, str(k))
                    _write_i32(caller, slot + 4, kp)
                    _write_i32(caller, slot + 8, kl)
                else:
                    _write_bytes(caller, slot + 4, _encode_field(kt, k))
        _write_i32(caller, bucket_ptr + 4, count)  # header.count
        _write_i32(caller, wrapper_ptr + 8, bucket_ptr)  # link
    return wrapper_ptr

def _encode_map(
    caller: wasmtime.Caller, d: dict[object, object], kt: str, vt: str,
) -> int:
    """Encode a Python dict into a fresh Map wrapper + bucket."""
    return _encode_entries(
        caller, _WRAP_KIND_MAP, list(d.items()), kt, vt,
    )

def _encode_set(
    caller: wasmtime.Caller, s: set[object], et: str,
) -> int:
    """Encode a Python set into a fresh Set wrapper + bucket."""
    return _encode_entries(
        caller, _WRAP_KIND_SET, [(e, 0) for e in s], et, None,
    )

def _alloc_map_wrapper(
    caller: wasmtime.Caller, d: dict[object, object],
) -> int:
    """Build a Map<String, V> wrapper from a host-built dict (#706).

    Used by the JSON / HTML parser paths (``write_json``'s JObject
    branch, HtmlElement attrs), whose keys are always strings.
    Bucket-as-truth: the wrapper's bucket IS the map; no
    ``_map_store`` entry.  Heap-pointer values stay reachable from
    the conservative scan via wrapper → bucket → val word, closing
    the #695 silent-UAF window.  Keys are coerced to ``str`` per
    ``write_json``'s ``map_dict[str(k)] = val`` invariant.
    """
    items: list[tuple[object, object]] = [
        (str(k), v) for k, v in d.items()
    ]
    # Value tag follows the caller: write_json's JObject values are
    # Json heap pointers (int → "b"); write_html's attrs values are
    # strings ("s").  The two callers never mix value types, so a
    # single uniform tag per map is correct.
    vt = "s" if any(isinstance(v, str) for _, v in items) else "b"
    return _encode_entries(caller, _WRAP_KIND_MAP, items, "s", vt)

def _decode_jobject(
    caller: wasmtime.Caller, wrapper_ptr: int,
) -> dict[object, object]:
    """Decode a JObject's Map<String, Json> (values are Json ptrs)."""
    return _decode_map(caller, wrapper_ptr, "s", "b")

def _decode_attrs(
    caller: wasmtime.Caller, wrapper_ptr: int,
) -> dict[object, object]:
    """Decode an HtmlElement's Map<String, String> attributes."""
    return _decode_map(caller, wrapper_ptr, "s", "s")

def _alloc_string(
    caller: wasmtime.Caller, s: str,
) -> tuple[int, int]:
    """Allocate a string in WASM memory; returns (ptr, len)."""
    encoded = s.encode("utf-8")
    length = len(encoded)
    if length == 0:
        return (0, 0)
    ptr = _call_alloc(caller, length)
    _write_bytes(caller, ptr, encoded)
    return (ptr, length)

def _alloc_result_ok_string(
    caller: wasmtime.Caller, s: str,
) -> int:
    """Allocate Result.Ok(String) on the WASM heap; returns ADT ptr."""
    str_ptr, str_len = _alloc_string(caller, s)
    # GC-rooting (folded into #706): ``str_ptr`` lives only in this
    # Python local across the struct ``_call_alloc`` below; the
    # conservative scan can't see it, so a GC there would sweep the
    # string block and we'd store a dangling pointer.  Root it across
    # the alloc; its reachability transfers to the ADT's +4 field.
    with _ShadowGuard(caller) as guard:
        if str_ptr != 0:
            guard.push(str_ptr)
        # Layout: tag(i32)=0 at +0, str_ptr(i32) at +4, str_len(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        _write_i32(caller, adt_ptr + 4, str_ptr)
        _write_i32(caller, adt_ptr + 8, str_len)
    return adt_ptr

def _alloc_result_err_string(
    caller: wasmtime.Caller, s: str,
) -> int:
    """Allocate Result.Err(String) on the WASM heap; returns ADT ptr."""
    str_ptr, str_len = _alloc_string(caller, s)
    # GC-rooting (folded into #706): see _alloc_result_ok_string —
    # root str_ptr across the struct alloc so a GC can't sweep it.
    with _ShadowGuard(caller) as guard:
        if str_ptr != 0:
            guard.push(str_ptr)
        # Layout: tag(i32)=1 at +0, str_ptr(i32) at +4, str_len(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 1)       # tag = Err
        _write_i32(caller, adt_ptr + 4, str_ptr)
        _write_i32(caller, adt_ptr + 8, str_len)
    return adt_ptr

def _alloc_result_ok_unit(caller: wasmtime.Caller) -> int:
    """Allocate Result.Ok(()) on the WASM heap; returns ADT ptr."""
    # Layout: tag(i32)=0 at +0, no payload
    adt_ptr = _call_alloc(caller, 4)
    _write_i32(caller, adt_ptr, 0)       # tag = Ok
    return adt_ptr

def _alloc_option_some_string(
    caller: wasmtime.Caller, s: str,
) -> int:
    """Allocate Option.Some(String) on the WASM heap; returns ADT ptr."""
    str_ptr, str_len = _alloc_string(caller, s)
    # GC-rooting (folded into #706): see _alloc_result_ok_string —
    # root str_ptr across the struct alloc so a GC can't sweep it.
    with _ShadowGuard(caller) as guard:
        if str_ptr != 0:
            guard.push(str_ptr)
        # Layout: tag(i32)=1 at +0, str_ptr(i32) at +4, str_len(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 1)       # tag = Some
        _write_i32(caller, adt_ptr + 4, str_ptr)
        _write_i32(caller, adt_ptr + 8, str_len)
    return adt_ptr

def _alloc_option_none(caller: wasmtime.Caller) -> int:
    """Allocate Option.None on the WASM heap; returns ADT ptr."""
    # Layout: tag(i32)=0 at +0, no payload
    adt_ptr = _call_alloc(caller, 4)
    _write_i32(caller, adt_ptr, 0)       # tag = None
    return adt_ptr

def _alloc_ordering(caller: wasmtime.Caller, tag: int) -> int:
    """Allocate an Ordering value on the WASM heap.

    Tags: 0 = Less, 1 = Equal, 2 = Greater.
    """
    adt_ptr = _call_alloc(caller, 4)
    _write_i32(caller, adt_ptr, tag)
    return adt_ptr

def _alloc_array_of_strings(
    caller: wasmtime.Caller, strings: list[str],
) -> tuple[int, int]:
    """Allocate an Array<String> on the WASM heap.

    Returns (backing_ptr, count) — the WASM pair representation.
    Each element occupies 8 bytes: (i32 ptr, i32 len).
    """
    count = len(strings)
    if count == 0:
        return (0, 0)
    # GC-rooting (folded into #706): root the backing array across the
    # per-element string allocs.  It lives only in this Python local and
    # would otherwise be swept by a GC inside the loop; each element's
    # str_ptr is written into the (now rooted) backing immediately, so
    # no element pointer is ever held unrooted across an alloc.
    with _ShadowGuard(caller) as guard:
        backing_ptr = _call_alloc(caller, count * 8)
        guard.push(backing_ptr)
        for i, s in enumerate(strings):
            str_ptr, str_len = _alloc_string(caller, s)
            _write_i32(caller, backing_ptr + i * 8, str_ptr)
            _write_i32(caller, backing_ptr + i * 8 + 4, str_len)
    return (backing_ptr, count)

def _alloc_result_ok_i32(
    caller: wasmtime.Caller, value: int,
) -> int:
    """Allocate Result.Ok(i32) — wraps a heap pointer in Ok."""
    # GC-rooting (folded into #706): ``value`` is a heap pointer held
    # only in this Python local across the struct alloc below; root it
    # so a GC there can't sweep the payload the caller just built (the
    # Option / Json / HtmlNode / regex match).  Harmless for the one
    # Bool caller — 0 no-ops, 1 is out of heap range.
    with _ShadowGuard(caller) as guard:
        if value != 0:
            guard.push(value)
        # Layout: tag(i32)=0 at +0, value(i32) at +4
        adt_ptr = _call_alloc(caller, 8)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        _write_i32(caller, adt_ptr + 4, value)
    return adt_ptr


# ---------------------------------------------------------------------------
# Shared collection marshalling helpers (#421)
#
# i64/f64 read+write plus the Option/Array allocation wrappers shared by the
# Map / Set / Decimal / JSON / HTML host families.  Relocated from a
# conditional block inside execute(); all are caller-parameterised, so they
# move to module scope unchanged.
# ---------------------------------------------------------------------------

def _write_i64(
    caller: wasmtime.Caller, offset: int, value: int,
) -> None:
    _write_bytes(
        caller, offset,
        struct.pack("<q", value),
    )

def _write_f64(
    caller: wasmtime.Caller, offset: int, value: float,
) -> None:
    _write_bytes(
        caller, offset,
        struct.pack("<d", value),
    )

def _read_i32(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i32 from WASM memory."""
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    buf = memory.data_ptr(caller)
    val: int = struct.unpack_from(
        "<I", bytes(buf[offset:offset + 4]),
    )[0]
    return val

def _read_f64(caller: wasmtime.Caller, offset: int) -> float:
    """Read a little-endian f64 from WASM memory."""
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    buf = memory.data_ptr(caller)
    val: float = struct.unpack_from(
        "<d", bytes(buf[offset:offset + 8]),
    )[0]
    return val

def _alloc_option_some_i64(
    caller: wasmtime.Caller, value: int,
) -> int:
    """Option.Some wrapping an i64 value.

    Layout: tag(i32) at +0, padding at +4, payload(i64) at +8.
    Total 16 bytes (i64 aligned to 8-byte boundary).
    """
    adt_ptr = _call_alloc(caller, 16)
    _write_i32(caller, adt_ptr, 1)  # tag = Some
    _write_i64(caller, adt_ptr + 8, value)
    return adt_ptr

def _alloc_option_some_i32(
    caller: wasmtime.Caller, value: int,
) -> int:
    """Option.Some wrapping an i32 value."""
    # GC-rooting (folded into #706): root a heap-pointer payload
    # (e.g. a Decimal wrapper from decimal_from_string /
    # decimal_div) across the struct alloc.  Harmless for
    # non-pointer i32 values — 0 no-ops, small ints are out of
    # heap range.  Mirrors _alloc_result_ok_i32.
    with _ShadowGuard(caller) as guard:
        if value != 0:
            guard.push(value)
        adt_ptr = _call_alloc(caller, 8)
        _write_i32(caller, adt_ptr, 1)  # tag = Some
        _write_i32(caller, adt_ptr + 4, value)
    return adt_ptr

def _alloc_option_some_f64(
    caller: wasmtime.Caller, value: float,
) -> int:
    """Option.Some wrapping an f64 value.

    Layout: tag(i32) at +0, padding at +4, payload(f64) at +8.
    Total 16 bytes (f64 aligned to 8-byte boundary).
    """
    adt_ptr = _call_alloc(caller, 16)
    _write_i32(caller, adt_ptr, 1)  # tag = Some
    _write_f64(caller, adt_ptr + 8, value)
    return adt_ptr

def _alloc_array_of_i64(
    caller: wasmtime.Caller, values: list[int],
) -> tuple[int, int]:
    """Allocate Array<Int/Nat> — each element is 8 bytes."""
    count = len(values)
    if count == 0:
        return (0, 0)
    ptr = _call_alloc(caller, count * 8)
    for i, v in enumerate(values):
        _write_i64(caller, ptr + i * 8, v)
    return (ptr, count)

def _alloc_array_of_i32(
    caller: wasmtime.Caller, values: list[int],
) -> tuple[int, int]:
    """Allocate Array<Bool/Byte/ADT> — each element is 4 bytes."""
    count = len(values)
    if count == 0:
        return (0, 0)
    ptr = _call_alloc(caller, count * 4)
    for i, v in enumerate(values):
        _write_i32(caller, ptr + i * 4, v)
    return (ptr, count)

def _alloc_array_of_f64(
    caller: wasmtime.Caller, values: list[float],
) -> tuple[int, int]:
    """Allocate Array<Float64> — each element is 8 bytes."""
    count = len(values)
    if count == 0:
        return (0, 0)
    ptr = _call_alloc(caller, count * 8)
    for i, v in enumerate(values):
        _write_f64(caller, ptr + i * 8, v)
    return (ptr, count)
