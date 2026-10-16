"""WASM heap marshalling helpers for the Vera runtime.

Memory read/write, shadow-stack GC rooting, wrapper-ADT handle tagging,
building and reading a map through the module's own exports, and
Result/Option/Array allocation -- all
parameterised by the `wasmtime.Caller` (memory is reached via
`caller["memory"]` / `caller["alloc"]`), so they are plain module-level
functions.  Extracted from `execute()` in `vera/codegen/api.py` (#421).
"""

from __future__ import annotations

import struct
from collections.abc import Callable, Iterable
from typing import TypeVar

import wasmtime

from vera.runtime.text import safe_utf8_decode


def _slice_and_decode(
    memory: wasmtime.Memory,
    context: wasmtime.Store | wasmtime.Caller,
    ptr: int,
    length: int,
) -> str:
    """Slice ``length`` bytes at ``ptr`` from ``memory`` and safe-decode them.

    Shared body of :func:`_read_wasm_string` and :func:`_read_string_export`:
    resolve the ``data_ptr`` for the given wasmtime ``context`` (a live
    ``Caller`` mid-call, or the ``Store`` post-run) and route the slice through
    :func:`safe_utf8_decode`, so a corrupt region surfaces as U+FFFD rather than
    a ``UnicodeDecodeError`` escaping the trampoline (#589 / #592).  The decode
    is the only shared concern; the raw ``ctypes`` slice does **no** bounds
    checking of its own, so each caller MUST validate ``(ptr, length)`` before
    calling (#1145): :func:`_read_string_export` returns ``None`` on an
    out-of-bounds or negative pair (a post-run fallback to the raw pointer),
    while :func:`_read_wasm_string` raises a ``wasmtime.WasmtimeError`` (a live
    trampoline has no ``None`` to return — the guest gets a clean
    ``out_of_bounds`` trap).
    """
    buf = memory.data_ptr(context)
    return safe_utf8_decode(bytes(buf[ptr:ptr + length]))

def _read_wasm_string(
    caller: wasmtime.Caller, ptr: int, length: int,
) -> str:
    """Read a UTF-8 string from WASM memory.

    Bounds-checks ``(ptr, length)`` against the live memory size before the
    slice (#1145).  The read goes through a raw ``ctypes`` pointer
    (:func:`_slice_and_decode`), which does no bounds checking of its own, so an
    out-of-range pair reads past the memory region into wasmtime's guard page
    and kills the host process with ``SIGBUS`` — and because the crash happens
    inside ``bytes(buf[...])``, *before* decoding, the :func:`safe_utf8_decode`
    contract (#589 / #592) does not cover it.  A negative or out-of-bounds pair
    — from an upstream codegen bug or a program that computes a bad
    ``(ptr, len)`` — instead raises a ``wasmtime.WasmtimeError`` carrying the
    ``out of bounds memory access`` reason, which ``execute()`` classifies as a
    clean ``out_of_bounds`` trap (with backtrace + Fix) exactly like a native
    guest OOB, rather than taking the host down.

    A corrupt but *in-bounds* region still decodes via
    :func:`safe_utf8_decode` (``errors="replace"`` → U+FFFD) rather than a raw
    ``UnicodeDecodeError`` escaping the trampoline; downstream path / env-var /
    file-content consumers then surface their own "not found" errors when the
    replacement chars match nothing — a strict improvement over a traceback.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    mem_size = memory.data_len(caller)
    if length < 0 or ptr < 0 or ptr + length > mem_size:
        raise wasmtime.WasmtimeError(
            "out of bounds memory access: host string read of "
            f"{length} byte(s) at offset {ptr} exceeds WASM memory "
            f"size {mem_size}"
        )
    return _slice_and_decode(memory, caller, ptr, length)

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
    return _slice_and_decode(memory, store, ptr, length)

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

def _require_readable(
    memory: wasmtime.Memory,
    caller: wasmtime.Caller,
    offset: int,
    nbytes: int,
    what: str,
) -> None:
    """Refuse an ``(offset, nbytes)`` read that leaves linear memory.

    The ONE bounds check for every raw host reader (#1442), and the same
    one :func:`_read_wasm_string` grew under #1145 — for the same
    reason.  Its callers are :func:`_read_i32_at` and
    :func:`_read_bytes_at` (the ``decode_response_adt`` path),
    :func:`_read_i32` and :func:`_read_f64` (reached from ``read_json``
    on the ``json_stringify`` path), and ``markdown.py``'s own
    ``_read_i32`` / ``_read_i64`` / ``_read_string`` (walking a
    guest-built AST; the last reaches the slice through
    :func:`_slice_and_decode`).  Each
    slices a raw ``ctypes`` pointer, which bounds-checks nothing: an
    offset past the end reads into wasmtime's guard page and takes the
    HOST down with ``SIGBUS``, not the guest with a trap.  A negative
    ``nbytes`` is just as wrong in the other direction — the ctypes
    slice returns an empty ``bytes``, which ``struct.unpack`` then
    rejects or, worse, a caller treats as a legitimately empty field.

    What unites them is not the call site but the OFFSET's provenance:
    every one is handed a value read out of guest memory rather than
    returned by an allocator.  The two ``data_ptr`` sites that are not
    on this list — ``_ShadowGuard.push`` and the String-argument
    marshaller in ``vera/codegen/api.py`` — are writes at
    allocator-supplied offsets, which is why they are not in the family.

    Raising ``wasmtime.WasmtimeError`` with the ``out of bounds memory
    access`` reason puts the failure on the path ``execute()`` already
    classifies as a clean ``out_of_bounds`` trap, with a backtrace and a
    Fix, exactly like a native guest OOB.

    This is CONTAINMENT, not the primary guard.  Every offset reaching
    these helpers should already be a pointer the guest allocated, so a
    violation means something upstream handed the host a value that is
    not the pointer it was taken for — #1442's own case was a ``handle``
    whose declared type was not ``Request``, admitted by a
    ``validate_handler`` that checked the lowered ABI instead of the Vera
    types.  That hole is closed at its source; this keeps the next one in
    the family a diagnostic rather than a dead process.
    """
    mem_size = memory.data_len(caller)
    if nbytes < 0 or offset < 0 or offset + nbytes > mem_size:
        raise wasmtime.WasmtimeError(
            f"out of bounds memory access: host {what} read of "
            f"{nbytes} byte(s) at offset {offset} exceeds WASM memory "
            f"size {mem_size}"
        )

def _read_i32_at(caller: wasmtime.Caller, offset: int) -> int:
    """Read a little-endian i32 from WASM memory at `offset`.

    Module-factory-level counterpart to ``_write_i32`` (line ~944).
    A nested ``_read_i32`` exists later inside the decimal closures;
    this version is shared by all module-level helpers that need
    to inspect linear memory (e.g. ``_map_items`` below).

    Bounds-checked via :func:`_require_readable` before the raw slice
    (#1442) — see there for why the check cannot live in the ctypes read.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, offset, 4, "i32")
    buf = memory.data_ptr(caller)
    return int(struct.unpack_from("<I", bytes(buf[offset:offset + 4]))[0])

def _read_bytes_at(
    caller: wasmtime.Caller, offset: int, length: int,
) -> bytes:
    """Read `length` raw bytes from WASM linear memory at `offset`.

    Bounds-checked via :func:`_require_readable` before the raw slice
    (#1442) — see there for why the check cannot live in the ctypes read.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, offset, length, "byte-range")
    buf = memory.data_ptr(caller)
    return bytes(buf[offset:offset + length])

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
        if sp < 0 or sp + 4 > limit:
            # The host-side twin of the WAT-side bound (the
            # ``unreachable`` in ``gc_shadow_push``, which a host names
            # by the generic kind's shadow-stack cause): raised here as
            # a host-side error, so it reaches the reader as
            # ``host_error`` with this message, not as a wasmtime trap.
            # #791: the bound is slot-complete — the push writes a
            # 4-byte slot at ``[sp..sp+3]``, so ``sp + 4 > limit``
            # (not ``sp >= limit``) rejects a misaligned ``gc_sp``
            # with 1-3 bytes of headroom that would otherwise
            # partially spill past the window, and ``sp < 0``
            # rejects a negative pointer that would index the
            # ctypes buffer BEFORE the linear-memory base.
            # Unreachable via generated WAT (which advances
            # ``$gc_sp`` in 4-byte steps from a 4-aligned base) —
            # defense-in-depth for hand-written fixtures / future
            # host paths.
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
# destructor firing.  A Map or Set is no wrapper (#1676).
_WRAP_KIND_DECIMAL = 3
_DECIMAL_HANDLE_TAG = 0xFEEDC003
_KIND_TO_TAG_API = {
    _WRAP_KIND_DECIMAL: _DECIMAL_HANDLE_TAG,
}
# #573: the 12-byte wrapper:
#   +0  tag (i32)                                 [#573]
#   +4  handle | 0x80000000 (bit-31)              [#578]
#   +8  0, the field Map's and Set's buckets once held [#695/#706]
# Must agree with ``_WRAPPER_BODY_SIZE`` in
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
    # A Decimal wrapper carries no bucket (value-typed), so +8 stays 0.
    _write_i32(caller, body_ptr + 8, 0)
    _call_register_wrapper(caller, body_ptr, kind, raw_handle)
    return body_ptr

# ------------------------------------------------------------------
# #1676: a host builds and reads a `Map<String, V>` through the module
# ------------------------------------------------------------------
#
# A map is the module's own persistent trie (``vera/wasm/hamt.py``), so a
# host never reads or writes its blocks.  It builds one with one call of
# the module's ``map_from_arrays$ks_v<t>`` export, from a keys array and a
# values array it writes, and reads one back with ``map_keys$ks`` and
# ``map_values$v<t>``, which return arrays in the map's order (insertion
# order: a repeated key keeps its first position and takes its last
# value).  ``<t>`` is ``b`` for a ``Json`` value (a heap pointer) and ``s``
# for a ``String``.  The module exports the three whenever it declares a
# JSON or HTML import or holds a ``Request`` or ``Response``
# (``vera.wasm.hamt.HOST_MAPS``).

def _map_export(caller: wasmtime.Caller, name: str) -> wasmtime.Func:
    fn = caller[name]
    if not isinstance(fn, wasmtime.Func):  # pragma: no cover — codegen exports it
        raise RuntimeError(
            f"#1676: the module exports no {name}, the function a host "
            "builds or reads a map through")
    return fn


def _alloc_map(caller: wasmtime.Caller, value_tag: str,
               keys_ptr: int, vals_ptr: int, count: int) -> int:
    """The map of the *count* keys at *keys_ptr* (``(ptr, len)`` cells) and
    values at *vals_ptr*, in order: one call of the module's
    ``map_from_arrays$ks_v<value_tag>``, which roots both arrays."""
    built = _map_export(caller, f"map_from_arrays$ks_v{value_tag}")(
        caller, keys_ptr, count, vals_ptr, count)
    assert isinstance(built, int)  # noqa: S101
    return built


def _alloc_string_map(
    caller: wasmtime.Caller, items: "Iterable[tuple[str, str]]",
) -> int:
    """A ``Map<String, String>`` of *items*, in their order."""
    pairs = list(items)
    count = len(pairs)
    if count == 0:
        return _alloc_map(caller, "s", 0, 0, 0)
    with _ShadowGuard(caller) as guard:
        keys_ptr = _call_alloc(caller, count * 8)
        guard.push(keys_ptr)
        vals_ptr = _call_alloc(caller, count * 8)
        guard.push(vals_ptr)
        for i, (key, value) in enumerate(pairs):
            # Each string lands in its rooted array before the next
            # allocation can collect it.
            kp, kl = _alloc_string(caller, key)
            _write_i32(caller, keys_ptr + 8 * i, kp)
            _write_i32(caller, keys_ptr + 8 * i + 4, kl)
            vp, vl = _alloc_string(caller, value)
            _write_i32(caller, vals_ptr + 8 * i, vp)
            _write_i32(caller, vals_ptr + 8 * i + 4, vl)
        return _alloc_map(caller, "s", keys_ptr, vals_ptr, count)


def _map_items(
    caller: wasmtime.Caller, map_ptr: int, value_tag: str,
) -> "list[tuple[str, object]]":
    """The entries of the ``Map<String, V>`` at *map_ptr*, in its order: a
    ``String`` value (*value_tag* ``s``) as a ``str``, a heap value (``b``)
    as its pointer.  Each export allocates, so the map, and the keys array
    the first returns, stay rooted across both calls; whatever else reaches
    the map is its reader's to root (``_rooted_read``)."""
    with _ShadowGuard(caller) as guard:
        guard.push(map_ptr)
        keys_ptr, count = _map_export(caller, "map_keys$ks")(caller, map_ptr)
        guard.push(keys_ptr)
        keys = [
            _read_wasm_string(
                caller, _read_i32(caller, keys_ptr + 8 * i),
                _read_i32(caller, keys_ptr + 8 * i + 4))
            for i in range(count)
        ]
        vals_ptr, _ = _map_export(caller, f"map_values$v{value_tag}")(caller, map_ptr)
        values: list[object]
        if value_tag == "s":
            values = [
                _read_wasm_string(
                    caller, _read_i32(caller, vals_ptr + 8 * i),
                    _read_i32(caller, vals_ptr + 8 * i + 4))
                for i in range(count)
            ]
        else:
            values = [_read_i32(caller, vals_ptr + 4 * i) for i in range(count)]
    return list(zip(keys, values, strict=True))


_T = TypeVar("_T")


def _rooted_read(
    caller: wasmtime.Caller, ptr: int, read: "Callable[[], _T]",
) -> "_T":
    """``read()``, with the value at *ptr* rooted for the whole of it.

    The JSON and HTML readers reach each map through the module's
    ``map_keys$ks`` and ``map_values$v<t>``, which allocate (#1676), so a
    collection can run inside any one map's read; the value is rooted so
    that it cannot sweep a sibling the walk reaches next, whether or not
    the call site rooted the argument."""
    with _ShadowGuard(caller) as guard:
        guard.push(ptr)
        return read()


def _alloc_jobject_map(
    caller: wasmtime.Caller, keys_ptr: int, vals_ptr: int, count: int,
) -> int:
    """A JObject's ``Map<String, Json>`` of the *count* keys (``(ptr, len)``
    cells) and ``Json`` pointers two arrays hold."""
    return _alloc_map(caller, "b", keys_ptr, vals_ptr, count)


def _alloc_attrs(caller: wasmtime.Caller, attrs: dict[object, object]) -> int:
    """An HtmlElement's ``Map<String, String>`` attributes."""
    return _alloc_string_map(caller, ((str(k), str(v)) for k, v in attrs.items()))


def _decode_jobject(
    caller: wasmtime.Caller, map_ptr: int,
) -> dict[object, object]:
    """A JObject's ``Map<String, Json>``, its values the ``Json`` pointers."""
    return dict(_map_items(caller, map_ptr, "b"))


def _decode_attrs(
    caller: wasmtime.Caller, map_ptr: int,
) -> dict[object, object]:
    """An HtmlElement's ``Map<String, String>`` attributes."""
    return dict(_map_items(caller, map_ptr, "s"))


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

def _alloc_result_ok_bytes(
    caller: wasmtime.Caller, data: bytes,
) -> int:
    """Allocate Result.Ok(Array<Byte>) on the WASM heap; returns ADT ptr.

    An ``Array<Byte>`` is a (ptr, len) pair over one-byte cells, the
    layout generated code reads, so *data* is written as it is, in one
    copy; the empty array is ``(0, 0)``.  The ADT is a ``Result<String,
    String>``'s: tag at +0, ptr at +4, len at +8 (#1711).
    """
    length = len(data)
    arr_ptr = 0
    if length:
        arr_ptr = _call_alloc(caller, length)
        _write_bytes(caller, arr_ptr, data)
    # GC-rooting: ``arr_ptr`` lives only in this Python local across the
    # struct ``_call_alloc``; root it, as _alloc_result_ok_string does.
    with _ShadowGuard(caller) as guard:
        if arr_ptr != 0:
            guard.push(arr_ptr)
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 0)       # tag = Ok
        _write_i32(caller, adt_ptr + 4, arr_ptr)
        _write_i32(caller, adt_ptr + 8, length)
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
    """Read a little-endian i32 from WASM memory.

    Bounds-checked through :func:`_require_readable` (#1442).  Reached
    from ``read_json`` on the ``json_stringify`` path
    (``vera/runtime/json.py``), which walks a guest-built JSON tree by
    following pointers read out of that tree — so every offset here
    derives from guest memory contents rather than from an allocator,
    which is exactly the shape that must not be trusted to a raw slice.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, offset, 4, "i32")
    buf = memory.data_ptr(caller)
    val: int = struct.unpack_from(
        "<I", bytes(buf[offset:offset + 4]),
    )[0]
    return val

def _read_f64(caller: wasmtime.Caller, offset: int) -> float:
    """Read a little-endian f64 from WASM memory.

    Bounds-checked through :func:`_require_readable` (#1442); the
    ``read_json`` sibling of :func:`_read_i32` above, and reached the
    same way.
    """
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    _require_readable(memory, caller, offset, 8, "f64")
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

def _read_wasm_array_of_options_of_string(
    caller: wasmtime.Caller, ptr: int, count: int,
) -> list[str | None]:
    """Read an ``Array<Option<String>>`` (a ``DB`` params argument) from WASM
    memory into a Python list of ``str`` (Some) / ``None`` (None).

    The backing at ``ptr`` holds ``count`` 4-byte i32 pointers, each to an
    ``Option<String>`` ADT.  ``count == 0`` is the empty array (``ptr`` is the
    null pair pointer and is never dereferenced).  No allocation happens here,
    so no GC rooting is needed.

    Every guest-controlled offset is bounds-checked before it reaches
    :func:`_read_i32`, whose raw ``ctypes`` slice does no bounds checking of its
    own — an out-of-range read runs past the memory region into wasmtime's guard
    page and kills the host with ``SIGBUS`` (#1145 class).  Three offsets are
    guest-controlled and each is validated: the outer ``(ptr, count)``
    pointer-array range, every per-element ``opt_ptr`` before its tag is read,
    and the full 12-byte ``Some(String)`` cell before its ``str_ptr`` /
    ``str_len`` fields are read.  Any out-of-range offset — or a negative
    ``count`` — raises a clean ``out_of_bounds`` trap, matching a native guest
    OOB; the ``Some`` payload's bytes are then read through the already-guarded
    :func:`_read_wasm_string`.
    """
    if count < 0:
        raise wasmtime.WasmtimeError(
            "out of bounds memory access: DB parameter array has "
            f"negative count {count}"
        )
    if count == 0:
        return []
    memory = caller["memory"]
    assert isinstance(memory, wasmtime.Memory)  # noqa: S101
    mem_size = memory.data_len(caller)

    def _require_in_bounds(offset: int, nbytes: int, what: str) -> None:
        if offset < 0 or offset + nbytes > mem_size:
            raise wasmtime.WasmtimeError(
                f"out of bounds memory access: DB parameter {what} at offset "
                f"{offset} ({nbytes} byte(s)) exceeds WASM memory size "
                f"{mem_size}"
            )

    _require_in_bounds(ptr, count * 4, f"array of {count} pointer(s)")
    out: list[str | None] = []
    for i in range(count):
        opt_ptr = _read_i32(caller, ptr + i * 4)
        _require_in_bounds(opt_ptr, 4, "Option tag")
        if _read_i32(caller, opt_ptr) == 1:       # Some(String) — tag 1
            _require_in_bounds(opt_ptr, 12, "Some(String) cell")
            s_ptr = _read_i32(caller, opt_ptr + 4)
            s_len = _read_i32(caller, opt_ptr + 8)
            out.append(_read_wasm_string(caller, s_ptr, s_len))
        else:                                      # None — tag 0
            out.append(None)
    return out

def _alloc_array_of_options_of_string(
    caller: wasmtime.Caller, cells: list[str | None],
) -> tuple[int, int]:
    """Allocate an ``Array<Option<String>>`` on the WASM heap.

    Returns ``(backing_ptr, count)`` — each element is a 4-byte i32 pointer to
    an ``Option<String>`` ADT (``Some(s)`` for a ``str`` cell, ``None`` for a
    Python ``None``).
    """
    count = len(cells)
    if count == 0:
        return (0, 0)
    # GC-rooting (#229 / #692 class): root the backing across the per-cell
    # Option (and its inner string) allocs.  Each cell's Option ptr is written
    # into the now-rooted backing immediately, so no element pointer is ever
    # held unrooted across an alloc.
    with _ShadowGuard(caller) as guard:
        backing_ptr = _call_alloc(caller, count * 4)
        guard.push(backing_ptr)
        for i, cell in enumerate(cells):
            opt_ptr = (
                _alloc_option_none(caller) if cell is None
                else _alloc_option_some_string(caller, cell)
            )
            _write_i32(caller, backing_ptr + i * 4, opt_ptr)
    return (backing_ptr, count)

def _alloc_result_ok_rows(
    caller: wasmtime.Caller, rows: list[list[str | None]],
) -> int:
    """Allocate ``Result.Ok(Array<Array<Option<String>>>)`` — the ``DB.query``
    result grid — and return the ADT pointer.

    The outer backing holds ``len(rows)`` 8-byte (row_ptr, n_cols) pairs; each
    row is an ``Array<Option<String>>``.  The ``Result.Ok`` wrapper is the
    12-byte pair-payload shape (tag 0 at +0, ptr at +4, count at +8) — the same
    as ``_alloc_result_ok_string``, with an array payload.
    """
    # One guard spans the whole build: the outer backing is rooted before any
    # row is allocated and stays rooted through the final Result.Ok alloc, so
    # every row (and, transitively, its cells and strings) stays reachable from
    # the shadow stack the entire time.  Each row's (ptr, count) is written into
    # the rooted outer backing immediately after the row is built, so no row
    # pointer is held unrooted across an alloc.
    with _ShadowGuard(caller) as guard:
        n_rows = len(rows)
        outer_ptr = 0
        if n_rows != 0:
            outer_ptr = _call_alloc(caller, n_rows * 8)
            guard.push(outer_ptr)
            for i, row in enumerate(rows):
                row_ptr, n_cols = _alloc_array_of_options_of_string(caller, row)
                _write_i32(caller, outer_ptr + i * 8, row_ptr)
                _write_i32(caller, outer_ptr + i * 8 + 4, n_cols)
        # Layout: tag(i32)=0 at +0, backing_ptr(i32) at +4, count(i32) at +8
        adt_ptr = _call_alloc(caller, 12)
        _write_i32(caller, adt_ptr, 0)            # tag = Ok
        _write_i32(caller, adt_ptr + 4, outer_ptr)
        _write_i32(caller, adt_ptr + 8, n_rows)
    return adt_ptr

def _alloc_result_ok_i64(
    caller: wasmtime.Caller, value: int,
) -> int:
    """Allocate ``Result.Ok(Int)`` — the ``DB.execute`` affected-row count.

    Layout: tag(i32)=0 at +0, payload(i64) at +8 (8-byte aligned), 16 bytes
    total — mirroring ``_alloc_option_some_i64``.  No shadow-rooting: the
    payload is an i64 value, not a heap pointer.
    """
    adt_ptr = _call_alloc(caller, 16)
    _write_i32(caller, adt_ptr, 0)                # tag = Ok
    _write_i64(caller, adt_ptr + 8, value)
    return adt_ptr


# =====================================================================
# #305 — HttpServer handler marshalling (Request build / Response read)
# =====================================================================

class InstanceCaller:
    """Adapt a (Store, Instance) pair to the ``caller`` protocol.

    The heap helpers above take a ``wasmtime.Caller`` and use exactly
    two of its capabilities: export lookup (``caller["memory"]``) and
    being passed back to wasmtime calls as the store context
    (``memory.write(caller, ...)``, ``alloc_fn(caller, size)``).  The
    #305 serve driver runs OUTSIDE any host import — there is no
    Caller — so this adapter provides the same protocol from a plain
    instantiated module: ``__getitem__`` resolves exports and
    ``__getattr__`` delegates everything else to the wrapped Store
    (wasmtime accepts the delegating object wherever it needs a store
    context).
    """

    def __init__(
        self, store: wasmtime.Store, instance: wasmtime.Instance,
    ) -> None:
        self._store = store
        self._instance_exports = instance.exports(store)

    def __getitem__(self, name: str) -> object:
        return self._instance_exports[name]

    def __getattr__(self, attr: str) -> object:
        return getattr(self._store, attr)


def build_request_adt(
    caller: wasmtime.Caller,
    layout: object,
    method: str,
    path: str,
    headers: dict[str, str],
    body: str,
) -> int:
    """Build a prelude ``Request(method, path, headers, body)`` ADT.

    ``layout`` is the compiled module's ``ConstructorLayout`` for the
    ``Request`` constructor (field order: method ``i32_pair``, path
    ``i32_pair``, headers ``Map<String, String>`` wrapper ``i32``,
    body ``i32_pair``).  Offsets come from the layout — never
    hardcoded — so a future layout-algorithm change cannot desync the
    driver from the guest.

    Every intermediate allocation is shadow-rooted (#570/#692 class):
    the string allocations, the Map wrapper, and the ADT body itself
    each get a ``guard.push`` so a GC triggered by a later allocation
    in the sequence cannot sweep an earlier one.  The guard's exit
    restores ``gc_sp``; the returned pointer is then rooted by the
    handler function's own GC prologue when passed as its parameter
    (no allocation happens in between).
    """
    field_offsets = layout.field_offsets  # type: ignore[attr-defined]
    total_size = layout.total_size  # type: ignore[attr-defined]
    tag = layout.tag  # type: ignore[attr-defined]
    (m_off, m_ty), (p_off, p_ty), (h_off, h_ty), (b_off, b_ty) = (
        field_offsets
    )
    if (m_ty, p_ty, h_ty, b_ty) != ("i32_pair", "i32_pair", "i32", "i32_pair"):
        raise ValueError(
            f"#305: unexpected Request layout {field_offsets!r}; the "
            "prelude Request shape and this builder must move together"
        )
    with _ShadowGuard(caller) as guard:
        m_ptr, m_len = _alloc_string(caller, method)
        if m_ptr:
            guard.push(m_ptr)
        p_ptr, p_len = _alloc_string(caller, path)
        if p_ptr:
            guard.push(p_ptr)
        h_ptr = _alloc_string_map(caller, headers.items())
        guard.push(h_ptr)
        b_ptr, b_len = _alloc_string(caller, body)
        if b_ptr:
            guard.push(b_ptr)
        adt_ptr = _call_alloc(caller, total_size)
        guard.push(adt_ptr)
        _write_i32(caller, adt_ptr + 0, tag)
        _write_i32(caller, adt_ptr + m_off, m_ptr)
        _write_i32(caller, adt_ptr + m_off + 4, m_len)
        _write_i32(caller, adt_ptr + p_off, p_ptr)
        _write_i32(caller, adt_ptr + p_off + 4, p_len)
        _write_i32(caller, adt_ptr + h_off, h_ptr)
        _write_i32(caller, adt_ptr + b_off, b_ptr)
        _write_i32(caller, adt_ptr + b_off + 4, b_len)
    return adt_ptr


def decode_response_adt(
    caller: wasmtime.Caller, layout: object, response_ptr: int,
) -> dict[str, object]:
    """Decode a prelude ``Response(status, headers, body)`` ADT.

    The headers are read through the module's map functions, which
    allocate, so the response is rooted while they run.  Returns
    ``{"status": int, "headers": dict[str, str], "body": str}``.
    """
    field_offsets = layout.field_offsets  # type: ignore[attr-defined]
    (s_off, s_ty), (h_off, h_ty), (b_off, b_ty) = field_offsets
    if (s_ty, h_ty, b_ty) != ("i64", "i32", "i32_pair"):
        raise ValueError(
            f"#305: unexpected Response layout {field_offsets!r}; the "
            "prelude Response shape and this decoder must move together"
        )
    status_bytes = _read_bytes_at(caller, response_ptr + s_off, 8)
    status = struct.unpack("<q", status_bytes)[0]
    headers_ptr = _read_i32_at(caller, response_ptr + h_off)
    headers: dict[str, str] = {}
    if headers_ptr:
        # The module's map functions allocate the arrays they return, so
        # the response is rooted while they run (#1676).
        with _ShadowGuard(caller) as guard:
            guard.push(response_ptr)
            headers = {
                str(k): str(v)
                for k, v in _decode_attrs(caller, headers_ptr).items()
            }
    body_ptr = _read_i32_at(caller, response_ptr + b_off)
    body_len = _read_i32_at(caller, response_ptr + b_off + 4)
    body = _read_wasm_string(caller, body_ptr, body_len)
    return {"status": status, "headers": headers, "body": body}
