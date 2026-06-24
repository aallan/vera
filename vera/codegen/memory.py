"""ADT memory-layout utilities for the Vera code generator.

Pure data/math helpers -- constructor memory layout, WASM value-type
sizes and alignment, and the #578 wrap-handle range guard.  No wasmtime
or runtime dependency, so they import cleanly into the compiler
(`vera/codegen/*`, `vera/wasm/*`) and the runtime alike.  Extracted from
`api.py` (#421); re-exported from `vera.codegen.api` for back-compat.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass
class ConstructorLayout:
    """WASM memory layout for a single ADT constructor."""

    tag: int  # discriminant (0, 1, 2, ...)
    field_offsets: tuple[tuple[int, str], ...]  # (byte_offset, wasm_type) per field
    total_size: int  # total bytes, 8-byte aligned
    # #747: per-field "is a concrete @Nat field" flags, for the runtime
    # @Int -> @Nat narrowing guard at construction sites.  Length matches
    # ``field_offsets`` for user constructors (built in the same loop); ``()``
    # for built-in layouts, where consumers bounds-check (`i < len(...)`)
    # rather than assume a flag exists for every field.
    nat_fields: tuple[bool, ...] = ()

    def __post_init__(self) -> None:
        # #759: ``nat_fields`` runs parallel to ``field_offsets``.  User
        # constructors build the two in the same loop (airtight), but a
        # built-in layout (e.g. ``MdHeading``) hand-authors them as separate
        # literals — enforce the length invariant loudly at construction so a
        # drifted literal fails here, not as a silently mis-indexed guard.  An
        # explicit ``raise`` (not ``assert``) so the check survives ``python -O``
        # and is a real runtime guard, matching this file's validation style.
        if self.nat_fields and len(self.nat_fields) != len(self.field_offsets):
            raise ValueError(
                f"nat_fields (len {len(self.nat_fields)}) must match "
                f"field_offsets (len {len(self.field_offsets)}) or be empty"
            )


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


def _wasm_type_size(wt: str) -> int:
    """Byte size of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    if wt == "i32_pair":
        return 8
    raise ValueError(f"Unknown WASM type: {wt}")


def _wasm_type_align(wt: str) -> int:
    """Natural alignment of a WASM value type."""
    if wt == "i32":
        return 4
    if wt in ("i64", "f64"):
        return 8
    if wt == "i32_pair":
        return 4
    raise ValueError(f"Unknown WASM type: {wt}")


def _align_up(offset: int, align: int) -> int:
    """Round offset up to the next multiple of align."""
    return (offset + align - 1) & ~(align - 1)
