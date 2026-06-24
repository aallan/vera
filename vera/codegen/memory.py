"""ADT memory-layout utilities for the Vera code generator.

Pure data/math helpers -- constructor memory layout, and WASM value-type sizes and
alignment.  No wasmtime or runtime dependency, so they import cleanly into the compiler
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
