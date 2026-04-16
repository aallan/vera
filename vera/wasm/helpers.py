"""Shared helpers and data classes for the WASM translation layer.

Contains WasmSlotEnv, StringPool, and module-level helper functions
used by multiple wasm submodules.  Kept separate to avoid circular
imports between context.py and the mixin modules.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from vera.types import (
    BOOL,
    FLOAT64,
    FunctionType,
    INT,
    NAT,
    STRING,
    UNIT,
    PrimitiveType,
    Type,
    base_type,
)


# =====================================================================
# Slot environment — De Bruijn → WASM local mapping
# =====================================================================

@dataclass
class WasmSlotEnv:
    """Maps Vera typed De Bruijn indices to WASM local indices.

    Mirrors SlotEnv in smt.py.  Maintains a stack per type name.
    Index 0 = most recent binding (last element in the list),
    matching De Bruijn convention.
    """

    _stacks: dict[str, list[int]] = field(default_factory=dict)

    def resolve(self, type_name: str, index: int) -> int | None:
        """Look up @Type.index → WASM local index."""
        stack = self._stacks.get(type_name, [])
        pos = len(stack) - 1 - index
        if 0 <= pos < len(stack):
            return stack[pos]
        return None

    def push(self, type_name: str, local_idx: int) -> WasmSlotEnv:
        """Return a new environment with *local_idx* pushed for *type_name*."""
        new_stacks = {k: list(v) for k, v in self._stacks.items()}
        new_stacks.setdefault(type_name, []).append(local_idx)
        return WasmSlotEnv(new_stacks)


# =====================================================================
# String pool — deduplicated string constants
# =====================================================================

@dataclass
class StringPool:
    """Manages string literal constants in the WASM data section.

    Deduplicates identical strings and tracks their offsets in
    linear memory.
    """

    _strings: dict[str, tuple[int, int]] = field(default_factory=dict)
    _offset: int = 0

    def intern(self, value: str) -> tuple[int, int]:
        """Return (offset, length) for a string, deduplicating."""
        if value in self._strings:
            return self._strings[value]
        encoded = value.encode("utf-8")
        entry = (self._offset, len(encoded))
        self._strings[value] = entry
        self._offset += len(encoded)
        return entry

    def entries(self) -> list[tuple[str, int, int]]:
        """Return all (value, offset, length) sorted by offset."""
        return [
            (value, offset, length)
            for value, (offset, length) in sorted(
                self._strings.items(), key=lambda x: x[1][0]
            )
        ]

    def has_strings(self) -> bool:
        """Whether any strings have been interned."""
        return len(self._strings) > 0

    @property
    def heap_offset(self) -> int:
        """First byte after all string data — heap starts here."""
        return self._offset


# =====================================================================
# Alignment helper
# =====================================================================

def _align_up(offset: int, align: int) -> int:
    """Round *offset* up to the next multiple of *align*."""
    return (offset + align - 1) & ~(align - 1)


# =====================================================================
# GC shadow stack helper
# =====================================================================

def gc_shadow_push(local_idx: int) -> list[str]:
    """Generate WAT instructions to push an i32 value onto the GC shadow stack.

    Stores the value from ``local_idx`` at the current shadow-stack
    pointer (``$gc_sp``) and advances ``$gc_sp`` by 4 bytes.  Traps
    if the push would overflow the shadow stack into the GC worklist
    region.
    """
    return [
        "global.get $gc_sp",
        "global.get $gc_stack_limit",
        "i32.ge_u",
        "if",
        "  unreachable",  # shadow stack overflow
        "end",
        "global.get $gc_sp",
        f"local.get {local_idx}",
        "i32.store",
        "global.get $gc_sp",
        "i32.const 4",
        "i32.add",
        "global.set $gc_sp",
    ]


# =====================================================================
# Type mapping helpers
# =====================================================================

def wasm_type(t: Type) -> str | None:
    """Map a Vera Type to a WAT value type string.

    Returns "i64" for Int/Nat, "f64" for Float64, "i32" for Bool/Byte/ADT,
    "i32_pair" for String, None for Unit, or "unsupported" for others.
    """
    if isinstance(t, PrimitiveType):
        if t is INT or t is NAT:
            return "i64"
        if t is FLOAT64:
            return "f64"
        if t is BOOL:
            return "i32"
        if t is STRING:
            return "i32_pair"
        if t is UNIT:
            return None
    # Byte type
    bt = base_type(t)
    if isinstance(bt, PrimitiveType):
        if bt is INT or bt is NAT:
            return "i64"
        if bt is FLOAT64:
            return "f64"
        if bt is BOOL:
            return "i32"
        if bt is STRING:
            return "i32_pair"
        if bt is UNIT:
            return None
    if isinstance(t, FunctionType):
        return "i32"  # closure pointer
    return "unsupported"


def wasm_type_or_none(t: Type) -> str | None:
    """Like wasm_type but returns None for both Unit and unsupported."""
    result = wasm_type(t)
    if result == "unsupported":
        return None
    return result


def is_compilable_type(t: Type) -> bool:
    """Check if a Vera type can be compiled to WASM."""
    wt = wasm_type(t)
    return wt is not None and wt != "unsupported"


# =====================================================================
# Array element helpers
# =====================================================================

def _is_pair_element_type(elem_type: str) -> bool:
    """Check if an array element type is a pair type (ptr, len).

    String and Array<T> elements are represented as two consecutive
    i32 values (pointer + length), requiring 8 bytes of storage.
    Bare "Array" (without type args) also matches, since the element
    type name from _infer_vera_type may not include type parameters.
    """
    return elem_type == "String" or elem_type == "Array" or elem_type.startswith("Array<")


def _element_mem_size(elem_type: str) -> int | None:
    """Get memory size in bytes for an array element type.

    Primitive types have fixed sizes.  Pair types (String, Array<T>)
    use 8 bytes (ptr + len).  All other compound types (ADTs) use
    4 bytes (i32 heap pointer).
    """
    sizes = {
        "Int": 8,
        "Nat": 8,
        "Float64": 8,
        "Bool": 1,
        "Byte": 1,
    }
    size = sizes.get(elem_type)
    if size is not None:
        return size
    # Pair types: (ptr, len) = 8 bytes
    if _is_pair_element_type(elem_type):
        return 8
    # ADT / other compound types: i32 heap pointer = 4 bytes
    return 4


def _element_load_op(elem_type: str) -> str | None:
    """Get the WASM load instruction for an array element type.

    Returns None for pair types (String, Array<T>) which require
    special two-load handling in the caller.
    """
    ops = {
        "Int": "i64.load",
        "Nat": "i64.load",
        "Float64": "f64.load",
        "Bool": "i32.load8_u",
        "Byte": "i32.load8_u",
    }
    op = ops.get(elem_type)
    if op is not None:
        return op
    # Pair types need two loads — caller must handle specially
    if _is_pair_element_type(elem_type):
        return None
    # ADT / other compound types: single i32 load
    return "i32.load"


def _element_store_op(elem_type: str) -> str | None:
    """Get the WASM store instruction for an array element type.

    Returns None for pair types (String, Array<T>) which require
    special two-store handling in the caller.
    """
    ops = {
        "Int": "i64.store",
        "Nat": "i64.store",
        "Float64": "f64.store",
        "Bool": "i32.store8",
        "Byte": "i32.store8",
    }
    op = ops.get(elem_type)
    if op is not None:
        return op
    # Pair types need two stores — caller must handle specially
    if _is_pair_element_type(elem_type):
        return None
    # ADT / other compound types: single i32 store
    return "i32.store"


def _element_wasm_type(elem_type: str) -> str | None:
    """Get the WASM value type for an array element type.

    Returns "i32_pair" for pair types (String, Array<T>),
    "i32" for ADT/compound types, or the native type for primitives.
    """
    types = {
        "Int": "i64",
        "Nat": "i64",
        "Float64": "f64",
        "Bool": "i32",
        "Byte": "i32",
    }
    wt = types.get(elem_type)
    if wt is not None:
        return wt
    # Pair types: (ptr, len) represented as i32_pair
    if _is_pair_element_type(elem_type):
        return "i32_pair"
    # ADT / other compound types: i32 heap pointer
    return "i32"
