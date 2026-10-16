"""`Map<K, V>` and `Set<T>` as persistent hash tries in generated code (#1676).

A map or a set is a block of the module's own heap and its fourteen
operations are functions of the module, generated here on demand, one per
operation and representation: no host implements one.  An update copies the
path it changes and shares every other block with the collection it was
given, which it leaves as it was, so an insert costs the depth of the trie.

**The blocks.**  Every block is a plain heap object; the conservative
collector reaches all of them through their words.

- The header, the value a `Map` or `Set` slot holds (16 bytes): ``+0`` the
  number of entries (i32), ``+4`` the root branch or 0 (i32), ``+8`` the next
  insertion number, stored as ``2n + 1`` (i64).
- A branch (``8 + 4c`` bytes): ``+0`` the data map and ``+4`` the node map
  (i32 bitmaps, one bit per 5-bit hash digit; no bit is in both), then its
  ``c`` children: the entries of the data map's digits in digit order, then
  the branches of the node map's.  A child's index is the population count
  of its bitmap below its digit (``i32.popcnt``).
- A collision node, below the last branch (``4 + 4c`` bytes): ``+0`` the
  count, then the entries of two or more keys with one 64-bit hash.
- An entry (32 bytes, never changed once written): ``+0`` the key's hash
  (i64), ``+8`` its insertion number (``2n + 1``: odd, so no scan reads it
  as an object), ``+16`` the key and ``+24`` the value, each one 8-byte word.

Hash digits are read from the low end, five bits a level: the branches at
shifts 0 to 60 consume all 64 bits, and two keys whose hashes are equal
meet in a collision node at shift 65.  An update copies at most thirteen
branches and a collision node.  A branch below the root never holds a single
entry and nothing else: a remove that leaves one moves the entry up.

**Representations.**  A key, value or element is one of five tags, as its
instance's name spells it (``map_insert$ks_vi``): ``i`` an `Int` or `Nat`
(i64), ``f`` a `Float64` (f64), ``s`` a `String` (``ptr``, ``len``), ``y`` a
`Bool` or `Byte` (i32, one byte in an array), and ``b`` any other value, a
heap pointer (i32).  Its word is the value widened to 64 bits; a `String`'s
is ``ptr | len << 32``, the pair as it lies in an array cell.

**Keys.**  The hash is the 64-bit finalizer of MurmurHash3 over the `Hash`
intrinsic's value for the key: an `Int`'s own value, a `Float64`'s bit
pattern, a `String`'s FNV-1a, a `Bool`'s or `Byte`'s value.  A heap key's is
its address, as a heap key's equality is (#1732).  Keys compare by
SameValueZero: a `Float64` key is stored canonical (``-0.0`` as ``0.0``, every
NaN as one NaN), so equal keys have equal words, and a `String` compares by
content (``$eq_String``).

**Order.**  An enumeration (``map_keys``, ``map_values``, ``set_to_array``)
reads the entries in insertion order: an entry keeps its insertion number
when its key is inserted again, and a removed key's goes with it.  The trie
is walked and the entries sorted by their numbers.

**Rooting.**  Every block a helper allocates is pushed on the shadow stack
by the helper that allocates it, and an operation's top-level helper saves
``$gc_sp`` on entry, roots its pointer parameters, and restores it before it
returns, so its result is unrooted when it lands, as a host import's was:
the call site roots it (``WasmContext._root_landed_value``).
"""

from __future__ import annotations

from collections.abc import Callable, Iterator

from vera.wasm.helpers import gc_shadow_push

#: The representation tags, as an instance's name spells them.
TAGS: tuple[str, ...] = ("i", "f", "s", "y", "b")

#: The WAT parameters one value of each tag takes.
PARAMS: dict[str, tuple[str, ...]] = {
    "i": ("i64",), "f": ("f64",), "s": ("i32", "i32"), "y": ("i32",), "b": ("i32",),
}

#: The bytes one value of each tag takes in an array.
CELL: dict[str, int] = {"i": 8, "f": 8, "s": 8, "y": 1, "b": 4}

HEADER_SIZE = 16
ENTRY_SIZE = 32
#: A node below a branch at this shift is a collision node.
LAST_SHIFT = 60

#: Option's constructors, by the tags the prelude gives them (`None`, `Some`).
_NONE_TAG = 0
_SOME_TAG = 1

#: MurmurHash3's 64-bit finalizer constants, and FNV-1a's (the `Hash`
#: intrinsic's string hash, `WasmContext._translate_hash_string`).
_FMIX_1 = 0xFF51AFD7ED558CCD
_FMIX_2 = 0xC4CEB9FE1A85EC53
_FNV_BASIS = 0xCBF29CE484222325
_FNV_PRIME = 0x100000001B3


def _i64(value: int) -> str:
    """An ``i64.const`` of *value* read as a signed 64-bit integer."""
    signed = value - (1 << 64) if value >= 1 << 63 else value
    return f"i64.const {signed}"


# =====================================================================
# Names
# =====================================================================

#: The operations, by the slots their names carry (``"kv"``: ``$k<t>_v<t>``).
OPERATIONS: dict[str, str] = {
    "map_new": "", "map_size": "", "map_insert": "kv", "map_get": "kv",
    "map_contains": "k", "map_remove": "k", "map_keys": "k", "map_values": "v",
    "map_from_arrays": "kv",
    "set_new": "", "set_size": "", "set_add": "e", "set_contains": "e",
    "set_remove": "e", "set_to_array": "e",
}


def helper_name(op: str, **tags: str | None) -> str:
    """The function an operation lowers to at the representations *tags*
    names: ``helper_name("map_insert", k="s", v="i")`` is
    ``map_insert$ks_vi``.  The tags given must be the operation's slots."""
    slots = OPERATIONS[op]
    present = {slot: tag for slot, tag in tags.items() if tag is not None}
    if set(present) != set(slots) or any(t not in TAGS for t in present.values()):
        raise ValueError(f"{op} is named by {slots!r}, not by {present}")
    if not slots:
        return op
    return op + "$" + "_".join(f"{slot}{present[slot]}" for slot in slots)


def _parse(name: str) -> tuple[str, dict[str, str]]:
    op, _, suffix = name.partition("$")
    tags = {part[0]: part[1:] for part in suffix.split("_")} if suffix else {}
    return op, tags


def tags_of(name: str) -> dict[str, str]:
    """The tags an operation's function name carries, by slot."""
    return _parse(name)[1]


#: The functions a host builds and reads a ``Map<String, V>`` through, by
#: the value's tag, which the module exports: one call builds a map from
#: the keys and values the host wrote in two arrays, and two read one back.
#: ``b`` is a JSON object's (a ``Json`` value), ``s`` an HTML element's
#: attributes and a ``Request``'s or ``Response``'s headers.
HOST_MAPS: dict[str, tuple[str, ...]] = {
    "b": ("map_from_arrays$ks_vb", "map_keys$ks", "map_values$vb"),
    "s": ("map_from_arrays$ks_vs", "map_keys$ks", "map_values$vs"),
}


def _cls(tag: str) -> str:
    """The equality a key of *tag* compares by: its bytes, or its word."""
    return "s" if tag == "s" else "w"


# =====================================================================
# WAT text
# =====================================================================

def _func(name: str, params: list[tuple[str, str]], results: list[str],
          locals_: list[tuple[str, str]], body: list[str]) -> str:
    """One function's text, its body indented by its structure."""
    head = f"  (func ${name}" + "".join(f" (param ${p} {t})" for p, t in params)
    if results:
        head += f" (result {' '.join(results)})"
    lines = [head]
    lines.extend(f"    (local ${n} {t})" for n, t in locals_)
    depth = 2
    for ins in body:
        word = ins.split(None, 1)[0] if ins.strip() else ""
        if word in ("end", "else"):
            depth -= 1
        lines.append("  " * depth + ins)
        if word in ("block", "loop", "if", "else"):
            depth += 1
    lines[-1] += ")"
    return "\n".join(lines)


def _push(local: str) -> list[str]:
    return gc_shadow_push(f"${local}")


def _save() -> list[str]:
    return ["global.get $gc_sp", "local.set $sp"]


def _restore() -> list[str]:
    return ["local.get $sp", "global.set $gc_sp"]


def _digit(word: list[str], shift: str = "$shift") -> list[str]:
    """The 5-bit digit of the hash *word* leaves, at the shift local."""
    return [*word, f"local.get {shift}", "i64.extend_i32_u", "i64.shr_u",
            "i32.wrap_i64", "i32.const 31", "i32.and"]


def _below(bitmap: str, bit: str = "$bit") -> list[str]:
    """How many of *bitmap*'s bits lie below *bit*."""
    return [f"local.get {bitmap}", f"local.get {bit}", "i32.const 1", "i32.sub",
            "i32.and", "i32.popcnt"]


def _children(node: str) -> list[str]:
    return [f"local.get {node}", "i32.load", "i32.popcnt",
            f"local.get {node}", "i32.load offset=4", "i32.popcnt", "i32.add"]


def _child(node: str, index: str) -> list[str]:
    return [f"local.get {node}", f"local.get {index}", "i32.const 2", "i32.shl",
            "i32.add", "i32.load offset=8"]


def _key_equal(cls: str, entry: str = "$e", kw: str = "$kw") -> list[str]:
    """Whether *entry*'s key is the key whose word is *kw*."""
    if cls == "w":
        return [f"local.get {entry}", "i64.load offset=16", f"local.get {kw}", "i64.eq"]
    return [f"local.get {entry}", "i32.load offset=16",
            f"local.get {entry}", "i32.load offset=20",
            f"local.get {kw}", "i32.wrap_i64",
            f"local.get {kw}", "i64.const 32", "i64.shr_u", "i32.wrap_i64",
            "call $eq_String"]


def _hit(cls: str, entry: str = "$e") -> list[str]:
    """Whether *entry* holds the key: its hash, then its key."""
    return [f"local.get {entry}", "i64.load", "local.get $h", "i64.eq",
            "if (result i32)", *_key_equal(cls, entry), "else", "i32.const 0", "end"]


def _alloc(size: list[str], into: str) -> list[str]:
    return [*size, "call $alloc", f"local.set {into}", *_push(into[1:])]


def _copy(dst: list[str], src: list[str], words: list[str]) -> list[str]:
    """``memory.copy`` of *words* 4-byte words."""
    return [*dst, *src, *words, "i32.const 2", "i32.shl", "memory.copy"]


# =====================================================================
# The shared helpers
# =====================================================================

def _hamt_new() -> str:
    return _func("hamt$new", [], ["i32"], [("m", "i32")], [
        f"i32.const {HEADER_SIZE}", "call $alloc", "local.tee $m",
        "i32.const 0", "i32.store",
        "local.get $m", "i32.const 0", "i32.store offset=4",
        "local.get $m", "i64.const 1", "i64.store offset=8",
        "local.get $m",
    ])


def _hamt_mix() -> str:
    """MurmurHash3's finalizer: every bit of the result depends on every
    bit of the argument, so the low digits of a structured key spread."""
    step = ["local.get $h", "local.get $h", "i64.const 33", "i64.shr_u", "i64.xor"]
    return _func("hamt$mix", [("h", "i64")], ["i64"], [], [
        *step, "local.set $h",
        "local.get $h", _i64(_FMIX_1), "i64.mul", "local.set $h",
        *step, "local.set $h",
        "local.get $h", _i64(_FMIX_2), "i64.mul", "local.set $h",
        *step,
    ])


def _hash_body(cls: str) -> list[str]:
    """The body of ``$hamt_hash$<cls>``: a key's hash, from its word or,
    for a `String`, from its bytes (FNV-1a, as the `Hash` intrinsic)."""
    if cls == "w":
        return ["local.get $w", "call $hamt$mix"]
    return [
        _i64(_FNV_BASIS), "local.set $h",
        "i32.const 0", "local.set $i",
        "block $done", "loop $byte",
        "local.get $i", "local.get $l", "i32.ge_u", "br_if $done",
        "local.get $h", "local.get $p", "local.get $i", "i32.add", "i32.load8_u",
        "i64.extend_i32_u", "i64.xor", _i64(_FNV_PRIME), "i64.mul", "local.set $h",
        "local.get $i", "i32.const 1", "i32.add", "local.set $i",
        "br $byte", "end", "end",
        "local.get $h", "call $hamt$mix",
    ]


def _hamt_hash(cls: str) -> str:
    if cls == "w":
        return _func("hamt_hash$w", [("w", "i64")], ["i64"], [], _hash_body("w"))
    return _func("hamt_hash$s", [("p", "i32"), ("l", "i32")], ["i64"],
                 [("h", "i64"), ("i", "i32")], _hash_body("s"))


def _hamt_canon() -> str:
    """A `Float64` key's canonical value: every NaN as one, -0.0 as 0.0."""
    return _func("hamt$canon", [("x", "f64")], ["f64"], [], [
        "local.get $x", "local.get $x", "f64.ne",
        "if (result f64)", "f64.const nan",
        "else", "local.get $x", "f64.const 0", "f64.add", "end",
    ])


def _hamt_entry() -> str:
    return _func(
        "hamt$entry", [("h", "i64"), ("seq", "i64"), ("kw", "i64"), ("vw", "i64")],
        ["i32"], [("e", "i32")], [
            f"i32.const {ENTRY_SIZE}", "call $alloc", "local.tee $e",
            "local.get $h", "i64.store",
            "local.get $e", "local.get $seq", "i64.store offset=8",
            "local.get $e", "local.get $kw", "i64.store offset=16",
            "local.get $e", "local.get $vw", "i64.store offset=24",
            *_push("e"), "local.get $e",
        ])


def _hamt_merge() -> str:
    """The node holding two entries a branch at *shift* cannot separate."""
    d1 = _digit(["local.get $e1", "i64.load"])
    d2 = _digit(["local.get $e2", "i64.load"])
    return _func(
        "hamt$merge", [("e1", "i32"), ("e2", "i32"), ("shift", "i32")], ["i32"],
        [("d1", "i32"), ("d2", "i32"), ("n", "i32"), ("sub", "i32")], [
            "local.get $shift", f"i32.const {LAST_SHIFT}", "i32.gt_u",
            "if",
            *_alloc(["i32.const 12"], "$n"),
            "local.get $n", "i32.const 2", "i32.store",
            "local.get $n", "local.get $e1", "i32.store offset=4",
            "local.get $n", "local.get $e2", "i32.store offset=8",
            "local.get $n", "return",
            "end",
            *d1, "local.set $d1", *d2, "local.set $d2",
            "local.get $d1", "local.get $d2", "i32.ne",
            "if",
            *_alloc(["i32.const 16"], "$n"),
            "local.get $n", "i32.const 1", "local.get $d1", "i32.shl",
            "i32.const 1", "local.get $d2", "i32.shl", "i32.or", "i32.store",
            "local.get $n", "i32.const 0", "i32.store offset=4",
            "local.get $d1", "local.get $d2", "i32.lt_u",
            "if",
            "local.get $n", "local.get $e1", "i32.store offset=8",
            "local.get $n", "local.get $e2", "i32.store offset=12",
            "else",
            "local.get $n", "local.get $e2", "i32.store offset=8",
            "local.get $n", "local.get $e1", "i32.store offset=12",
            "end",
            "local.get $n", "return",
            "end",
            "local.get $e1", "local.get $e2", "local.get $shift", "i32.const 5",
            "i32.add", "call $hamt$merge", "local.set $sub",
            *_alloc(["i32.const 12"], "$n"),
            "local.get $n", "i32.const 0", "i32.store",
            "local.get $n", "i32.const 1", "local.get $d1", "i32.shl",
            "i32.store offset=4",
            "local.get $n", "local.get $sub", "i32.store offset=8",
            "local.get $n",
        ])


def _hamt_node_set() -> str:
    """A copy of a branch with child *idx* replaced."""
    return _func(
        "hamt$node_set", [("node", "i32"), ("idx", "i32"), ("child", "i32")],
        ["i32"], [("size", "i32"), ("n", "i32")], [
            *_children("$node"), "i32.const 2", "i32.shl", "i32.const 8", "i32.add",
            "local.set $size",
            *_alloc(["local.get $size"], "$n"),
            "local.get $n", "local.get $node", "local.get $size", "memory.copy",
            "local.get $n", "local.get $idx", "i32.const 2", "i32.shl", "i32.add",
            "local.get $child", "i32.store offset=8",
            "local.get $n",
        ])


def _hamt_node_add_entry() -> str:
    """A copy of a branch with entry *e* added at digit *bit*, data index *idx*."""
    return _func(
        "hamt$node_add_entry",
        [("node", "i32"), ("bit", "i32"), ("idx", "i32"), ("e", "i32")], ["i32"],
        [("cnt", "i32"), ("n", "i32")], [
            *_children("$node"), "local.set $cnt",
            *_alloc(["local.get $cnt", "i32.const 1", "i32.add", "i32.const 2",
                     "i32.shl", "i32.const 8", "i32.add"], "$n"),
            "local.get $n", "local.get $node", "i32.load", "local.get $bit", "i32.or",
            "i32.store",
            "local.get $n", "local.get $node", "i32.load offset=4", "i32.store offset=4",
            *_copy(["local.get $n", "i32.const 8", "i32.add"],
                   ["local.get $node", "i32.const 8", "i32.add"], ["local.get $idx"]),
            "local.get $n", "local.get $idx", "i32.const 2", "i32.shl", "i32.add",
            "local.get $e", "i32.store offset=8",
            *_copy(["local.get $n", "local.get $idx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 12", "i32.add"],
                   ["local.get $node", "local.get $idx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $cnt", "local.get $idx", "i32.sub"]),
            "local.get $n",
        ])


def _hamt_node_entry_to_sub() -> str:
    """A copy of a branch whose entry at data index *eidx* (digit *bit*)
    becomes the node *sub*."""
    return _func(
        "hamt$node_entry_to_sub",
        [("node", "i32"), ("bit", "i32"), ("eidx", "i32"), ("sub", "i32")], ["i32"],
        [("cnt", "i32"), ("ne", "i32"), ("p", "i32"), ("n", "i32"), ("nm", "i32")], [
            *_children("$node"), "local.set $cnt",
            "local.get $node", "i32.load", "i32.popcnt", "local.set $ne",
            "local.get $node", "i32.load offset=4", "local.set $nm",
            *_below("$nm"), "local.set $p",
            *_alloc(["local.get $cnt", "i32.const 2", "i32.shl", "i32.const 8",
                     "i32.add"], "$n"),
            "local.get $n", "local.get $node", "i32.load", "local.get $bit", "i32.xor",
            "i32.store",
            "local.get $n", "local.get $nm", "local.get $bit", "i32.or",
            "i32.store offset=4",
            *_copy(["local.get $n", "i32.const 8", "i32.add"],
                   ["local.get $node", "i32.const 8", "i32.add"], ["local.get $eidx"]),
            *_copy(["local.get $n", "local.get $eidx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $node", "local.get $eidx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 12", "i32.add"],
                   ["local.get $ne", "i32.const 1", "i32.sub", "local.get $eidx",
                    "i32.sub", "local.get $p", "i32.add"]),
            "local.get $n", "local.get $ne", "i32.const 1", "i32.sub", "local.get $p",
            "i32.add", "i32.const 2", "i32.shl", "i32.add", "local.get $sub",
            "i32.store offset=8",
            *_copy(["local.get $n", "local.get $ne", "local.get $p", "i32.add",
                    "i32.const 2", "i32.shl", "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $node", "local.get $ne", "local.get $p", "i32.add",
                    "i32.const 2", "i32.shl", "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $cnt", "local.get $ne", "i32.sub", "local.get $p",
                    "i32.sub"]),
            "local.get $n",
        ])


def _hamt_node_remove_entry() -> str:
    """A copy of a branch without its entry at data index *idx* (digit *bit*)."""
    return _func(
        "hamt$node_remove_entry", [("node", "i32"), ("bit", "i32"), ("idx", "i32")],
        ["i32"], [("cnt", "i32"), ("n", "i32")], [
            *_children("$node"), "local.set $cnt",
            *_alloc(["local.get $cnt", "i32.const 1", "i32.sub", "i32.const 2",
                     "i32.shl", "i32.const 8", "i32.add"], "$n"),
            "local.get $n", "local.get $node", "i32.load", "local.get $bit", "i32.xor",
            "i32.store",
            "local.get $n", "local.get $node", "i32.load offset=4", "i32.store offset=4",
            *_copy(["local.get $n", "i32.const 8", "i32.add"],
                   ["local.get $node", "i32.const 8", "i32.add"], ["local.get $idx"]),
            *_copy(["local.get $n", "local.get $idx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $node", "local.get $idx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 12", "i32.add"],
                   ["local.get $cnt", "i32.const 1", "i32.sub", "local.get $idx",
                    "i32.sub"]),
            "local.get $n",
        ])


def _hamt_node_sub_to_entry() -> str:
    """A copy of a branch whose node at child index *nidx* (digit *bit*)
    becomes the entry *e*, at its data index."""
    return _func(
        "hamt$node_sub_to_entry",
        [("node", "i32"), ("bit", "i32"), ("nidx", "i32"), ("e", "i32")], ["i32"],
        [("cnt", "i32"), ("q", "i32"), ("dm", "i32"), ("n", "i32")], [
            *_children("$node"), "local.set $cnt",
            "local.get $node", "i32.load", "local.set $dm",
            *_below("$dm"), "local.set $q",
            *_alloc(["local.get $cnt", "i32.const 2", "i32.shl", "i32.const 8",
                     "i32.add"], "$n"),
            "local.get $n", "local.get $dm", "local.get $bit", "i32.or", "i32.store",
            "local.get $n", "local.get $node", "i32.load offset=4", "local.get $bit",
            "i32.xor", "i32.store offset=4",
            *_copy(["local.get $n", "i32.const 8", "i32.add"],
                   ["local.get $node", "i32.const 8", "i32.add"], ["local.get $q"]),
            "local.get $n", "local.get $q", "i32.const 2", "i32.shl", "i32.add",
            "local.get $e", "i32.store offset=8",
            *_copy(["local.get $n", "local.get $q", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 12", "i32.add"],
                   ["local.get $node", "local.get $q", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $nidx", "local.get $q", "i32.sub"]),
            *_copy(["local.get $n", "local.get $nidx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 12", "i32.add"],
                   ["local.get $node", "local.get $nidx", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 12", "i32.add"],
                   ["local.get $cnt", "i32.const 1", "i32.sub", "local.get $nidx",
                    "i32.sub"]),
            "local.get $n",
        ])


def _hamt_coll_set() -> str:
    """A copy of a collision node with entry *i* replaced."""
    return _func(
        "hamt$coll_set", [("node", "i32"), ("i", "i32"), ("e", "i32")], ["i32"],
        [("size", "i32"), ("n", "i32")], [
            "local.get $node", "i32.load", "i32.const 2", "i32.shl", "i32.const 4",
            "i32.add", "local.set $size",
            *_alloc(["local.get $size"], "$n"),
            "local.get $n", "local.get $node", "local.get $size", "memory.copy",
            "local.get $n", "local.get $i", "i32.const 2", "i32.shl", "i32.add",
            "local.get $e", "i32.store offset=4",
            "local.get $n",
        ])


def _hamt_coll_add() -> str:
    """A copy of a collision node with entry *e* after its others."""
    return _func(
        "hamt$coll_add", [("node", "i32"), ("e", "i32")], ["i32"],
        [("cnt", "i32"), ("n", "i32")], [
            "local.get $node", "i32.load", "local.set $cnt",
            *_alloc(["local.get $cnt", "i32.const 2", "i32.shl", "i32.const 8",
                     "i32.add"], "$n"),
            "local.get $n", "local.get $cnt", "i32.const 1", "i32.add", "i32.store",
            *_copy(["local.get $n", "i32.const 4", "i32.add"],
                   ["local.get $node", "i32.const 4", "i32.add"], ["local.get $cnt"]),
            "local.get $n", "local.get $cnt", "i32.const 2", "i32.shl", "i32.add",
            "local.get $e", "i32.store offset=4",
            "local.get $n",
        ])


def _hamt_coll_remove() -> str:
    """A copy of a collision node without its entry *i*."""
    return _func(
        "hamt$coll_remove", [("node", "i32"), ("i", "i32")], ["i32"],
        [("cnt", "i32"), ("n", "i32")], [
            "local.get $node", "i32.load", "local.set $cnt",
            *_alloc(["local.get $cnt", "i32.const 2", "i32.shl"], "$n"),
            "local.get $n", "local.get $cnt", "i32.const 1", "i32.sub", "i32.store",
            *_copy(["local.get $n", "i32.const 4", "i32.add"],
                   ["local.get $node", "i32.const 4", "i32.add"], ["local.get $i"]),
            *_copy(["local.get $n", "local.get $i", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 4", "i32.add"],
                   ["local.get $node", "local.get $i", "i32.const 2", "i32.shl",
                    "i32.add", "i32.const 8", "i32.add"],
                   ["local.get $cnt", "i32.const 1", "i32.sub", "local.get $i",
                    "i32.sub"]),
            "local.get $n",
        ])


def _hamt_ins(cls: str) -> str:
    """``(node', status)`` for the branch or collision node *node* at *shift*
    with the key added: status 0 when nothing changed (*node* itself), 1
    when a present key took a new value, 2 when the key is new."""
    name = f"hamt_ins${cls}"
    new_entry = ["local.get $h", "local.get $seq", "local.get $kw", "local.get $vw",
                 "call $hamt$entry", "local.set $ne"]
    kept_entry = ["local.get $h", "local.get $e", "i64.load offset=8", "local.get $kw",
                  "local.get $vw", "call $hamt$entry", "local.set $ne"]
    same_value = ["local.get $e", "i64.load offset=24", "local.get $vw", "i64.eq",
                  "if", "local.get $node", "i32.const 0", "return", "end"]
    return _func(
        name,
        [("node", "i32"), ("shift", "i32"), ("h", "i64"), ("kw", "i64"),
         ("vw", "i64"), ("seq", "i64")],
        ["i32", "i32"],
        [("bit", "i32"), ("dm", "i32"), ("nm", "i32"), ("idx", "i32"), ("e", "i32"),
         ("ne", "i32"), ("sub", "i32"), ("st", "i32"), ("n", "i32"), ("i", "i32")], [
            "local.get $shift", f"i32.const {LAST_SHIFT}", "i32.gt_u",
            "if",
            "local.get $node", "i32.load", "local.set $n",
            "i32.const 0", "local.set $i",
            "block $absent", "loop $scan",
            "local.get $i", "local.get $n", "i32.ge_u", "br_if $absent",
            "local.get $node", "local.get $i", "i32.const 2", "i32.shl", "i32.add",
            "i32.load offset=4", "local.set $e",
            *_key_equal(cls),
            "if",
            *same_value, *kept_entry,
            "local.get $node", "local.get $i", "local.get $ne", "call $hamt$coll_set",
            "i32.const 1", "return",
            "end",
            "local.get $i", "i32.const 1", "i32.add", "local.set $i",
            "br $scan", "end", "end",
            *new_entry,
            "local.get $node", "local.get $ne", "call $hamt$coll_add",
            "i32.const 2", "return",
            "end",
            "i32.const 1", *_digit(["local.get $h"]), "i32.shl", "local.set $bit",
            "local.get $node", "i32.load", "local.set $dm",
            "local.get $node", "i32.load offset=4", "local.set $nm",
            "local.get $dm", "local.get $bit", "i32.and",
            "if",
            *_below("$dm"), "local.set $idx",
            *_child("$node", "$idx"), "local.set $e",
            *_hit(cls),
            "if",
            *same_value, *kept_entry,
            "local.get $node", "local.get $idx", "local.get $ne", "call $hamt$node_set",
            "i32.const 1", "return",
            "end",
            *new_entry,
            "local.get $e", "local.get $ne", "local.get $shift", "i32.const 5",
            "i32.add", "call $hamt$merge", "local.set $sub",
            "local.get $node", "local.get $bit", "local.get $idx", "local.get $sub",
            "call $hamt$node_entry_to_sub",
            "i32.const 2", "return",
            "end",
            "local.get $nm", "local.get $bit", "i32.and",
            "if",
            "local.get $dm", "i32.popcnt", *_below("$nm"), "i32.add", "local.set $idx",
            *_child("$node", "$idx"),
            "local.get $shift", "i32.const 5", "i32.add",
            "local.get $h", "local.get $kw", "local.get $vw", "local.get $seq",
            f"call ${name}", "local.set $st", "local.set $sub",
            "local.get $st", "i32.eqz",
            "if", "local.get $node", "i32.const 0", "return", "end",
            "local.get $node", "local.get $idx", "local.get $sub", "call $hamt$node_set",
            "local.get $st", "return",
            "end",
            *new_entry,
            "local.get $node", "local.get $bit", *_below("$dm"), "local.get $ne",
            "call $hamt$node_add_entry",
            "i32.const 2",
        ])


def _hamt_insert(cls: str) -> str:
    """The header of the map *m* with the key added (*m* itself when that
    changes nothing)."""
    return _func(
        f"hamt_insert${cls}",
        [("m", "i32"), ("h", "i64"), ("kw", "i64"), ("vw", "i64")], ["i32"],
        [("sp", "i32"), ("root", "i32"), ("seq", "i64"), ("e", "i32"), ("r", "i32"),
         ("st", "i32"), ("out", "i32"), ("shift", "i32")], [
            *_save(), *_push("m"),
            "local.get $m", "i32.load offset=4", "local.set $root",
            "local.get $m", "i64.load offset=8", "local.set $seq",
            "local.get $root", "i32.eqz",
            "if",
            "local.get $h", "local.get $seq", "local.get $kw", "local.get $vw",
            "call $hamt$entry", "local.set $e",
            *_alloc(["i32.const 12"], "$r"),
            "local.get $r", "i32.const 1", *_digit(["local.get $h"]), "i32.shl",
            "i32.store",
            "local.get $r", "i32.const 0", "i32.store offset=4",
            "local.get $r", "local.get $e", "i32.store offset=8",
            "i32.const 2", "local.set $st",
            "else",
            "local.get $root", "i32.const 0", "local.get $h", "local.get $kw",
            "local.get $vw", "local.get $seq", f"call $hamt_ins${cls}",
            "local.set $st", "local.set $r",
            "local.get $st", "i32.eqz",
            "if", *_restore(), "local.get $m", "return", "end",
            "end",
            *_alloc([f"i32.const {HEADER_SIZE}"], "$out"),
            "local.get $out", "local.get $m", "i32.load", "local.get $st",
            "i32.const 1", "i32.shr_u", "i32.add", "i32.store",
            "local.get $out", "local.get $r", "i32.store offset=4",
            "local.get $out", "local.get $seq", "local.get $st", "i32.const 2", "i32.and",
            "i64.extend_i32_u", "i64.add", "i64.store offset=8",
            *_restore(), "local.get $out",
        ])


def _hamt_find(cls: str) -> str:
    """The entry of the key in the map *m*, or 0."""
    return _func(
        f"hamt_find${cls}", [("m", "i32"), ("h", "i64"), ("kw", "i64")], ["i32"],
        [("node", "i32"), ("shift", "i32"), ("bit", "i32"), ("dm", "i32"),
         ("nm", "i32"), ("idx", "i32"), ("e", "i32"), ("n", "i32"), ("i", "i32")], [
            "local.get $m", "i32.load offset=4", "local.set $node",
            "i32.const 0", "local.set $shift",
            "loop $down",
            "local.get $node", "i32.eqz", "if", "i32.const 0", "return", "end",
            "local.get $shift", f"i32.const {LAST_SHIFT}", "i32.gt_u",
            "if",
            "local.get $node", "i32.load", "local.set $n",
            "i32.const 0", "local.set $i",
            "block $absent", "loop $scan",
            "local.get $i", "local.get $n", "i32.ge_u", "br_if $absent",
            "local.get $node", "local.get $i", "i32.const 2", "i32.shl", "i32.add",
            "i32.load offset=4", "local.set $e",
            *_key_equal(cls), "if", "local.get $e", "return", "end",
            "local.get $i", "i32.const 1", "i32.add", "local.set $i",
            "br $scan", "end", "end",
            "i32.const 0", "return",
            "end",
            "i32.const 1", *_digit(["local.get $h"]), "i32.shl", "local.set $bit",
            "local.get $node", "i32.load", "local.set $dm",
            "local.get $node", "i32.load offset=4", "local.set $nm",
            "local.get $dm", "local.get $bit", "i32.and",
            "if",
            *_below("$dm"), "local.set $idx",
            *_child("$node", "$idx"), "local.set $e",
            *_hit(cls), "if", "local.get $e", "return", "end",
            "i32.const 0", "return",
            "end",
            "local.get $nm", "local.get $bit", "i32.and", "i32.eqz",
            "if", "i32.const 0", "return", "end",
            "local.get $dm", "i32.popcnt", *_below("$nm"), "i32.add", "local.set $idx",
            *_child("$node", "$idx"), "local.set $node",
            "local.get $shift", "i32.const 5", "i32.add", "local.set $shift",
            "br $down",
            "end",
            "i32.const 0",
        ])


def _hamt_rem(cls: str) -> str:
    """``(result, status)`` for *node* at *shift* without the key: status 0
    when the key is absent, 1 when *result* is the node without it, 2 when
    *result* is the one entry left, which the parent takes in its place, and
    3 when the root is left empty."""
    name = f"hamt_rem${cls}"
    return _func(
        name, [("node", "i32"), ("shift", "i32"), ("h", "i64"), ("kw", "i64")],
        ["i32", "i32"],
        [("bit", "i32"), ("dm", "i32"), ("nm", "i32"), ("idx", "i32"), ("e", "i32"),
         ("sub", "i32"), ("st", "i32"), ("n", "i32"), ("i", "i32")], [
            "local.get $shift", f"i32.const {LAST_SHIFT}", "i32.gt_u",
            "if",
            "local.get $node", "i32.load", "local.set $n",
            "i32.const 0", "local.set $i",
            "block $absent", "loop $scan",
            "local.get $i", "local.get $n", "i32.ge_u", "br_if $absent",
            "local.get $node", "local.get $i", "i32.const 2", "i32.shl", "i32.add",
            "i32.load offset=4", "local.set $e",
            *_key_equal(cls),
            "if",
            "local.get $n", "i32.const 2", "i32.eq",
            "if",
            "local.get $node", "i32.const 1", "local.get $i", "i32.sub", "i32.const 2",
            "i32.shl", "i32.add", "i32.load offset=4", "i32.const 2", "return",
            "end",
            "local.get $node", "local.get $i", "call $hamt$coll_remove",
            "i32.const 1", "return",
            "end",
            "local.get $i", "i32.const 1", "i32.add", "local.set $i",
            "br $scan", "end", "end",
            "i32.const 0", "i32.const 0", "return",
            "end",
            "i32.const 1", *_digit(["local.get $h"]), "i32.shl", "local.set $bit",
            "local.get $node", "i32.load", "local.set $dm",
            "local.get $node", "i32.load offset=4", "local.set $nm",
            "local.get $dm", "local.get $bit", "i32.and",
            "if",
            *_below("$dm"), "local.set $idx",
            *_child("$node", "$idx"), "local.set $e",
            *_hit(cls), "i32.eqz",
            "if", "i32.const 0", "i32.const 0", "return", "end",
            *_children("$node"), "i32.const 1", "i32.eq",
            "if", "i32.const 0", "i32.const 3", "return", "end",
            "local.get $shift", "i32.const 0", "i32.ne",
            "local.get $nm", "i32.eqz", "i32.and",
            "local.get $dm", "i32.popcnt", "i32.const 2", "i32.eq", "i32.and",
            "if",
            "local.get $node", "i32.const 1", "local.get $idx", "i32.sub", "i32.const 2",
            "i32.shl", "i32.add", "i32.load offset=8", "i32.const 2", "return",
            "end",
            "local.get $node", "local.get $bit", "local.get $idx",
            "call $hamt$node_remove_entry", "i32.const 1", "return",
            "end",
            "local.get $nm", "local.get $bit", "i32.and", "i32.eqz",
            "if", "i32.const 0", "i32.const 0", "return", "end",
            "local.get $dm", "i32.popcnt", *_below("$nm"), "i32.add", "local.set $idx",
            *_child("$node", "$idx"),
            "local.get $shift", "i32.const 5", "i32.add", "local.get $h", "local.get $kw",
            f"call ${name}", "local.set $st", "local.set $sub",
            "local.get $st", "i32.eqz",
            "if", "i32.const 0", "i32.const 0", "return", "end",
            "local.get $st", "i32.const 1", "i32.eq",
            "if",
            "local.get $node", "local.get $idx", "local.get $sub", "call $hamt$node_set",
            "i32.const 1", "return",
            "end",
            "local.get $shift", "i32.const 0", "i32.ne",
            "local.get $dm", "i32.eqz", "i32.and",
            "local.get $nm", "i32.popcnt", "i32.const 1", "i32.eq", "i32.and",
            "if", "local.get $sub", "i32.const 2", "return", "end",
            "local.get $node", "local.get $bit", "local.get $idx", "local.get $sub",
            "call $hamt$node_sub_to_entry", "i32.const 1",
        ])


def _hamt_remove(cls: str) -> str:
    """The header of the map *m* without the key (*m* itself when absent)."""
    return _func(
        f"hamt_remove${cls}", [("m", "i32"), ("h", "i64"), ("kw", "i64")], ["i32"],
        [("sp", "i32"), ("root", "i32"), ("r", "i32"), ("st", "i32"), ("out", "i32"),
         ("shift", "i32")], [
            *_save(), *_push("m"),
            "local.get $m", "i32.load offset=4", "local.set $root",
            "local.get $root", "i32.eqz",
            "if", *_restore(), "local.get $m", "return", "end",
            "local.get $root", "i32.const 0", "local.get $h", "local.get $kw",
            f"call $hamt_rem${cls}", "local.set $st", "local.set $r",
            "local.get $st", "i32.eqz",
            "if", *_restore(), "local.get $m", "return", "end",
            "local.get $st", "i32.const 2", "i32.eq",
            "if",
            "local.get $r", "local.set $root",
            *_alloc(["i32.const 12"], "$r"),
            "local.get $r", "i32.const 1",
            *_digit(["local.get $root", "i64.load"]), "i32.shl", "i32.store",
            "local.get $r", "i32.const 0", "i32.store offset=4",
            "local.get $r", "local.get $root", "i32.store offset=8",
            "end",
            *_alloc([f"i32.const {HEADER_SIZE}"], "$out"),
            "local.get $out", "local.get $m", "i32.load", "i32.const 1", "i32.sub",
            "i32.store",
            "local.get $out",
            "local.get $st", "i32.const 3", "i32.eq",
            "if (result i32)", "i32.const 0", "else", "local.get $r", "end",
            "i32.store offset=4",
            "local.get $out", "local.get $m", "i64.load offset=8", "i64.store offset=8",
            *_restore(), "local.get $out",
        ])


def _hamt_collect() -> str:
    """Write *node*'s entries at *buf*[*pos*..]; the position after them."""
    return _func(
        "hamt$collect",
        [("node", "i32"), ("shift", "i32"), ("buf", "i32"), ("pos", "i32")], ["i32"],
        [("ne", "i32"), ("nn", "i32"), ("j", "i32")], [
            "local.get $shift", f"i32.const {LAST_SHIFT}", "i32.gt_u",
            "if",
            *_copy(["local.get $buf", "local.get $pos", "i32.const 2", "i32.shl",
                    "i32.add"],
                   ["local.get $node", "i32.const 4", "i32.add"],
                   ["local.get $node", "i32.load"]),
            "local.get $pos", "local.get $node", "i32.load", "i32.add", "return",
            "end",
            "local.get $node", "i32.load", "i32.popcnt", "local.set $ne",
            "local.get $node", "i32.load offset=4", "i32.popcnt", "local.set $nn",
            *_copy(["local.get $buf", "local.get $pos", "i32.const 2", "i32.shl",
                    "i32.add"],
                   ["local.get $node", "i32.const 8", "i32.add"], ["local.get $ne"]),
            "local.get $pos", "local.get $ne", "i32.add", "local.set $pos",
            "i32.const 0", "local.set $j",
            "block $done", "loop $sub",
            "local.get $j", "local.get $nn", "i32.ge_u", "br_if $done",
            "local.get $node", "local.get $ne", "local.get $j", "i32.add",
            "i32.const 2", "i32.shl", "i32.add", "i32.load offset=8",
            "local.get $shift", "i32.const 5", "i32.add",
            "local.get $buf", "local.get $pos", "call $hamt$collect", "local.set $pos",
            "local.get $j", "i32.const 1", "i32.add", "local.set $j",
            "br $sub", "end", "end",
            "local.get $pos",
        ])


def _hamt_sorted() -> str:
    """The entries of the non-empty map *m*, in insertion order: a buffer of
    entry pointers, rooted (the caller restores ``$gc_sp``)."""
    seq = ["i32.const 2", "i32.shl", "i32.add", "i32.load", "i64.load offset=8"]
    return _func(
        "hamt$sorted", [("m", "i32")], ["i32"],
        [("n", "i32"), ("a", "i32"), ("b", "i32"), ("t", "i32"), ("w", "i32"),
         ("i", "i32"), ("mid", "i32"), ("hi", "i32"), ("l", "i32"), ("r", "i32"),
         ("o", "i32")], [
            "local.get $m", "i32.load", "local.set $n",
            *_alloc(["local.get $n", "i32.const 2", "i32.shl"], "$a"),
            *_alloc(["local.get $n", "i32.const 2", "i32.shl"], "$b"),
            "local.get $m", "i32.load offset=4", "i32.const 0", "local.get $a",
            "i32.const 0", "call $hamt$collect", "drop",
            "i32.const 1", "local.set $w",
            "block $sorted", "loop $pass",
            "local.get $w", "local.get $n", "i32.ge_u", "br_if $sorted",
            "i32.const 0", "local.set $i",
            "block $runs", "loop $run",
            "local.get $i", "local.get $n", "i32.ge_u", "br_if $runs",
            "local.get $i", "local.get $w", "i32.add", "local.tee $mid",
            "local.get $n", "local.get $mid", "local.get $n", "i32.lt_u", "select",
            "local.set $mid",
            "local.get $mid", "local.get $w", "i32.add", "local.tee $hi",
            "local.get $n", "local.get $hi", "local.get $n", "i32.lt_u", "select",
            "local.set $hi",
            "local.get $i", "local.set $l",
            "local.get $mid", "local.set $r",
            "local.get $i", "local.set $o",
            "block $merged", "loop $take",
            "local.get $o", "local.get $hi", "i32.ge_u", "br_if $merged",
            "local.get $b", "local.get $o", "i32.const 2", "i32.shl", "i32.add",
            "local.get $r", "local.get $hi", "i32.ge_u",
            "if (result i32)", "i32.const 1",
            "else",
            "local.get $l", "local.get $mid", "i32.lt_u",
            "if (result i32)",
            "local.get $a", "local.get $l", *seq,
            "local.get $a", "local.get $r", *seq, "i64.lt_u",
            "else", "i32.const 0", "end",
            "end",
            "if (result i32)",
            "local.get $a", "local.get $l", "i32.const 2", "i32.shl", "i32.add",
            "i32.load",
            "local.get $l", "i32.const 1", "i32.add", "local.set $l",
            "else",
            "local.get $a", "local.get $r", "i32.const 2", "i32.shl", "i32.add",
            "i32.load",
            "local.get $r", "i32.const 1", "i32.add", "local.set $r",
            "end",
            "i32.store",
            "local.get $o", "i32.const 1", "i32.add", "local.set $o",
            "br $take", "end", "end",
            "local.get $hi", "local.set $i",
            "br $run", "end", "end",
            "local.get $a", "local.set $t", "local.get $b", "local.set $a",
            "local.get $t", "local.set $b",
            "local.get $w", "i32.const 1", "i32.shl", "local.set $w",
            "br $pass", "end", "end",
            "local.get $a",
        ])


# =====================================================================
# The operations
# =====================================================================

def _params(name: str, tag: str) -> list[tuple[str, str]]:
    if tag == "s":
        return [(f"{name}p", "i32"), (f"{name}l", "i32")]
    return [(name, PARAMS[tag][0])]


def _word(name: str, tag: str, *, key: bool) -> list[str]:
    """The 64-bit word of the value the parameters *name* hold."""
    if tag == "i":
        return [f"local.get ${name}"]
    if tag == "f":
        canon = ["call $hamt$canon"] if key else []
        return [f"local.get ${name}", *canon, "i64.reinterpret_f64"]
    if tag == "s":
        return [f"local.get ${name}p", "i64.extend_i32_u", f"local.get ${name}l",
                "i64.extend_i32_u", "i64.const 32", "i64.shl", "i64.or"]
    return [f"local.get ${name}", "i64.extend_i32_u"]


def _hash(name: str, tag: str) -> list[str]:
    """The hash of the key the parameters *name* hold, its word in ``$kw``."""
    if tag == "s":
        return [f"local.get ${name}p", f"local.get ${name}l", "call $hamt_hash$s"]
    return ["local.get $kw", "call $hamt_hash$w"]


def _roots(name: str, tag: str) -> list[str]:
    """Root the heap value the parameters *name* hold, when they hold one."""
    if tag == "s":
        return _push(f"{name}p")
    if tag == "b":
        return _push(name)
    return []


def _keyed(op: str, tags: dict[str, str]) -> tuple[str, str]:
    """The key tag and the key slot of a keyed operation."""
    slot = "e" if op.startswith("set_") else "k"
    return tags[slot], slot


def _deps_for_key(tag: str) -> tuple[str, ...]:
    deps: tuple[str, ...] = (f"hamt_hash${_cls(tag)}",)
    if tag == "f":
        deps += ("hamt$canon",)
    return deps


def _op_new(name: str) -> tuple[str, tuple[str, ...]]:
    return _func(name, [], ["i32"], [], ["call $hamt$new"]), ("hamt$new",)


def _op_size(name: str) -> tuple[str, tuple[str, ...]]:
    return _func(name, [("m", "i32")], ["i64"], [],
                 ["local.get $m", "i32.load", "i64.extend_i32_u"]), ()


def _op_insert(name: str, op: str, tags: dict[str, str]) -> tuple[str, tuple[str, ...]]:
    kt, _slot = _keyed(op, tags)
    vt = tags.get("v")
    params = [("m", "i32"), *_params("k", kt)]
    if vt is not None:
        params += _params("v", vt)
    value = _word("v", vt, key=False) if vt is not None else ["i64.const 0"]
    body = [
        *_save(), *_push("m"), *_roots("k", kt),
        *(_roots("v", vt) if vt is not None else []),
        *_word("k", kt, key=True), "local.set $kw",
        "local.get $m", *_hash("k", kt), "local.get $kw", *value,
        f"call $hamt_insert${_cls(kt)}", "local.set $r",
        *_restore(), "local.get $r",
    ]
    text = _func(name, params, ["i32"], [("sp", "i32"), ("kw", "i64"), ("r", "i32")], body)
    return text, (f"hamt_insert${_cls(kt)}", *_deps_for_key(kt))


def _op_remove(name: str, op: str, tags: dict[str, str]) -> tuple[str, tuple[str, ...]]:
    kt, _slot = _keyed(op, tags)
    body = [
        *_save(), *_push("m"), *_roots("k", kt),
        *_word("k", kt, key=True), "local.set $kw",
        "local.get $m", *_hash("k", kt), "local.get $kw",
        f"call $hamt_remove${_cls(kt)}", "local.set $r",
        *_restore(), "local.get $r",
    ]
    text = _func(name, [("m", "i32"), *_params("k", kt)], ["i32"],
                 [("sp", "i32"), ("kw", "i64"), ("r", "i32")], body)
    return text, (f"hamt_remove${_cls(kt)}", *_deps_for_key(kt))


def _op_contains(name: str, op: str, tags: dict[str, str]) -> tuple[str, tuple[str, ...]]:
    kt, _slot = _keyed(op, tags)
    body = [
        *_word("k", kt, key=True), "local.set $kw",
        "local.get $m", *_hash("k", kt), "local.get $kw",
        f"call $hamt_find${_cls(kt)}", "i32.const 0", "i32.ne",
    ]
    text = _func(name, [("m", "i32"), *_params("k", kt)], ["i32"], [("kw", "i64")], body)
    return text, (f"hamt_find${_cls(kt)}", *_deps_for_key(kt))


def _option_some(vt: str) -> tuple[int, list[str]]:
    """The size of a `Some` of a value of *vt*, and the stores of its field
    from the entry ``$e`` into the block ``$o`` (``vera.wasm.helpers``'
    ``field_layout``: the field after the tag, at its alignment)."""
    if vt in ("i", "f"):
        return 16, ["local.get $o", "local.get $e", "i64.load offset=24",
                    "i64.store offset=8"]
    if vt == "s":
        return 16, ["local.get $o", "local.get $e", "i64.load offset=24",
                    "i64.store offset=4"]
    return 8, ["local.get $o", "local.get $e", "i32.load offset=24", "i32.store offset=4"]


def _op_get(name: str, tags: dict[str, str]) -> tuple[str, tuple[str, ...]]:
    kt, vt = tags["k"], tags["v"]
    size, field = _option_some(vt)
    body = [
        *_save(), *_push("m"), *_roots("k", kt),
        *_word("k", kt, key=True), "local.set $kw",
        "local.get $m", *_hash("k", kt), "local.get $kw",
        f"call $hamt_find${_cls(kt)}", "local.set $e",
        "local.get $e", "i32.eqz",
        "if",
        "i32.const 8", "call $alloc", "local.tee $o", f"i32.const {_NONE_TAG}",
        "i32.store",
        "else",
        f"i32.const {size}", "call $alloc", "local.tee $o", f"i32.const {_SOME_TAG}",
        "i32.store", *field,
        "end",
        *_restore(), "local.get $o",
    ]
    text = _func(name, [("m", "i32"), *_params("k", kt)], ["i32"],
                 [("sp", "i32"), ("kw", "i64"), ("e", "i32"), ("o", "i32")], body)
    return text, (f"hamt_find${_cls(kt)}", *_deps_for_key(kt))


def _cell_store(tag: str, offset: int) -> list[str]:
    """Store the word at *offset* of the entry ``$e`` in the cell ``$c``."""
    if tag in ("i", "f", "s"):
        return ["local.get $c", "local.get $e", f"i64.load offset={offset}", "i64.store"]
    if tag == "y":
        return ["local.get $c", "local.get $e", f"i32.load offset={offset}", "i32.store8"]
    return ["local.get $c", "local.get $e", f"i32.load offset={offset}", "i32.store"]


def _op_enumerate(name: str, tag: str, offset: int) -> tuple[str, tuple[str, ...]]:
    """The keys (*offset* 16) or the values (24) of the map ``$m`` as an
    array of *tag*'s cells, in insertion order."""
    cell = CELL[tag]
    body = [
        *_save(), *_push("m"),
        "local.get $m", "i32.load", "local.tee $n", "i32.eqz",
        "if", *_restore(), "i32.const 0", "i32.const 0", "return", "end",
        "local.get $m", "call $hamt$sorted", "local.set $buf",
        *_alloc(["local.get $n", f"i32.const {cell}", "i32.mul"], "$out"),
        "i32.const 0", "local.set $i",
        "block $done", "loop $cells",
        "local.get $i", "local.get $n", "i32.ge_u", "br_if $done",
        "local.get $buf", "local.get $i", "i32.const 2", "i32.shl", "i32.add",
        "i32.load", "local.set $e",
        "local.get $out", "local.get $i", f"i32.const {cell}", "i32.mul", "i32.add",
        "local.set $c",
        *_cell_store(tag, offset),
        "local.get $i", "i32.const 1", "i32.add", "local.set $i",
        "br $cells", "end", "end",
        *_restore(), "local.get $out", "local.get $n",
    ]
    text = _func(name, [("m", "i32")], ["i32", "i32"],
                 [("sp", "i32"), ("n", "i32"), ("buf", "i32"), ("out", "i32"),
                  ("i", "i32"), ("e", "i32"), ("c", "i32")], body)
    return text, ("hamt$sorted",)


def _cell_word(array: str, tag: str, *, key: bool) -> list[str]:
    """The word of cell ``$i`` of the array at *array*."""
    cell = CELL[tag]
    at = [f"local.get {array}", "local.get $i", f"i32.const {cell}", "i32.mul", "i32.add"]
    if tag in ("i", "s"):
        return [*at, "i64.load"]
    if tag == "f":
        canon = ["call $hamt$canon"] if key else []
        return [*at, "f64.load", *canon, "i64.reinterpret_f64"]
    if tag == "y":
        return [*at, "i32.load8_u", "i64.extend_i32_u"]
    return [*at, "i32.load", "i64.extend_i32_u"]


def _op_from_arrays(name: str, tags: dict[str, str]) -> tuple[str, tuple[str, ...]]:
    """The map of the keys and values two arrays hold, inserted in order: a
    host builds a map in one call to this export (a later duplicate key
    keeps the first one's position and takes its value)."""
    kt, vt = tags["k"], tags["v"]
    if kt == "s":
        hash_key = ["local.get $kw", "i32.wrap_i64", "local.get $kw", "i64.const 32",
                    "i64.shr_u", "i32.wrap_i64", "call $hamt_hash$s"]
    else:
        hash_key = ["local.get $kw", "call $hamt_hash$w"]
    body = [
        *_save(), *_push("kp"), *_push("vp"),
        "call $hamt$new", "local.set $m",
        "global.get $gc_sp", "local.set $slot", *_push("m"),
        "i32.const 0", "local.set $i",
        "block $done", "loop $pairs",
        "local.get $i", "local.get $kn", "i32.ge_u", "br_if $done",
        *_cell_word("$kp", kt, key=True), "local.set $kw",
        "local.get $m", *hash_key, "local.get $kw", *_cell_word("$vp", vt, key=False),
        f"call $hamt_insert${_cls(kt)}", "local.set $m",
        "local.get $slot", "local.get $m", "i32.store",
        "local.get $i", "i32.const 1", "i32.add", "local.set $i",
        "br $pairs", "end", "end",
        *_restore(), "local.get $m",
    ]
    text = _func(name, [("kp", "i32"), ("kn", "i32"), ("vp", "i32"), ("vn", "i32")],
                 ["i32"], [("sp", "i32"), ("m", "i32"), ("slot", "i32"), ("i", "i32"),
                           ("kw", "i64")], body)
    return text, ("hamt$new", f"hamt_insert${_cls(kt)}", *_deps_for_key(kt))


# =====================================================================
# The table
# =====================================================================

_SHARED: dict[str, Callable[[], str]] = {
    "hamt$new": _hamt_new, "hamt$mix": _hamt_mix, "hamt$canon": _hamt_canon,
    "hamt$entry": _hamt_entry, "hamt$merge": _hamt_merge,
    "hamt$node_set": _hamt_node_set, "hamt$node_add_entry": _hamt_node_add_entry,
    "hamt$node_entry_to_sub": _hamt_node_entry_to_sub,
    "hamt$node_remove_entry": _hamt_node_remove_entry,
    "hamt$node_sub_to_entry": _hamt_node_sub_to_entry,
    "hamt$coll_set": _hamt_coll_set, "hamt$coll_add": _hamt_coll_add,
    "hamt$coll_remove": _hamt_coll_remove,
    "hamt$collect": _hamt_collect, "hamt$sorted": _hamt_sorted,
}

#: What each shared helper calls.
_SHARED_DEPS: dict[str, tuple[str, ...]] = {
    "hamt$merge": ("hamt$merge",),
    "hamt$sorted": ("hamt$collect",),
}

#: The helper ``eq_String`` is ``WasmContext``'s, shared with ``==``.
EQ_STRING = "eq_String"


def _per_class(name: str) -> tuple[str, tuple[str, ...]]:
    base, _, cls = name.partition("$")
    eq: tuple[str, ...] = (EQ_STRING,) if cls == "s" else ()
    if base == "hamt_hash":
        return _hamt_hash(cls), ("hamt$mix",)
    if base == "hamt_ins":
        return _hamt_ins(cls), ("hamt$entry", "hamt$merge", "hamt$node_set",
                                "hamt$node_add_entry", "hamt$node_entry_to_sub",
                                "hamt$coll_set", "hamt$coll_add", *eq)
    if base == "hamt_insert":
        return _hamt_insert(cls), (f"hamt_ins${cls}", "hamt$entry")
    if base == "hamt_find":
        return _hamt_find(cls), eq
    if base == "hamt_rem":
        return _hamt_rem(cls), ("hamt$node_set", "hamt$node_remove_entry",
                                "hamt$node_sub_to_entry", "hamt$coll_remove", *eq)
    if base == "hamt_remove":
        return _hamt_remove(cls), (f"hamt_rem${cls}",)
    raise KeyError(name)


def helper(name: str) -> tuple[str, tuple[str, ...]]:
    """The text of the helper *name* and the helpers it calls."""
    if name in _SHARED:
        return _SHARED[name](), _SHARED_DEPS.get(name, ())
    if name.startswith("hamt_"):
        return _per_class(name)
    op, tags = _parse(name)
    if op in ("map_new", "set_new"):
        return _op_new(name)
    if op in ("map_size", "set_size"):
        return _op_size(name)
    if op in ("map_insert", "set_add"):
        return _op_insert(name, op, tags)
    if op in ("map_remove", "set_remove"):
        return _op_remove(name, op, tags)
    if op in ("map_contains", "set_contains"):
        return _op_contains(name, op, tags)
    if op == "map_get":
        return _op_get(name, tags)
    if op == "map_keys":
        return _op_enumerate(name, tags["k"], 16)
    if op == "set_to_array":
        return _op_enumerate(name, tags["e"], 16)
    if op == "map_values":
        return _op_enumerate(name, tags["v"], 24)
    if op == "map_from_arrays":
        return _op_from_arrays(name, tags)
    raise KeyError(name)


def register(
    name: str, helpers: dict[str, str], request_eq: Callable[[], None],
) -> None:
    """Add the helper *name* and every helper it calls to *helpers*, each
    once.  ``$eq_String``, which a `String` key compares by, is the one the
    trie shares with ``==`` and does not generate, so *request_eq* asks the
    caller for it."""
    for needed in closure(name):
        if needed == EQ_STRING:
            request_eq()
        elif needed not in helpers:
            helpers[needed] = helper(needed)[0]


def closure(name: str) -> Iterator[str]:
    """*name* and every helper it calls, each once, ``eq_String`` included."""
    seen: set[str] = set()
    stack = [name]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        yield current
        if current != EQ_STRING:
            stack.extend(helper(current)[1])
