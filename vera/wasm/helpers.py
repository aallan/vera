"""Shared helpers and data classes for the WASM translation layer.

Contains WasmSlotEnv, StringPool, and module-level helper functions
used by multiple wasm submodules.  Kept separate to avoid circular
imports between context.py and the mixin modules.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass, field

from vera import ast
from vera.skip import CodegenInvariantError
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

# #705: Vera type names that compile to ``i32`` WASM type but are
# inline values (not heap pointers).  Bindings of these types — at
# match arms, let statements, and let-destruct field extractions —
# do NOT need to be shadow-pushed onto the GC stack, because
# reclaiming an inline value is a no-op (the value isn't a pointer
# to anything).
#
# Hoisted to ``helpers.py`` so ``data.py`` and ``context.py`` share
# the same authoritative set — previously duplicated in both files
# with cross-referencing comments, which would silently drift if
# someone added a new inline-i32 type (e.g. a hypothetical ``Char``
# primitive) to one but not the other.
_INLINE_I32_TYPES = frozenset({"Bool", "Byte", "Unit"})


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

    def bindings_added_since(
        self, older: WasmSlotEnv
    ) -> list[tuple[str, int]]:
        """The ``(type_name, local_idx)`` bindings this env has and *older*
        does not, in binding order.

        The statement-scoped GC rooting (#1371) asks exactly this question:
        a statement reclaims every shadow root its lowering made and then
        re-roots what it BOUND, and what it bound is the environment delta.
        Reading the delta is what lets one rule serve `let`, pair-`let` and
        `let`-destructure alike, instead of each producer remembering to
        root its own binding and each then having to remember not to.

        A binding only ever appends to its type's stack, so the delta is
        the tail of each stack past the older env's length.
        """
        added: list[tuple[str, int]] = []
        for type_name, stack in self._stacks.items():
            previous = len(older._stacks.get(type_name, ()))
            added.extend((type_name, idx) for idx in stack[previous:])
        return added


# =====================================================================
# The two names one State cell answers to (#1218)
# =====================================================================

@dataclass(frozen=True)
class CellNames:
    """A State cell's IDENTITY and its REPRESENTATION, carried together.

    *family* is :func:`vera.naming.family_name` — what the checker's cell
    type renders to, what the host symbol is mangled from, and the ONLY
    thing two cells are ever compared on.  *base* is
    :func:`vera.naming.family_base_name` — the same type with its
    refinements stripped, which decides the WASM value type, pointer-ness,
    and which #1203 write guard applies.

    They differ exactly when the cell type is refined (#1218): `State<Pos>`,
    `State<Neg>` and `State<Int>` are three cells that are all i64.  Before
    #1218 one string did both jobs, so making it discriminate the predicate
    would have silently switched off every decision keyed on `"Nat"` /
    `"Int"` / `"Byte"` / `"Bool"` / `"String"` — the guards would stop being
    emitted while the verifier went on recording them as `tier3_runtime`.

    Recorded per OP NAME in ``WasmContext._effect_op_cells``, in lock-step
    with ``_effect_ops``, so a `get`/`put` call site can ask what cell it
    dispatches to WITHOUT parsing the mangled import name back out of its
    own dispatch target.  That parse was a second, independent derivation of
    the family — the seam #1233's round-5 review found re-mangling an
    already-mangled name at — and it is gone: one canonical family is
    threaded to both consumers.

    *type_expr* is the cell type as it was WRITTEN, carried for the one
    question neither name can answer: a refined cell's PREDICATE (#1268).
    ``family`` renders it and ``base`` strips it, but the #1268 payload guard
    has to LOWER it, so the guard reads the type expression its producer
    already held rather than parsing a predicate back out of a mangled family
    — the second-derivation trap #1218/#1233 closed everywhere else.  Excluded
    from equality (``compare=False``): a cell's identity is its family, and a
    ``TypeExpr`` carries source spans, so comparing it would make two cells of
    one family differ by where each was written.
    """

    family: str
    base: str
    type_expr: ast.TypeExpr | None = field(default=None, compare=False)


# =====================================================================
# State handler clause registry entry (#976 / #1211)
# =====================================================================

@dataclass(frozen=True)
class StateClauseEntry:
    """One ``handle[State<T>]`` clause, plus the scope it compiles in.

    Registered per op name by ``_translate_handle_state`` and consumed by
    ``_translate_state_clause_op``, which inlines the clause body at each
    get/put call site in the handled body (#976 intrinsic-hybrid semantics).

    Everything after ``put_import`` is the handler-DECLARATION scope — the
    context that existed at the ``handle`` expression, before this handler
    installed its own bindings and op registries.  The checker checks clause
    bodies THERE (§7.5.2): a clause is not part of the body it refines, so
    both an outer slot reference and a bare ``get``/``put`` in a clause body
    resolve against the enclosing context, not against this handler.  Keeping
    the whole declaration-time scope in one record is what stops the two
    halves drifting — ``decl_env`` alone was threaded first (#1202) and the
    op registries were left at the innermost handler's, so a bare op in a
    nested handler's clause body wrote the WRONG CELL (#1211).

    Fields (each has a consumer — the tuple this replaced also carried the
    effect argument's alias-opaque source spelling, which nothing unpacking
    it ever read):
        clause: the ``HandlerClause`` to inline.
        family: the resolved cell family — the cell's IDENTITY, so import
            naming and every comparison against another cell (#1218).
        family_base: the same family with its refinements stripped — the
            cell's REPRESENTATION, so WASM value type, pointer-ness, and
            which #1203 write guard applies.  Both are carried because a
            refined cell needs both and they differ: `State<Pos>` is its own
            cell (identity) and is an i64 taking the plain `Int` guards
            (representation).
        state_slot_name: the state annotation's slot name; ``None`` for a
            stateless handler, which binds no state slot in the checker.
        decl_env: the declaration scope's slot environment.
        get_import / put_import: this handler's own host-cell imports — the
            intrinsic read/store the clause refines, not a declaration-time
            value.
        decl_effect_ops / decl_effect_op_result_wt / decl_effect_op_result_vera
        / decl_effect_op_cells:
            the four op registries as they stood at the declaration.
        decl_state_clause_ops: the clause registry as it stood at the
            declaration — the ENCLOSING handlers' clauses, never this
            handler's own, so re-entering an op from inside a clause body
            walks strictly outwards and terminates.
        decl_addressable_from: how many host cells were pushed at the
            declaration — the index into ``_pushed_cell_families`` from which
            this clause body's cells are SHADOWS.  A bare op in the clause
            body resolves into the declaration scope, but the host intrinsics
            address only the innermost cell of a family, so an op whose family
            appears at or after this index cannot reach its cell (#1233).
    """

    clause: ast.HandlerClause
    family: str
    family_base: str
    state_slot_name: str | None
    decl_env: WasmSlotEnv
    get_import: str
    put_import: str
    decl_effect_ops: dict[str, tuple[str, bool]]
    decl_effect_op_result_wt: dict[str, str | None]
    decl_effect_op_result_vera: dict[str, str | None]
    decl_effect_op_cells: dict[str, CellNames]
    decl_state_clause_ops: dict[str, "StateClauseEntry"]
    decl_addressable_from: int


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

# The line that opens every ``gc_shadow_push`` sequence.  Named once so the
# emitter below and :func:`contains_shadow_push` read the SAME spelling — two
# independently-maintained copies would let a reworded emitter silently stop
# being detected, and the detector's caller (#1322's match scoping) would then
# emit no ``$gc_sp`` restore for a match that does push.
_SHADOW_PUSH_MARKER = "global.get $gc_stack_limit"


def gc_shadow_push(local_idx: int) -> list[str]:
    """Generate WAT instructions to push an i32 value onto the GC shadow stack.

    Stores the value from ``local_idx`` at the current shadow-stack
    pointer (``$gc_sp``) and advances ``$gc_sp`` by 4 bytes.  Traps
    if the push would overflow the shadow stack into the GC worklist
    region — bounding the FULL four-byte slot, not just its first byte
    (#791, and its four siblings in #860), so a ``$gc_sp`` that lands
    within four bytes of ``$gc_stack_limit`` cannot store past the end.
    """
    return [
        "global.get $gc_sp",
        "i32.const 4",
        "i32.add",
        _SHADOW_PUSH_MARKER,
        "i32.gt_u",
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


def contains_shadow_push(instructions: Iterable[str]) -> bool:
    """Whether *instructions* contains at least one :func:`gc_shadow_push`.

    Answers the one question #1322's match scoping needs: did lowering this
    sub-expression put anything on the shadow stack that a ``$gc_sp`` restore
    would have to reclaim?  A match that pushed nothing gets no wrapper, so
    the emitted WAT of a non-rooting match is unchanged and — decisively — a
    function whose lowering never sets ``needs_alloc`` never acquires a
    reference to ``$gc_sp``, a global that only exists when it does.

    Several call sites indent the emitted lines before appending them, so the
    match is on the stripped line.  ``$gc_stack_limit`` is read nowhere else
    inside a function body: its only other consumers are ``$register_wrapper``
    and the collector in ``vera/codegen/assembly.py``, which are assembled as
    whole functions and never flow through an instruction list.
    """
    return any(i.strip() == _SHADOW_PUSH_MARKER for i in instructions)


# =====================================================================
# Whitespace predicate emitter
# =====================================================================

def emit_is_ascii_whitespace(byte_local: int, indent: str = "") -> list[str]:
    """Generate WAT instructions for the canonical ASCII-whitespace
    predicate.

    Reads the byte value from ``byte_local`` and leaves a 0/1 i32 on
    the operand stack.  Matches Python's ``str.isspace()`` ASCII set:
    ``{tab(9), LF(10), VT(11), FF(12), CR(13), space(32)}``.  The
    four contiguous control codes 9..=13 collapse into a single
    branchless range check ``(byte - 9) < 5``.

    All four sites that test for ASCII whitespace
    (``_translate_is_whitespace``, ``_translate_trim``'s
    ``_is_ws_inline`` closure, and the count and emit passes inside
    ``_translate_structural_split`` for ``string_words``) MUST go
    through this helper rather than re-encoding the byte literals.
    Open-coded copies will silently diverge — see PR #510 round 2,
    where ``_translate_strip`` open-coded a narrower set
    {32, 9, 10, 13} that lacked VT/FF.

    The helper does NOT load the byte from memory (callers vary on
    whether they read via ``i32.load8_u`` then ``local.set`` or are
    handed the byte some other way) and does NOT consume the result
    (callers may ``i32.eqz`` it for early-exit, ``if``-test it, or
    OR it into a running accumulator).
    """
    return [
        f"{indent}local.get {byte_local}",
        f"{indent}i32.const 32",
        f"{indent}i32.eq",
        f"{indent}local.get {byte_local}",
        f"{indent}i32.const 9",
        f"{indent}i32.sub",
        f"{indent}i32.const 5",
        f"{indent}i32.lt_u",
        f"{indent}i32.or",
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

def _strip_future(name: str) -> str:
    """Strip representation-transparent ``Future<…>`` wrappers (#1045).

    ``Future<T>`` has the SAME array-element representation as its payload
    ``T`` (#841), so the element sizing / load / store / wasm-type
    decisions below must see through the wrapper and key on ``T``.
    Loops so nested futures (``Future<Future<Int>>``) collapse fully.

    String-form only — aliases are pre-resolved by the caller
    (``vera/wasm/data.py`` canonicalizes via ``_canonicalize_alias_slot_name``
    then ``_resolve_base_type_name`` before these helpers), so an *aliased*
    future (``type Fut = Future<Int>``) arrives as the FULL compound
    spelling ``"Future<Int>"`` and is stripped normally here (#1058); the
    canonicaliser is what recovers the payload the name-only resolve
    dropped.
    """
    while name.startswith("Future<") and name.endswith(">"):
        name = name[7:-1]
    return name


# Opaque host-handle types: i32 indices into Python-side host stores
# (`_map_store`, `_set_store`, `_decimal_store` in
# `vera/codegen/api.py`).  These look like i32 heap pointers to the
# default GC heuristic but are NOT pointers into the Vera GC heap, so:
#
#   - Pushing them onto the GC shadow stack as roots wastes shadow-
#     stack space (#347), and a handle index in the heap-pointer
#     range with valid alignment would cause spurious marks of
#     unrelated heap objects during the conservative mark phase.
#
#   - Treating them as ADT heap pointers in `array_fold` /
#     `array_map` rooting heuristics (#490) extends the same problem
#     into the iterative-builder loops.
#
# String/Array (pair types) ARE GC-managed and remain rooted.  ADT
# types (Option, Result, user data, Json, Html, etc.) are
# GC-managed.  Only the three host-handle types below are excluded.
#
# Note: per-execute() handle leaks for these stores are tracked
# separately as #346 — that's an active-reclamation problem
# distinct from the rooting decision the classifier informs.
#
# #573 phases 1-3: ``Map``, ``Set``, and ``Decimal`` have all
# migrated to the heap-wrap-as-ADT scheme.  Their values are now
# pointers to GC-managed wrapper ADTs (8-byte objects holding the
# real i32 host handle in field 0); they ARE Vera-heap pointers
# and MUST be rooted, so the set is empty.  Any future host-
# handle type added without wrapper migration would be added
# here, but in practice all host-handle types should follow the
# wrap-as-ADT pattern from the start.
_HOST_HANDLE_TYPES: frozenset[str] = frozenset()


def _is_host_handle_type(type_name: str | None) -> bool:
    """Return True if `type_name` names an opaque host-handle type
    that should be excluded from GC-rooting decisions.

    Pre-#573 (v0.0.132): used to exclude ``Map`` / ``Set`` /
    ``Decimal`` handles from shadow-stack rooting because those
    values lowered to raw i32 host-store indices — not Vera-heap
    pointers — and the conservative GC's mark phase would either
    reject them via the heap-range check (the common case) or
    spuriously mark an unrelated heap object whose address
    happened to match a handle value.

    Post-#573 (v0.0.134): all three types migrated to the
    heap-wrap-as-ADT scheme.  Their values are now pointers to
    GC-managed wrapper ADTs and DO require rooting, so the
    underlying ``_HOST_HANDLE_TYPES`` set is empty and this
    helper always returns False.  The function is kept rather
    than deleted so future host-handle types added without
    wrapper migration have an obvious place to register their
    exclusion.

    Parametric forms like `Map<K, V>` strip to the bare head; we
    match on prefix.  ``Regex`` was historically discussed for
    inclusion but Vera doesn't expose a `Regex` value type —
    regex operations take pattern strings and return Result, with
    no persistent host-side handle.
    """
    if type_name is None:
        return False
    if type_name in _HOST_HANDLE_TYPES:
        return True
    # Parametric form: Map<K, V>, Set<T>, etc.
    head = type_name.split("<", 1)[0]
    return head in _HOST_HANDLE_TYPES


# The inline i32 scalars, as a REPRESENTATION question — `Unit` is absent
# because it has no WASM value at all, so no boundary ever asks whether one
# is a pointer (`_INLINE_I32_TYPES` above answers the different question of
# which BINDINGS need no push, and a Unit binding is one of them).
_NON_POINTER_I32_BASES = frozenset({"Bool", "Byte"})

# The largest value an inline i32 scalar can hold: `@Byte` is 0..255 and
# `@Bool` is 0/1 (spec §11).  Read by the heap-layout guard in
# `vera/codegen/assembly.py`, which keeps the GC heap above this range so a
# scalar that reached the shadow stack could never be mistaken for a
# pointer by the conservative mark phase.
MAX_INLINE_I32_VALUE = 255


def is_gc_pointer_base(base_name: str) -> bool:
    """Whether an ``i32``-lowered value is a Vera-heap pointer to be rooted.

    THE pointer-ness rule (#1255), stated once.  An ``i32`` is either an
    inline scalar (``@Bool`` / ``@Byte``), an opaque host handle, or a
    pointer into the GC heap; only the last must go on the shadow stack,
    and pushing one of the others costs a slot and a spurious mark
    candidate.  Callers pair it with their own ``wt == "i32"`` test — the
    pair convention (String / Array) is a pointer by construction and is
    decided by width, not by name.

    *base_name* MUST be the REPRESENTATION base — the name after alias
    chasing and refinement stripping, which is
    :func:`vera.naming.family_base_name` from a type expression and
    ``WasmContext._resolve_base_type_name`` from a slot name.  The
    syntactic head is what #1255 was: ``type SmallByte = { @Byte | … }``
    answers ``SmallByte``, which is in neither set, so every closure
    parameter, return and capture of a refined or aliased scalar was rooted
    as though it were a heap pointer.  Inert, because the mark phase's
    first guard rejects anything below the heap (see the layout invariant
    in ``vera/codegen/assembly.py``) — but a classification rule cannot
    rely on a downstream range check to be right.

    The parameter is a plain ``str``, not ``str | None``: both admissible
    producers are total — ``family_base_name`` falls back to
    :func:`vera.slots.family_fallback_name` rather than returning ``None``,
    and ``_resolve_base_type_name`` returns its input unchanged when it
    resolves no further.  An optional parameter here would have been a
    branch no caller can reach, and one that quietly invited a caller to
    hand over ``_type_expr_to_slot_name``'s optional result — the very
    syntactic-head spelling this replaces.
    """
    return (base_name not in _NON_POINTER_I32_BASES
            and not _is_host_handle_type(base_name))


def state_type_arg(effect_ref: ast.EffectRefNode) -> ast.TypeExpr:
    """The single type argument of a ``State<T>`` effect reference.

    Shape validation only, shared by the two sides that name that argument
    (#1208): the ``WasmContext`` translating ``old(State<T>)`` and the
    ``CodeGenerator`` collecting which snapshots to allocate.  The NAMING is
    deliberately not done here — each side renders through its own alias
    environment, and the whole point of the one renderer is that a name is a
    function of the environment it is asked in.
    """
    if not isinstance(effect_ref, ast.EffectRef):
        raise CodegenInvariantError(  # pragma: no cover
            "State type ref is not an EffectRef", effect_ref)
    if effect_ref.name != "State":
        raise CodegenInvariantError(  # pragma: no cover
            "State type ref name is not 'State'", effect_ref)
    if not effect_ref.type_args or len(effect_ref.type_args) != 1:
        raise CodegenInvariantError(  # pragma: no cover
            "State<T> must have exactly one type argument", effect_ref)
    return effect_ref.type_args[0]
