"""Every trap code generation can emit, named once (#1479).

A runtime trap reaches its user through three hops — the check code
generation emits, the signal that check raises, and the host that turns the
signal into a ``trap_kind``, a message and a Fix paragraph — and each hop
used to state the trap on its own terms.  This module is the one statement
all of them read:

* :data:`TRAP_KINDS` — every ``trap_kind`` value a host can report, with the
  code the :data:`TRAP_SIGNAL` import carries for it, its canonical
  description and its Fix paragraph.
* :data:`TRAP_EMITTERS` — every code-generation function that emits a check
  able to trap, the kind that check raises, and the verifier obligation kind
  (:data:`vera.obligations.core.ObligationKind`) it is the runtime half of.
* :class:`EmittedCheck` — one entry of the per-module record,
  ``CompileResult.emitted_checks``: which check a compiled module actually
  contains, at which source span.

The registry is data about the backend, so it is held to the backend rather
than trusted: ``tests/test_named_traps_1479.py`` scans the code-generation
package for every trap it emits and compares the answer with these tables.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from dataclasses import dataclass

#: The one host import a named check calls before its ``unreachable``.  Its
#: first argument is a :attr:`TrapKind.code`, the other two the
#: ``(pointer, length)`` of the check's own message in the data section (both
#: zero for a kind whose sites carry none).  One import carries every kind,
#: so naming a new trap costs a row in :data:`TRAP_KINDS` rather than a new
#: import and its fan-in.
TRAP_SIGNAL = "trap"

#: The contract channel: the message-carrying import every ``requires``,
#: ``ensures``, ``decreases`` and refinement check calls.  Its kind is always
#: ``contract_violation`` and its message is the contract's own text.
CONTRACT_SIGNAL = "contract_fail"


@dataclass(frozen=True)
class TrapKind:
    """One ``trap_kind`` value a host can report."""

    name: str
    """The ``trap_kind`` value: ``WasmTrapError.kind``, the JSON envelope's
    ``trap_kind``, and the browser runtime's ``VeraTrap.kind``."""

    code: int
    """The ``i32`` :data:`TRAP_SIGNAL` carries for this kind; ``0`` for a kind
    no check signals (a native instruction trap, the contract channel, a host
    error, or the generic ``unreachable``)."""

    description: str
    """The canonical one-line description.  It is the whole message for a
    kind whose sites carry none, and the fallback for one whose site message
    is missing."""

    fix: str
    """The Fix paragraph every host prints beneath the message.  Empty where
    the message itself is the instruction (a contract's text, a host
    binding's refusal) or no suggestion is possible (``unknown``).  The
    ``unreachable`` paragraph is derived from the internal roster rather than
    written here — see ``unreachable_fix_paragraph``."""

    site_message: bool = False
    """Whether each emission of this kind carries its own message: the
    operands of a subtraction, the text of an assertion, the index and its
    bound.  A kind whose sites carry none reports :attr:`description`."""


def _kinds(*rows: TrapKind) -> dict[str, TrapKind]:
    out: dict[str, TrapKind] = {}
    for row in rows:
        if row.name in out:  # pragma: no cover — a duplicate is a table typo
            raise ValueError(f"trap kind {row.name!r} declared twice")
        out[row.name] = row
    codes = [r.code for r in out.values() if r.code]
    if len(codes) != len(set(codes)):  # pragma: no cover — table typo
        raise ValueError("two trap kinds share a signal code")
    return out


# =====================================================================
# The generic `unreachable` kind and the causes that reach it
# =====================================================================

@dataclass(frozen=True)
class UnreachableCause:
    """One cause the generic ``unreachable`` Fix paragraph names.

    Every ``unreachable`` code generation emits either follows a signal that
    names its own kind, or sits at a site on :data:`INTERNAL_TRAPS`, whose
    entries each name one of these.  The paragraph is DERIVED from this
    table, so it names exactly the causes that can reach it — no cause the
    roster lacks, and no roster cause it omits.
    """

    key: str
    text: str
    """The sentences the paragraph carries for this cause."""


UNREACHABLE_CAUSES: tuple[UnreachableCause, ...] = (
    UnreachableCause(
        "shadow_stack_overflow",
        "GC shadow-stack overflow, which is what a DEEP RECURSION through a "
        "function holding heap references hits: every live frame roots its "
        "pointer parameters, its allocations, and the values it binds out "
        "of them, and the shadow stack holds 4 096 roots in total (16 KiB — "
        "`GC_STACK_SIZE` in `vera/codegen/assembly.py`).  A recursion that "
        "traps at a depth close to 4 096 divided by a small integer is this "
        "one: reduce the heap values live across the recursive call, or "
        "restructure so the call is in tail position (#549 GC-aware TCO "
        "restores `$gc_sp` at each hop, so the chain runs in constant shadow "
        "space).",
    ),
    UnreachableCause(
        "gc_worklist_overflow",
        "The collector's mark worklist overflowed: more heap objects were "
        "waiting to be marked at one time than its 16 384 entries hold "
        "(`GC_WORKLIST_SIZE` in `vera/codegen/assembly.py`), which one very "
        "wide live structure — an array or map holding more heap values "
        "than that — can reach.  Split the structure, or hold fewer heap "
        "values in it at once.",
    ),
    UnreachableCause(
        "wrap_table_overflow",
        "More than 4 096 host-backed values — `Map`, `Set`, `Decimal`, a "
        "parsed JSON or HTML map, a pending async request — were alive at "
        "once, and a collection freed none of them, so the table that "
        "tracks their host handles had no room for another.  Let values you "
        "no longer need become unreachable, or combine many small "
        "containers into fewer larger ones.",
    ),
    UnreachableCause(
        "wasi_io_failure",
        "Under `--target wasi-p2`, a standard stream, file or HTTP body the "
        "host provides failed part-way through an operation — a write to a "
        "closed stdout, a read error on stdin — and the adapter stopped the "
        "program rather than lose data.  The host's I/O failed, not the "
        "program's logic: check what the program's input and output are "
        "connected to.",
    ),
    UnreachableCause(
        "compiler_bug",
        "An internal consistency check failed: a garbage-collector "
        "invariant (`VERA_GC_CHECK_MARKS`), a runtime tripwire, or code the "
        "compiler places where execution cannot arrive — after a call that "
        "never returns (`IO.exit`, a handler that always throws) or in a "
        "function it dropped.  A well-typed program cannot reach any of "
        "these, so reaching one is a bug in Vera: please file a minimal "
        "reproducer at https://github.com/aallan/vera/issues/new.",
    ),
)

_COUNT_WORDS = ("One", "Two", "Three", "Four", "Five", "Six", "Seven",
                "Eight", "Nine")


def unreachable_fix_paragraph(
    causes: tuple[UnreachableCause, ...] = UNREACHABLE_CAUSES,
) -> str:
    """The generic ``unreachable`` Fix paragraph, derived from *causes*.

    A trap reaches the generic kind only by executing an ``unreachable`` no
    signal named, and every such site is on :data:`INTERNAL_TRAPS`; so the
    paragraph can say exactly which causes those are, and that none of them
    is a check on a value the program computed — each of those reports its
    own kind.
    """
    head = (
        f"{_COUNT_WORDS[len(causes) - 1]} causes reach this trap, and none "
        "of them is a check on a value the program computed — every such "
        "check reports its own kind."
    )
    body = "  ".join(
        f"({n}) {cause.text}" for n, cause in enumerate(causes, start=1))
    return f"{head}  {body}"


TRAP_KINDS: dict[str, TrapKind] = _kinds(
    TrapKind(
        "overflow", 1, "Integer overflow",
        "Integer arithmetic produced a value outside the representable "
        "range — the signed i64 range `[-2^63, 2^63)` for `@Int`, or the "
        "unsigned u64 range `[0, 2^64)` for `@Nat` (#808 routes `@Nat` "
        "overflows here too).  Add a `requires` precondition that "
        "constrains the operands so Z3 can prove the result is "
        "representable, or change the operation to a saturating / checked "
        "variant via a helper function.",
    ),
    TrapKind(
        "nat_guard", 2, "Negative value bound into a @Nat slot",
        "A negative `@Int` was bound into a `@Nat` slot — a `let @Nat = "
        "<@Int>`, a match or tuple-destructure binding, a constructor field, "
        "or a call / effect-operation argument whose formal is `@Nat`.  The "
        "verifier could not prove the value non-negative, so it left a "
        "runtime check here (Tier 3).  Add a `requires(... >= 0)` "
        "precondition, or narrow through an explicit branch "
        "(`if x >= 0 then { ... }`), so Z3 discharges it at compile time and "
        "the check becomes dead.",
    ),
    TrapKind(
        "widen_guard", 3,
        "@Nat value above i64.MAX widened into an @Int slot",
        "A `@Nat` value above `i64.MAX` was widened into an `@Int` slot — a "
        "return, a `let`, a call argument, a constructor field, an array "
        "element or a tuple component whose target is `@Int`.  `Nat` (u64) "
        "and `Int` (i64) share one machine representation, so such a value "
        "REINTERPRETS as a negative `@Int` (`u64.MAX` becomes `-1`); the "
        "verifier could not prove it in range, so it left a runtime check "
        "here (Tier 3).  Add a `requires(... <= i64.MAX)` precondition, or "
        "keep the value in `@Nat` and widen only where a bound is known, so "
        "Z3 discharges it at compile time and the check becomes dead.",
    ),
    TrapKind(
        "nat_underflow", 4, "@Nat subtraction would be negative",
        "A `@Nat` subtraction's right operand was larger than its left, so "
        "the result would have been negative, which no `@Nat` can hold.  "
        "The verifier could not prove the operands ordered, so it left a "
        "runtime check here (Tier 3).  Add the `requires(lhs >= rhs)` the "
        "message names to the enclosing function, or branch on the "
        "comparison first (`if lhs >= rhs then { lhs - rhs } else { ... }`), "
        "or compute in `@Int` where a negative result means something; "
        "`vera verify` then discharges the `nat_sub` obligation at compile "
        "time.",
        site_message=True,
    ),
    TrapKind(
        "assertion_failed", 5, "Assertion failed",
        "An `assert(...)` evaluated to false at run time: the property it "
        "states did not hold at that point, so either the property or the "
        "code reaching it is wrong — the message quotes the assertion.  When "
        "the property follows from the function's inputs, state it as a "
        "`requires(...)` so every caller must establish it and `vera verify` "
        "proves the assertion at compile time (Tier 1); `vera verify` also "
        "reports an assertion it can prove false as E507.",
        site_message=True,
    ),
    TrapKind(
        "index_out_of_bounds", 6, "Array index out of bounds",
        "An array index fell outside `[0, array_length(arr))`, so the read "
        "would have been outside the array.  Add a precondition naming the "
        "index and the array — `requires(i >= 0 && i < array_length(arr))` "
        "— or guard the access with an explicit branch, and `vera verify` "
        "proves the index in bounds at compile time (Tier 1); it reports an "
        "index it can prove out of bounds as E527.",
        site_message=True,
    ),
    TrapKind(
        "string_index_out_of_bounds", 7, "String index out of bounds",
        "`string_char_code(s, i)` reads the byte at index `i`, so `i` must "
        "lie in `[0, string_length(s))`.  `string_length` counts the BYTES "
        "of the UTF-8 encoding, not characters, so a string holding "
        "non-ASCII text is longer than its character count.  Add "
        "`requires(i >= 0 && i < string_length(s))`, or guard the call with "
        "an explicit branch.",
        site_message=True,
    ),
    TrapKind(
        "float_conversion", 8, "Float64 value outside the @Int range",
        "A `Float64` → `Int` conversion (`float_to_int`, `floor`, `ceil` or "
        "`round`) was given NaN, an infinity, or a value whose integer part "
        "lies outside `@Int`'s range `[-2^63, 2^63)`, none of which an "
        "`@Int` can hold.  Check the value first — `float_is_nan(x)`, "
        "`float_is_infinite(x)` and a range bound — in a `requires(...)` or "
        "an explicit branch; `vera verify` reports a constant argument it "
        "can prove out of the domain as E529.",
        site_message=True,
    ),
    TrapKind(
        "heap_exhausted", 9, "Heap exhausted",
        "The program ran out of heap memory.  The heap has a 2 GiB ceiling "
        "— one allocation, and all live data together, must stay below "
        "2^31 bytes (`$alloc` in `vera/codegen/assembly.py`) — and the host "
        "may refuse to grow memory before that.  The collector has already "
        "reclaimed everything unreachable when this fires, so the live data "
        "itself is too large: build smaller values (a very long "
        "`string_repeat`, `array_range` or accumulated string is the usual "
        "cause), or process the input in pieces instead of holding it all "
        "at once.  Under `--target wasi-p2`, one host result (an argument "
        "list, a line of input) must also fit the adapter's 64 KiB arena.",
    ),
    TrapKind(
        "contract_violation", 0, "Contract violation",
        "",
        site_message=True,
    ),
    TrapKind(
        "divide_by_zero", 0, "Integer division by zero",
        "Add a precondition `requires(divisor != 0)` on the function "
        "performing the division, or guard the division site with a "
        "non-zero check.  The Z3 verifier will then prove the division "
        "is safe at every call site at compile time.",
    ),
    TrapKind(
        "out_of_bounds", 0, "Out-of-bounds memory access",
        "A linear-memory load or store fell outside the module's memory.  "
        "Every array index and `string_char_code` index is bounds-checked "
        "before its access and reports `index_out_of_bounds` or "
        "`string_index_out_of_bounds` instead, and `string_slice` clamps its "
        "indices, so no check on a value your program computed reaches this "
        "kind: a runtime helper (`gc_collect`, `alloc`, a host binding) read "
        "or wrote outside memory, which is a bug in Vera rather than in the "
        "program — please file a minimal reproducer at "
        "https://github.com/aallan/vera/issues/new.",
    ),
    TrapKind(
        "stack_exhausted", 0, "WASM call stack exhausted",
        "Vera compiles tail-position calls to WASM `return_call` (#517, "
        "shipped in v0.0.126; allocating tail calls covered by GC-aware "
        "TCO in #549, v0.0.154), so iteration-shaped recursion runs in "
        "constant stack space — if you're still hitting this trap the "
        "recursion isn't actually in tail position.  Restructure with "
        "an accumulator parameter so the recursive call is the LAST "
        "thing the function does (no work after it, no `let`-binding "
        "of its result, no enclosing arithmetic).  One remaining "
        "exception: functions with a non-trivial runtime "
        "postcondition (`ensures` that emits a Tier-3 check) revert "
        "to plain `call` so the post-check runs after each call — "
        "either simplify the postcondition to one the verifier can "
        "discharge statically (Tier 1), or iterate via `array_fold` / "
        "`array_map` (which compile to WASM loops rather than "
        "recursion).",
    ),
    TrapKind(
        "unreachable", 0, "Reached `unreachable` WASM instruction",
        unreachable_fix_paragraph(),
    ),
    TrapKind("host_error", 0, "Host binding error", "", site_message=True),
    TrapKind("unknown", 0, "Unclassified trap", ""),
)


def kind_for_code(code: int) -> TrapKind | None:
    """The kind :data:`TRAP_SIGNAL` names by *code*, or None for a code no
    kind carries (which a module this compiler emitted never passes)."""
    for kind in TRAP_KINDS.values():
        if kind.code and kind.code == code:
            return kind
    return None


# =====================================================================
# The emitters
# =====================================================================

@dataclass(frozen=True)
class TrapEmitter:
    """One code-generation function that emits a check able to trap."""

    emitter: str
    """``<module under vera/>:<function>`` — the function whose decision it
    is to emit the check, e.g. ``"wasm/operators.py:_emit_nat_sub_guard"``.
    Every :class:`EmittedCheck` names one of these keys."""

    kind: str
    """The :data:`TRAP_KINDS` entry a failing check reports."""

    obligations: tuple[str, ...]
    """The verifier obligation kinds this check is the runtime half of —
    what a Tier-3 discharge of one of them relies on.  Empty for a check no
    obligation describes: a resource limit such as heap exhaustion."""

    via: str
    """How the check traps: ``"signal"`` (:data:`TRAP_SIGNAL`),
    ``"contract"`` (:data:`CONTRACT_SIGNAL`), or ``"native:<instruction>"``
    for a WASM instruction that traps by itself."""

    span: str
    """What an :class:`EmittedCheck` from this emitter locates: the node its
    span is taken from."""

    per_site: bool = True
    """Whether each emission is recorded in ``CompileResult.emitted_checks``.
    False for a runtime function (the allocator) that is emitted once per
    module and belongs to no source site."""


def _emitters(*rows: TrapEmitter) -> dict[str, TrapEmitter]:
    out: dict[str, TrapEmitter] = {}
    for row in rows:
        if row.emitter in out:  # pragma: no cover — table typo
            raise ValueError(f"trap emitter {row.emitter!r} declared twice")
        if row.kind not in TRAP_KINDS:  # pragma: no cover — table typo
            raise ValueError(f"{row.emitter}: unknown trap kind {row.kind!r}")
        out[row.emitter] = row
    return out


_VALUE = "the value expression the guard checks"
_OPERATION = "the expression performing the operation"

TRAP_EMITTERS: dict[str, TrapEmitter] = _emitters(
    # --- arithmetic ----------------------------------------------------
    TrapEmitter(
        "wasm/operators.py:_emit_overflow_guard", "overflow",
        ("int_overflow",), "signal", _OPERATION,
    ),
    TrapEmitter(
        "wasm/operators.py:_emit_nat_sub_guard", "nat_underflow",
        ("nat_sub",), "signal", _OPERATION,
    ),
    TrapEmitter(
        "wasm/operators.py:_translate_binary", "divide_by_zero",
        ("div_zero",), "native:i64.div_s i64.rem_s", _OPERATION,
    ),
    # --- the @Int / @Nat boundary -------------------------------------
    TrapEmitter(
        "wasm/operators.py:_emit_nat_bind_guard", "nat_guard",
        ("nat_bind",), "signal", _VALUE,
    ),
    TrapEmitter(
        "wasm/operators.py:_emit_int_widen_guard", "widen_guard",
        ("nat_to_int_coerce",), "signal", _VALUE,
    ),
    # --- assertions and indexing --------------------------------------
    TrapEmitter(
        "wasm/operators.py:_translate_assert", "assertion_failed",
        ("assert",), "signal", "the `assert(...)` expression",
    ),
    TrapEmitter(
        "wasm/data.py:_translate_index_expr", "index_out_of_bounds",
        ("index_bounds",), "signal", "the index expression `arr[i]`",
    ),
    TrapEmitter(
        "wasm/calls_strings.py:_translate_char_code",
        "string_index_out_of_bounds",
        ("index_bounds",), "signal", "the `string_char_code(...)` call",
    ),
    # --- Float64 -> Int -------------------------------------------------
    TrapEmitter(
        "wasm/calls_math.py:_translate_float_to_int", "float_conversion",
        ("float_to_int_domain",), "signal", "the conversion call",
    ),
    TrapEmitter(
        "wasm/calls_math.py:_translate_floor", "float_conversion",
        ("float_to_int_domain",), "signal", "the conversion call",
    ),
    TrapEmitter(
        "wasm/calls_math.py:_translate_ceil", "float_conversion",
        ("float_to_int_domain",), "signal", "the conversion call",
    ),
    TrapEmitter(
        "wasm/calls_math.py:_translate_round", "float_conversion",
        ("float_to_int_domain",), "signal", "the conversion call",
    ),
    # --- contracts ------------------------------------------------------
    TrapEmitter(
        "codegen/contracts.py:_compile_preconditions", "contract_violation",
        ("requires", "call_pre"), "contract", "the `requires(...)` clause",
    ),
    TrapEmitter(
        "codegen/contracts.py:_compile_postconditions", "contract_violation",
        ("ensures",), "contract", "the `ensures(...)` clause",
    ),
    TrapEmitter(
        "codegen/contracts.py:_emit_refinement_check", "contract_violation",
        ("refine_bind",), "contract",
        "the guarded binding's value, or the refined type expression at a "
        "function boundary",
    ),
    TrapEmitter(
        "codegen/contracts.py:_compile_decreases_entry", "contract_violation",
        ("decreases",), "contract", "the `decreases(...)` clause",
    ),
    TrapEmitter(
        "codegen/contracts.py:_dec_self_tail_prefix", "contract_violation",
        ("decreases",), "contract", "the `decreases(...)` clause",
    ),
    TrapEmitter(
        "codegen/contracts.py:_dec_bound_check_pairs", "contract_violation",
        ("decreases_bound",), "contract", "the `decreases(...)` clause",
    ),
    # --- runtime functions: one per module, no source site --------------
    TrapEmitter(
        "codegen/assembly.py:heap_trap", "heap_exhausted", (), "signal",
        "none: renders the trap of `$alloc` (a request of 2 GiB or more, a "
        "refused `memory.grow`, the 2 GiB heap ceiling) and of "
        "`$gc_collect`'s mark-bitmap growth, runtime functions emitted once "
        "per module", per_site=False,
    ),
    TrapEmitter(
        "codegen/wasi.py:_emit_cabi_realloc", "heap_exhausted", (), "signal",
        "none: the WASI host-data arena is a runtime function",
        per_site=False,
    ),
)


# =====================================================================
# The one rendering of a named trap
# =====================================================================

#: The import declaration a module carries when anything in it signals.
TRAP_IMPORT_WAT = (
    f'  (import "vera" "{TRAP_SIGNAL}" '
    f"(func $vera.{TRAP_SIGNAL} (param i32 i32 i32)))"
)


def signal_instructions(
    kind: str, ptr: int = 0, length: int = 0, marker: str = "",
) -> list[str]:
    """The instructions that raise trap *kind*: the signal, then the trap.

    The ONE place code generation writes the ``unreachable`` of a named
    check.  ``contract_violation`` goes through :data:`CONTRACT_SIGNAL` with
    the contract's text; every other kind through :data:`TRAP_SIGNAL` with
    its code and the check's own message (``ptr``/``length`` of an interned
    string, both zero for a kind whose sites carry none).  Callers splice
    the result where the trap belongs — inside the ``if`` that tests the
    check's condition — and raise the import's ``_needs_...`` flag beside
    the splice; ``WasmContext._emit_trap`` does both and records the check,
    passing the record's *marker* (:func:`check_marker`) for the signal's
    ``call`` to carry.
    """
    row = TRAP_KINDS[kind]
    if kind == "contract_violation":
        return [
            f"i32.const {ptr}",
            f"i32.const {length}",
            f"call $vera.{CONTRACT_SIGNAL}{marker}",
            "unreachable",
        ]
    if not row.code:
        raise ValueError(f"trap kind {kind!r} is not raised by a signal")
    return [
        f"i32.const {row.code}",
        f"i32.const {ptr}",
        f"i32.const {length}",
        f"call $vera.{TRAP_SIGNAL}{marker}",
        "unreachable",
    ]


#: While a module is assembled, every recorded check carries this WAT block
#: comment on the instruction that IS the check — a signal's ``call``, a
#: native division — naming the record entry it came from.  The per-module
#: record is read back from the assembled text
#: (``CodeGenerator._assemble_emitted_checks``), which then strips the
#: comments: a check whose instructions were thrown away is not in the text,
#: and one spliced twice is in it twice, so the record holds exactly the
#: checks the module holds, in the function that holds them.  Always found
#: and stripped through :func:`find_check_markers` and
#: :func:`strip_check_markers`, never through this pattern alone.
CHECK_MARKER_RE = re.compile(r" \(;vera-check:(\d+);\)")

#: A marker, or one of the two WAT lexemes that can hold a marker's text
#: without being one: a string literal — a data segment holds the program's
#: strings, printable characters verbatim — and a line comment.  Matched
#: left to right, so each literal and comment is consumed whole and only a
#: marker outside them is seen (it alone sets group 1).
_WAT_MARKER_LEXEMES = re.compile(
    r'"(?:[^"\\]|\\.)*"|;;[^\n]*|' + CHECK_MARKER_RE.pattern)


def check_marker(check_id: int) -> str:
    """The marker of record entry *check_id* (see :data:`CHECK_MARKER_RE`)."""
    return f" (;vera-check:{check_id};)"


def find_check_markers(
    wat: str, start: int = 0, end: int | None = None,
) -> Iterator[re.Match[str]]:
    """Every record marker in ``wat[start:end]`` — none inside a string
    literal or a comment, whatever the program's own text spells.  The
    entry id is ``group(1)``."""
    for match in _WAT_MARKER_LEXEMES.finditer(
            wat, start, len(wat) if end is None else end):
        if match.group(1) is not None:
            yield match


def strip_check_markers(wat: str) -> str:
    """*wat* without its record markers, every string literal and comment
    left exactly as it was."""
    return _WAT_MARKER_LEXEMES.sub(
        lambda match: "" if match.group(1) is not None else match.group(0),
        wat)


def signal_call_pattern(kind: str) -> re.Pattern[str]:
    """A pattern matching the signal :func:`signal_instructions` renders for
    *kind*, whatever its indentation, line breaks or message pointer — the
    way a test or an instrument asks "does this module raise *kind*?"
    without restating the rendering."""
    if kind == "contract_violation":
        return re.compile(
            rf"i32\.const \d+\s+i32\.const \d+\s+call \$vera\.{CONTRACT_SIGNAL}\b")
    code = TRAP_KINDS[kind].code
    if not code:
        raise ValueError(f"trap kind {kind!r} is not raised by a signal")
    return re.compile(
        rf"i32\.const {code}\s+i32\.const \d+\s+i32\.const \d+\s+"
        rf"call \$vera\.{TRAP_SIGNAL}\b")


# =====================================================================
# Every other trap site, by why it is not named
# =====================================================================

@dataclass(frozen=True)
class InternalTrap:
    """An ``unreachable`` code generation emits with no signal before it."""

    site: str
    """``<module under vera/>:<function or table>`` holding the literal."""

    cause: str
    """The :data:`UNREACHABLE_CAUSES` key the generic paragraph names it by."""

    count: int
    """How many such ``unreachable`` literals the site holds for this cause."""

    note: str


#: Every ``unreachable`` that reaches the generic kind.  A new bare
#: ``unreachable`` anywhere in the code-generation package is a failure of
#: the static scan until it is either named through :func:`signal_instructions`
#: or entered here under one of the causes the generic paragraph lists.
INTERNAL_TRAPS: tuple[InternalTrap, ...] = (
    InternalTrap(
        "wasm/helpers.py:gc_shadow_push", "shadow_stack_overflow", 1,
        "the per-push bound on the GC shadow stack",
    ),
    InternalTrap(
        "codegen/assembly.py:_emit_register_wrapper",
        "shadow_stack_overflow", 1,
        "rooting the in-flight wrapper before its slow-path collection",
    ),
    InternalTrap(
        "codegen/wasi.py:_SHADOW_PUSH_FN", "shadow_stack_overflow", 1,
        "the WASI adapter's copy of the shadow-stack push",
    ),
    InternalTrap(
        "codegen/assembly.py:_emit_register_wrapper",
        "wrap_table_overflow", 1,
        "the wrapper table is still full after a collection",
    ),
    InternalTrap(
        "codegen/assembly.py:_emit_gc_collect", "gc_worklist_overflow", 2,
        "the mark worklist's bound, at the root seed and in the drain loop",
    ),
    InternalTrap(
        "codegen/assembly.py:_emit_gc_assert_base", "compiler_bug", 1,
        "the VERA_GC_CHECK_MARKS invariant (a debugging knob)",
    ),
    InternalTrap(
        "codegen/wasi.py:_op_attach_bucket_to_wrapper", "compiler_bug", 1,
        "the server world's bucket-as-truth tripwire (#706)",
    ),
    InternalTrap(
        "wasm/calls.py:_translate_qualified_call", "compiler_bug", 1,
        "after `IO.exit`, which never returns",
    ),
    InternalTrap(
        "codegen/wasi.py:_op_exit", "compiler_bug", 1,
        "after `wasi:cli/exit`, which never returns",
    ),
    InternalTrap(
        "wasm/calls_handlers.py:_translate_handle_exn", "compiler_bug", 1,
        "after a `handle[Exn]` whose body and clause both diverge",
    ),
    InternalTrap(
        "codegen/core.py:_DROPPED_CLOSURE_BODY", "compiler_bug", 1,
        "the body of a closure whose enclosing function was dropped; its "
        "table slot survives and nothing can construct it",
    ),
    InternalTrap(
        "codegen/wasi.py:_emit_cabi_realloc", "compiler_bug", 1,
        "arena exhaustion in a component with no trap import, which "
        "performs no lowering that calls `cabi_realloc`",
    ),
    InternalTrap(
        "codegen/wasi.py:_write_or_trap", "wasi_io_failure", 1,
        "a failed blocking write to a standard stream",
    ),
    InternalTrap(
        "codegen/wasi.py:_read_byte", "wasi_io_failure", 1,
        "a failed read from stdin",
    ),
    InternalTrap(
        "codegen/wasi.py:_serve_handle", "wasi_io_failure", 7,
        "the server world's request / response stream failures",
    ),
)

#: The ``unreachable`` literals that ARE a signal: the WASI adapter's
#: implementations of the two imports, which trap after writing the
#: message.  Named, so they neither need a roster cause nor reach the
#: generic kind.
SIGNAL_SITES: tuple[tuple[str, int], ...] = (
    ("codegen/wasi.py:_op_contract_fail", 1),
    ("codegen/wasi.py:_op_trap", 2),
)


@dataclass(frozen=True)
class NativeSite:
    """A WASM instruction that traps by itself, at one site."""

    site: str
    instruction: str
    count: int
    reason: str
    """Why it cannot trap (a safe site), or which kind it traps as."""

    kind: str | None = None
    """The trap kind a user-reachable native trap reports; None for a site
    that cannot trap."""

    emitter: str | None = None
    """The :data:`TRAP_EMITTERS` key that emits (and records) a
    user-reachable native trap; None for a safe site."""


#: Natively trapping instructions a user program reaches.  Each is named by
#: the host's own trap message rather than by a signal, and recorded as a
#: check by its emitter.
NATIVE_TRAP_SITES: tuple[NativeSite, ...] = (
    NativeSite(
        "wasm/inference.py:_ARITH_OPS", "i64.div_s", 1,
        "`/` over @Int / @Nat: a zero divisor traps as divide_by_zero, "
        "and `INT_MIN / -1` as overflow",
        kind="divide_by_zero", emitter="wasm/operators.py:_translate_binary",
    ),
    NativeSite(
        "wasm/inference.py:_ARITH_OPS", "i64.rem_s", 1,
        "`%` over @Int / @Nat: a zero divisor traps as divide_by_zero",
        kind="divide_by_zero", emitter="wasm/operators.py:_translate_binary",
    ),
)

#: Natively trapping instructions that cannot trap where they are emitted.
SAFE_NATIVE_SITES: tuple[NativeSite, ...] = (
    NativeSite(
        "wasm/operators.py:_ARITH_OPS_I32_BYTE", "i32.div_u", 1,
        "`@Byte` is not a numeric type (`vera.types.NUMERIC_TYPES`), so the "
        "checker refuses `/` on it and no user division lowers here",
    ),
    NativeSite(
        "wasm/operators.py:_ARITH_OPS_I32_BYTE", "i32.rem_u", 1,
        "`@Byte` is not a numeric type, so the checker refuses `%` on it",
    ),
    NativeSite(
        "wasm/operators.py:_emit_int_mul_guard", "i64.div_s", 1,
        "reached only when the left operand is neither 0 nor -1",
    ),
    NativeSite(
        "wasm/operators.py:_emit_nat_mul_guard", "i64.div_u", 1,
        "reached only when the left operand is not 0",
    ),
    NativeSite(
        "wasm/calls_encoding.py:_translate_base64_encode", "i32.div_u", 1,
        "divides by the constant 3",
    ),
    NativeSite(
        "wasm/calls_encoding.py:_translate_base64_encode", "i32.rem_u", 1,
        "divides by the constant 3",
    ),
    NativeSite(
        "wasm/calls_strings.py:_translate_string_repeat", "i32.rem_u", 1,
        "the copy loop runs while the index is below length * count, which "
        "is zero when the length is",
    ),
    NativeSite(
        "wasm/calls_strings.py:_translate_pad", "i32.rem_u", 2,
        "the fill loop runs only for a non-empty fill string",
    ),
    NativeSite(
        "wasm/calls_strings.py:_to_string_core", "i64.rem_u", 1,
        "divides by the constant 10",
    ),
    NativeSite(
        "wasm/calls_strings.py:_to_string_core", "i64.div_u", 1,
        "divides by the constant 10",
    ),
    NativeSite(
        "wasm/calls_strings.py:_float_to_string_core", "i64.rem_u", 2,
        "divides by the constant 10",
    ),
    NativeSite(
        "wasm/calls_strings.py:_float_to_string_core", "i64.div_u", 2,
        "divides by the constant 10",
    ),
    NativeSite(
        "wasm/calls_strings.py:_float_to_string_core", "i64.trunc_f64_s", 1,
        "the fractional part scaled by 10^6 lies in [0, 10^6]",
    ),
    NativeSite(
        "wasm/calls_math.py:_trunc_after_domain_check", "i64.trunc_f64_s", 1,
        "preceded by the [-2^63, 2^63) domain check whose failure its "
        "caller signals as float_conversion",
    ),
    NativeSite(
        "codegen/wasi.py:_op_time", "i64.div_u", 1,
        "divides by the constant 10^6",
    ),
    NativeSite(
        "codegen/wasi.py:_op_random_int", "i64.rem_u", 2,
        "a zero range (the full 2^64 span) returns before either remainder",
    ),
)

#: Natively trapping instructions a user program reaches that trap where
#: the language says they must not.  Each names the issue that tracks it;
#: an entry here is a known defect, not a design.
KNOWN_TRAP_DEFECTS: tuple[NativeSite, ...] = (
    NativeSite(
        "wasm/calls_strings.py:_float_to_string_core", "i64.trunc_f64_s", 1,
        "#1482: the integer part of a finite value of magnitude 2^63 or "
        "more does not fit the i64 the digit loop runs over, so the total "
        "`float_to_string` traps, as float_conversion",
        kind="float_conversion",
    ),
)

#: The WASM instructions that trap by themselves on an operand, which the
#: static scan looks for.  Memory accesses, `call_indirect` and `throw`
#: trap only on a compiler or runtime bug and are out of its scope.
NATIVE_TRAPPING_INSTRUCTIONS: frozenset[str] = frozenset({
    "i32.div_s", "i32.div_u", "i32.rem_s", "i32.rem_u",
    "i64.div_s", "i64.div_u", "i64.rem_s", "i64.rem_u",
    "i32.trunc_f32_s", "i32.trunc_f32_u", "i32.trunc_f64_s",
    "i32.trunc_f64_u", "i64.trunc_f32_s", "i64.trunc_f32_u",
    "i64.trunc_f64_s", "i64.trunc_f64_u",
})


# =====================================================================
# How each host names a native trap
# =====================================================================

#: wasmtime's trap reason, as a lower-cased substring, to the kind it is —
#: first match wins (wasmtime and the WASI 0.2 host).  "integer overflow" is
#: also what wasmtime says for a truncation past its range or of an
#: infinity, so a host that can read the trapping instruction consults it
#: first (:func:`native_trap_kind`).
WASMTIME_NATIVE_TRAPS: tuple[tuple[str, str], ...] = (
    ("integer divide by zero", "divide_by_zero"),
    ("invalid conversion to integer", "float_conversion"),
    ("out of bounds memory access", "out_of_bounds"),
    ("call stack exhausted", "stack_exhausted"),
    ("unreachable", "unreachable"),
    ("integer overflow", "overflow"),
)

#: V8's ``WebAssembly.RuntimeError`` message to the kind it is (the browser
#: runtime).  A ``RangeError`` from call-stack exhaustion is
#: ``stack_exhausted`` there, whatever its message.  V8 gives every
#: truncation trap its own message, so it needs no instruction.
BROWSER_NATIVE_TRAPS: tuple[tuple[str, str], ...] = (
    ("divide by zero", "divide_by_zero"),
    ("remainder by zero", "divide_by_zero"),
    ("divide result unrepresentable", "overflow"),
    ("float unrepresentable in integer range", "float_conversion"),
    ("memory access out of bounds", "out_of_bounds"),
    ("unreachable", "unreachable"),
)

#: The opcode of every natively trapping instruction (WebAssembly core
#: specification, binary format, numeric instructions), so a host that
#: reports WHERE a trap happened can say which instruction it was: wasmtime
#: gives the trapping frame's offset into the module (core runtime) or the
#: component binary (WASI 0.2 host).
NATIVE_TRAP_OPCODES: dict[int, str] = {
    0x6D: "i32.div_s", 0x6E: "i32.div_u", 0x6F: "i32.rem_s", 0x70: "i32.rem_u",
    0x7F: "i64.div_s", 0x80: "i64.div_u", 0x81: "i64.rem_s", 0x82: "i64.rem_u",
    0xA8: "i32.trunc_f32_s", 0xA9: "i32.trunc_f32_u",
    0xAA: "i32.trunc_f64_s", 0xAB: "i32.trunc_f64_u",
    0xAE: "i64.trunc_f32_s", 0xAF: "i64.trunc_f32_u",
    0xB0: "i64.trunc_f64_s", 0xB1: "i64.trunc_f64_u",
}


def native_trap_kind(
    reason: str,
    instruction: str | None,
    table: tuple[tuple[str, str], ...],
) -> str | None:
    """The kind of a trap the WASM engine raised itself, from its *reason*
    (lower-cased, matched against *table*, first match wins) and — where the
    host can report it — the *instruction* that trapped.

    A float-to-integer truncation traps only on a value it cannot convert:
    NaN, an infinity, or a finite value past its target range.  That is a
    ``float_conversion`` whatever the engine calls it, and wasmtime calls the
    last two "integer overflow", the reason it also gives ``INT_MIN / -1``;
    the instruction is what tells them apart.  ``None`` for a reason no row
    matches.
    """
    if instruction is not None and ".trunc_" in instruction:
        return "float_conversion"
    for needle, kind in table:
        if needle in reason:
            return kind
    return None


@dataclass(frozen=True)
class NativeTrapCondition:
    """One way a natively trapping instruction traps by itself."""

    instruction: str
    condition: str
    """What makes it trap, in words."""

    operands: tuple[str, ...]
    """WAT instructions that push operands making it trap that way."""

    kind: str
    """The trap kind that is."""


_NATIVE_SHAPE = re.compile(r"^(i32|i64)\.(div|rem|trunc)_(?:(f32|f64)_)?([su])$")


def native_trap_conditions(instruction: str) -> tuple[NativeTrapCondition, ...]:
    """Every way *instruction* traps by itself, derived from its name under
    WebAssembly's semantics: integer division and remainder trap on a zero
    divisor, signed division also on the one quotient that overflows
    (``INT_MIN / -1``), and a truncation on NaN, on an infinity and on a
    finite value past its target range.  Raises for an instruction outside
    those families, so a trapping instruction nothing here can derive is a
    failure rather than a silent gap."""
    shape = _NATIVE_SHAPE.match(instruction)
    if shape is None:
        raise ValueError(f"no trap conditions known for {instruction!r}")
    result, op, source, sign = shape.groups()
    bits = 32 if result == "i32" else 64

    def cond(what: str, operands: tuple[str, ...], kind: str,
             ) -> NativeTrapCondition:
        return NativeTrapCondition(instruction, what, operands, kind)

    if op in ("div", "rem"):
        out = [cond("a zero divisor",
                    (f"{result}.const 1", f"{result}.const 0"),
                    "divide_by_zero")]
        if op == "div" and sign == "s":
            out.append(cond("the one quotient that overflows",
                            (f"{result}.const {-(2 ** (bits - 1))}",
                             f"{result}.const -1"), "overflow"))
        return tuple(out)
    past = 2 ** (bits - 1) if sign == "s" else 2 ** bits
    return (
        cond("NaN", (f"{source}.const nan",), "float_conversion"),
        cond("an infinity", (f"{source}.const inf",), "float_conversion"),
        cond("a finite value past its range", (f"{source}.const {past}",),
             "float_conversion"),
    )


def browser_trap_table() -> dict[str, object]:
    """The browser runtime's copy of the kind table, as JSON-ready data.

    ``vera/browser/runtime.mjs`` carries this between its generated-table
    markers; ``tests/test_named_traps_1479.py`` regenerates it and requires
    the file to hold exactly this, so the browser cannot name a trap
    differently from wasmtime and the WASI host.
    """
    return {
        "kinds": {
            name: {
                "code": kind.code,
                "description": kind.description,
                "fix": kind.fix,
                "siteMessage": kind.site_message,
            }
            for name, kind in sorted(TRAP_KINDS.items())
        },
        "native": [list(pair) for pair in BROWSER_NATIVE_TRAPS],
    }


def _validate() -> None:
    """Import-time consistency of the tables above."""
    if set(NATIVE_TRAP_OPCODES.values()) != NATIVE_TRAPPING_INSTRUCTIONS:
        raise ValueError(
            "NATIVE_TRAP_OPCODES and NATIVE_TRAPPING_INSTRUCTIONS disagree")
    for instruction in NATIVE_TRAPPING_INSTRUCTIONS:
        native_trap_conditions(instruction)
    cause_keys = {cause.key for cause in UNREACHABLE_CAUSES}
    for entry in INTERNAL_TRAPS:
        if entry.cause not in cause_keys:
            raise ValueError(
                f"{entry.site}: cause {entry.cause!r} is not one the generic "
                "unreachable paragraph names")
    for site in (*NATIVE_TRAP_SITES, *KNOWN_TRAP_DEFECTS):
        if site.kind not in TRAP_KINDS:
            raise ValueError(f"{site.site}: unknown trap kind {site.kind!r}")
    for site in NATIVE_TRAP_SITES:
        if site.emitter not in TRAP_EMITTERS:
            raise ValueError(f"{site.site}: unknown emitter {site.emitter!r}")


_validate()


# =====================================================================
# The per-module record
# =====================================================================

@dataclass(frozen=True)
class EmittedCheck:
    """One check a compiled module contains (``CompileResult.emitted_checks``).

    Entered by the emitter as it emits the check, whose instruction carries
    the entry's marker (:data:`CHECK_MARKER_RE`); listed once for every copy
    of the marker the assembled module holds, under the function holding it
    — so a check that never reaches the module is not listed, and one
    spliced twice is listed twice.  A generic body monomorphised N times
    contributes N entries sharing one span, one per clone; the ``function``
    field tells them apart.
    """

    emitter: str
    """The :data:`TRAP_EMITTERS` key of the function that emitted it."""

    kind: str
    """The trap kind a failing check reports (from the emitter's row)."""

    obligations: tuple[str, ...]
    """The verifier obligation kinds it is the runtime half of (from the
    emitter's row)."""

    function: str
    """The emitted WASM function it sits in: a declaration's symbol, a
    monomorphised clone's (``f$Int``), or a lifted closure's
    (``anon_3``)."""

    line: int
    """1-based line of the span start, or 0 when the emitter was handed no
    node (see :attr:`TrapEmitter.span`)."""

    column: int
    end_line: int
    end_column: int

    file: str | None
    """The source file the span lines in: the declaring module's for an
    imported body, the entry file's otherwise.  None inside a prelude or
    built-in function, whose spans point into synthetic source."""

    prelude: bool
    """Whether the check sits inside a prelude / built-in function the user
    did not write."""

    def to_dict(self) -> dict[str, object]:
        """A JSON-compatible form (field names as keys)."""
        return {
            "emitter": self.emitter,
            "kind": self.kind,
            "obligations": list(self.obligations),
            "function": self.function,
            "line": self.line,
            "column": self.column,
            "end_line": self.end_line,
            "end_column": self.end_column,
            "file": self.file,
            "prelude": self.prelude,
        }
