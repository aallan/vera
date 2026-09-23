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
        "Most often caused by `Array<T>[i]` with `i` outside `[0, "
        "array_length(arr))` or by `string_slice(s, start, end)` with "
        "out-of-range indices.  Add a `requires(i < "
        "array_length(arr))` precondition or guard the access "
        "explicitly.  If the trapping frame is `gc_collect`, "
        "`alloc`, or another runtime helper this is a compiler bug "
        "rather than a user error — please file a minimal reproducer "
        "at https://github.com/aallan/vera/issues/new.",
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
        "Three causes reach this trap.  (1) A non-exhaustive `match` "
        "whose missing arm would have required user code — add the "
        "missing arm explicitly rather than relying on a wildcard; the "
        "type checker will tell you which constructors are uncovered.  "
        "(2) A compiler-generated assertion, e.g. an ADT field offset "
        "that didn't resolve.  (3) GC shadow-stack overflow, which is "
        "what a DEEP RECURSION through a function holding heap "
        "references hits: every live frame roots its pointer "
        "parameters, its allocations, and the values it binds out of "
        "them, and the shadow stack holds 4 096 roots in total (16 KiB "
        "— `GC_STACK_SIZE` in `vera/codegen/assembly.py`).  A recursion "
        "that traps at a depth close to 4 096 divided by a small "
        "integer is this one: reduce the heap values live across the "
        "recursive call, or restructure so the call is in tail position "
        "(#549 GC-aware TCO restores `$gc_sp` at each hop, so the chain "
        "runs in constant shadow space).",
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
        "codegen/assembly.py:_emit_alloc", "heap_exhausted", (), "signal",
        "none: the allocator is a runtime function", per_site=False,
    ),
    TrapEmitter(
        "codegen/assembly.py:_emit_gc_collect", "heap_exhausted", (),
        "signal", "none: the collector is a runtime function",
        per_site=False,
    ),
    TrapEmitter(
        "codegen/wasi.py:_emit_cabi_realloc", "heap_exhausted", (), "signal",
        "none: the WASI host-data arena is a runtime function",
        per_site=False,
    ),
)


# =====================================================================
# The per-module record
# =====================================================================

@dataclass(frozen=True)
class EmittedCheck:
    """One check a compiled module contains (``CompileResult.emitted_checks``).

    Recorded by the emitter at the moment it emits the check, and kept only
    if the function it was emitted into survives into the module — a
    function dropped after compiling (``[E620]``) takes its checks with it.
    A generic body monomorphised N times contributes N entries sharing one
    span, one per clone; the ``function`` field tells them apart.
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
