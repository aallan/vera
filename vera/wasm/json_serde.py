"""WASM memory marshalling for Json ADT.

Provides bidirectional conversion between Python JSON values
(dict, list, str, float, bool, None) and the WASM Json ADT
memory representation.  Used by host function bindings in
vera.codegen.api.

Write direction (Python → WASM):
  write_json(caller, alloc, write_i32, write_f64, alloc_string,
             map_alloc, value) → int (heap pointer)

Read direction (WASM → Python):
  read_json(caller, ptr, read_i32, read_f64, read_string,
            decode_jobject) → Any

Text direction (Python → JSON text):
  dumps_canonical(value) → str
  format_json_number(value) → str

Accept domain (spec §9.7.1, #1306 / #1308):
  first_domain_violation(value) → str | None
  non_finite_parse_message(name) → str
  non_finite_number_message(name) → str
  lone_surrogate_message(code_point) → str

The domain gates sit in front of the write direction rather than inside
it: `vera/runtime/json.py` consults them on the value `json.loads`
returned, before `write_json` marshals anything, and
`vera/browser/runtime.mjs` carries the twin of each.  See the section
comment below for what the domain is and why it is stated rather than
inherited.

The text direction is the last mile of the read direction and lives here
for that reason: ``json_stringify`` is ``read_json`` followed by
``dumps_canonical``.  Its output form is canonical and shared with the
browser runtime — see the section comment above ``format_json_number``.

Json ADT layouts (from prelude injection → registration.py):
  JNull                        tag=0  ()               total=8
  JBool(Bool)                  tag=1  (4, i32)         total=8
  JNumber(Float64)             tag=2  (8, f64)         total=16
  JString(String)              tag=3  (4, i32_pair)    total=16
  JArray(Array<Json>)          tag=4  (4, i32_pair)    total=16
  JObject(Map<String, Json>)   tag=5  (4, i32)         total=8
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import wasmtime

# Type aliases for host function callbacks
AllocFn = Callable[[wasmtime.Caller, int], int]
WriteI32Fn = Callable[[wasmtime.Caller, int, int], None]
WriteF64Fn = Callable[[wasmtime.Caller, int, float], None]
AllocStringFn = Callable[[wasmtime.Caller, str], tuple[int, int]]
# #706: map_alloc is ``_alloc_map_wrapper`` — it encodes the Python
# dict into a fresh bucket-as-truth wrapper and returns the wrapper
# pointer (no host store, no wrap-table registration).  It accepts
# ``caller`` so it can call the exported ``$rt.alloc`` to build the
# wrapper + bucket in WASM memory.
MapAllocFn = Callable[[wasmtime.Caller, dict[object, object]], int]
ReadI32Fn = Callable[[wasmtime.Caller, int], int]
ReadF64Fn = Callable[[wasmtime.Caller, int], float]
ReadStringFn = Callable[[wasmtime.Caller, int, int], str]

# Tag constants matching prelude ADT declaration order
_TAG_JNULL = 0
_TAG_JBOOL = 1
_TAG_JNUMBER = 2
_TAG_JSTRING = 3
_TAG_JARRAY = 4
_TAG_JOBJECT = 5

# The three non-finite doubles under the names JavaScript spells them with.
# BOTH sections below read it — the accept domain to name the value it is
# refusing, canonical serialization to name the one it cannot render — so it
# sits above them rather than inside either: a private constant in one section
# consulted from the other is a dependency invisible to a reader working on
# that half, and the accept domain is separately hand-mirrored into
# ``vera/browser/runtime.mjs``.  Keyed on ``repr`` deliberately: a NaN is not
# equal to itself, so a dict keyed on the float VALUE cannot retrieve it.
_NON_FINITE_NAMES = {"nan": "NaN", "inf": "Infinity", "-inf": "-Infinity"}


# ---------------------------------------------------------------------------
# json_parse's accept domain (spec §9.7.1)
# ---------------------------------------------------------------------------
#
# ``json_parse`` accepts exactly RFC 8259-valid text that decodes to
# finite numbers and strings of Unicode scalar values; everything else
# is a handled ``Err``,
# identically on both hosts, at the parse.  The domain is Vera's own — it
# is not inherited from whichever parser a host happens to call, which is
# why each of the two exclusions below needs an explicit gate on at least
# one side:
#
#   * the JavaScript constants ``NaN`` / ``Infinity`` / ``-Infinity``,
#     which RFC 8259 has no literals for.  Python's ``json.loads`` admits
#     them through ``parse_constant``; ``JSON.parse`` refuses them
#     (#1306).
#   * a lone surrogate, which is not a Unicode scalar value and has no
#     UTF-8 encoding, so no Vera string can hold one.  Both host parsers
#     decode the escape happily and the refusal used to fall out of the
#     memory boundary — as a crash on one host and a silent U+FFFD
#     substitution on the other (#1308).
#
# Each refusal has ONE sentence, built here and hand-copied into
# ``vera/browser/runtime.mjs``; ``tests/test_browser.py`` holds the copy
# against this original so the two hosts cannot drift into saying
# different things about the same input.


def non_finite_parse_message(name: str) -> str:
    """The single sentence both runtimes return for a bare ``NaN``.

    ``name`` is the constant as it appears in the text — ``"NaN"``,
    ``"Infinity"`` or ``"-Infinity"`` — which is what Python's
    ``parse_constant`` hook is handed and what the browser's twin scan
    finds.
    """
    return (
        f"json_parse: {name} is not valid JSON — RFC 8259 has no NaN or "
        f"Infinity.  json_parse accepts RFC 8259 text only, not the "
        f"JavaScript constants: quote the value as a string, or write null."
    )


def lone_surrogate_message(code_point: int) -> str:
    """The single sentence both runtimes return for a lone surrogate.

    The code point is rendered in the canonical ``\\uXXXX`` escape form
    with uppercase hex, so the message does not depend on how the input
    spelled its escape.
    """
    return (
        f"json_parse: \\u{code_point:04X} decodes to a lone surrogate, which "
        f"is not a Unicode scalar value — a Vera string is a sequence of "
        f"scalar values, so this text has no representable decoding.  Write "
        f"the character as a matched high-then-low surrogate escape pair, or "
        f"remove the escape."
    )


def _first_lone_surrogate_in_str(text: str) -> int | None:
    """The first surrogate code point in ``text``, or ``None``.

    Every surrogate reaching this function is lone: ``json.loads``
    combines a well-formed ``\\uD83D\\uDE00`` escape pair into the single
    astral code point it denotes, so anything left in D800–DFFF failed to
    pair during decoding.  A plain range test is therefore complete here.

    The browser's twin cannot be this simple.  JS strings are UTF-16, so
    a paired astral character is still *stored* as two surrogate code
    units and the scan there has to consume pairs before judging what is
    lone — same rule ("no code point outside the scalar values"), applied
    to a different representation of the decoded value.
    """
    for ch in text:
        code_point = ord(ch)
        if 0xD800 <= code_point <= 0xDFFF:
            return code_point
    return None


def non_finite_number_message(name: str) -> str:
    """The single sentence both runtimes return for an overflowing number.

    The sibling of :func:`non_finite_parse_message`: the same exclusion
    — no accepted text decodes to a non-finite number — reached by a
    different syntax.  ``1e999`` breaks no RFC 8259 rule, so this one
    cites the permission the refusal rests on rather than a prohibition.
    """
    return (
        f"json_parse: a number in the text overflows to {name}, which JSON "
        f"cannot represent — RFC 8259 §6 lets an implementation set limits "
        f"on the range of numbers it accepts, and Vera's accepted range is "
        f"the finite Float64 values.  Keep the magnitude at or below "
        f"1.7976931348623157e308, or carry the value as a string."
    )


# The smallest magnitude whose nearest double is an infinity.
#
# ``json.loads`` returns a Python ``int`` for a digit string with no
# fraction and no exponent, and an ``int`` of any size is finite — but it
# still has to become an f64 at the WASM boundary, where ``float()``
# raises rather than saturating.  So the integer arm needs its own range
# check, and the check has to be pure integer arithmetic: implementing it
# as ``float(value)`` would BE the overflow it is looking for.
#
# The bound is the double ROUNDING boundary, not ``sys.float_info.max``.
# The largest finite double is ``2**1024 - 2**971``; the next value the
# format could name is ``2**1024``; the midpoint between them is
# ``2**1024 - 2**970``, and ties-to-even sends that midpoint upward to
# the infinity.  Everything strictly below rounds DOWN to the largest
# finite double and is perfectly representable — including integers
# larger than ``sys.float_info.max`` itself, which ``JSON.parse`` accepts
# and a bound of ``int(sys.float_info.max)`` would wrongly refuse here
# alone.  ``TestIntegerOverflowRefusal1306`` pins the derivation against
# ``float()`` as its oracle, and the band between the two candidate
# bounds as a control.
_INT_ROUNDS_TO_INFINITY = 2**1024 - 2**970


def first_domain_violation(value: Any) -> str | None:
    """The ``Err`` message for the first out-of-domain value, or ``None``.

    One walk over the decoded tree for both value-level exclusions of
    spec §9.7.1 — a string holding a lone surrogate, and a number that
    is not finite.  Both are properties of the decoded VALUE rather than
    of the text, so both are found here rather than at the parse gate,
    and finding them in one traversal is what makes "whichever comes
    first names the refusal" the rule, instead of a precedence table the
    two hosts could implement differently.

    Document order means, for an object, each key before its own value.
    Keys are checked as well as values: a key crosses the WASM boundary
    as a string exactly like a value does, and the key position is the
    one #1308's own reproduction used.

    Returning the sentence rather than the offending code point or float
    keeps the violation-to-message mapping in one place — a caller
    cannot pair a found violation with the wrong message — and gives the
    browser's twin the same kind of thing to return.

    Non-finite numbers reach the domain two ways.  ``1e999`` is a
    syntactically valid RFC 8259 number that overflows on decoding, and
    is caught here.  The bare constants ``NaN`` / ``Infinity`` are
    refused earlier, at the parse gate, because there the *text* is not
    RFC 8259 and each host's own parser decides that.  One exclusion,
    two entry routes, two sentences — the one that fires says which
    route the text took.

    Both ``float`` and ``int`` are range-checked, and the ``int`` arm is
    not redundant.  ``json.loads`` yields an ``int`` for a digit string
    with no fraction and no exponent, and it is true that a Python
    ``int`` cannot be infinite however many digits it has — but that is
    not the question.  The value must still become an f64 at the WASM
    boundary, and ``float()`` raises there for a magnitude past the
    rounding boundary, so an int-shaped ``1`` followed by 309 zeros
    reached ``write_json`` and killed the host where the browser — which
    has no int/float split and sees an ``Infinity`` either way — had
    returned the shared sentence all along.  ``bool`` subclasses ``int``
    and is excluded explicitly: a JSON boolean is not a number.
    """
    if isinstance(value, str):
        code_point = _first_lone_surrogate_in_str(value)
        if code_point is None:
            return None
        return lone_surrogate_message(code_point)
    if isinstance(value, float):
        if value != value or value in (float("inf"), float("-inf")):
            return non_finite_number_message(_NON_FINITE_NAMES[repr(value)])
        return None
    if isinstance(value, int) and not isinstance(value, bool):
        # ``bool`` subclasses ``int``; a boolean is a JSON boolean and
        # is never range-checked.  The comparisons below stay in integer
        # arithmetic all the way down, so a 400-digit literal is refused
        # rather than raising on its way to being measured.
        if value >= _INT_ROUNDS_TO_INFINITY:
            return non_finite_number_message("Infinity")
        if value <= -_INT_ROUNDS_TO_INFINITY:
            return non_finite_number_message("-Infinity")
        return None
    if isinstance(value, list):
        for item in value:
            found = first_domain_violation(item)
            if found is not None:
                return found
        return None
    if isinstance(value, dict):
        for key, item in value.items():
            if isinstance(key, str):
                code_point = _first_lone_surrogate_in_str(key)
                if code_point is not None:
                    return lone_surrogate_message(code_point)
            found = first_domain_violation(item)
            if found is not None:
                return found
        return None
    return None


def write_json(
    caller: wasmtime.Caller,
    alloc: AllocFn,
    write_i32: WriteI32Fn,
    write_f64: WriteF64Fn,
    alloc_string: AllocStringFn,
    map_alloc: MapAllocFn,
    guard: Any,
    value: Any,
) -> int:
    """Write a Python JSON value to WASM memory as a Json ADT.

    Returns the heap pointer to the allocated Json node.

    *guard* is a ``_ShadowGuard`` (defined in
    ``vera.codegen.api``).  Intermediate WASM heap pointers
    (string body, array backing, map wrapper) are pushed onto
    its shadow-stack window before any subsequent alloc that
    could trigger ``$rt.gc_collect``.  See #692 + the analogous
    notes in ``html_serde.write_html`` for the bug class.

    The returned root pointer is NOT pushed — the caller is
    responsible for rooting it before the next alloc.
    """
    if value is None:
        # JNull — tag=0, total=8.  Single alloc, no cross-pointer
        # holding, no rooting needed.
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, _TAG_JNULL)
        return ptr

    if isinstance(value, bool):
        # JBool(Bool) — tag=1, i32 at offset 4, total=8.  Single
        # alloc, no rooting needed.
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, _TAG_JBOOL)
        write_i32(caller, ptr + 4, 1 if value else 0)
        return ptr

    if isinstance(value, (int, float)):
        # JNumber(Float64) — tag=2, f64 at offset 8, total=16.
        # Single alloc, no rooting needed.
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_JNUMBER)
        write_f64(caller, ptr + 8, float(value))
        return ptr

    if isinstance(value, str):
        # JString(String) — tag=3, i32_pair at offset 4, total=16.
        # Allocate the string FIRST and root it before the body
        # alloc; the original order (body alloc then string alloc)
        # could trigger GC mid-construction while the body is in
        # a Python local with only the tag written.
        s_ptr, s_len = alloc_string(caller, value)
        if s_ptr != 0:
            guard.push(s_ptr)
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_JSTRING)
        write_i32(caller, ptr + 4, s_ptr)
        write_i32(caller, ptr + 8, s_len)
        return ptr

    if isinstance(value, list):
        # JArray(Array<Json>) — tag=4, i32_pair at offset 4,
        # total=16.  Root arr_ptr before recursing into children
        # (each sub-write may trigger GC) and across the final
        # body alloc.  Child pointers become reachable via the
        # rooted arr_ptr's slots as soon as we ``write_i32`` them.
        count = len(value)
        if count > 0:
            arr_ptr = alloc(caller, count * 4)
            guard.push(arr_ptr)
            for i, elem in enumerate(value):
                elem_ptr = write_json(
                    caller, alloc, write_i32, write_f64,
                    alloc_string, map_alloc, guard, elem,
                )
                write_i32(caller, arr_ptr + i * 4, elem_ptr)
        else:
            arr_ptr = 0
        ptr = alloc(caller, 16)
        write_i32(caller, ptr, _TAG_JARRAY)
        write_i32(caller, ptr + 4, arr_ptr)
        write_i32(caller, ptr + 8, count)
        return ptr

    if isinstance(value, dict):
        # JObject(Map<String, Json>) — tag=5, i32 at offset 4, total=8
        # Build a Map<String, Json> as a bucket-as-truth wrapper (#706).
        # Keys are stored as Python strings (matching map_contains$ks
        # which reads WASM strings and compares against Python strings).
        # Values are i32 Json heap pointers.
        #
        # #706: ``map_alloc`` is ``_alloc_map_wrapper`` (in
        # ``vera/codegen/api.py``), which encodes this Python dict
        # into a fresh bucket-as-truth wrapper + bucket and returns
        # the wrapper pointer.  That makes the JObject's i32 field
        # type-compatible with user-level ``map_get`` /
        # ``map_contains`` calls, which take the wrapper pointer
        # directly.  The JObject's Map is reclaimed by ordinary
        # mark-sweep when the wrapper becomes unreachable — there is
        # no host store to evict.
        #
        # #692: each iteration's val_ptr is pushed onto the
        # shadow stack BEFORE the next iteration's recursive
        # ``write_json`` (which may GC).  Without this, the
        # Python dict (``map_dict``) holds val_ptrs as ints that
        # the conservative scan can't see; the WASM blocks they
        # point to would be freed by the very next sub-alloc.
        #
        # Exception-safety note: if a recursive ``write_json``
        # raises mid-loop, the outer ``__exit__`` resets
        # ``$gc_sp`` and pops every prior ``val_ptr`` push.
        # ``map_dict`` still holds those ints as plain Python
        # values when the exception unwinds — but that's safe:
        # the function exits via the raise BEFORE the
        # ``map_alloc(caller, map_dict)`` call below, so the
        # stale ints never reach WASM.  A future maintainer
        # should NOT try to recover ``map_dict`` partial state
        # — the val_ptrs are guaranteed-invalid after the
        # guard exit.
        map_dict: dict[object, object] = {}
        for k, v in value.items():
            val_ptr = write_json(
                caller, alloc, write_i32, write_f64,
                alloc_string, map_alloc, guard, v,
            )
            guard.push(val_ptr)
            map_dict[str(k)] = val_ptr
        wrapper_ptr = map_alloc(caller, map_dict)
        guard.push(wrapper_ptr)
        ptr = alloc(caller, 8)
        write_i32(caller, ptr, _TAG_JOBJECT)
        write_i32(caller, ptr + 4, wrapper_ptr)
        return ptr

    # Fallback: treat as string
    return write_json(
        caller, alloc, write_i32, write_f64,
        alloc_string, map_alloc, guard, str(value),
    )


def read_json(
    caller: wasmtime.Caller,
    ptr: int,
    read_i32: ReadI32Fn,
    read_f64: ReadF64Fn,
    read_string: ReadStringFn,
    decode_jobject: "Callable[[wasmtime.Caller, int], dict[Any, Any]]",
) -> Any:
    """Read a Json ADT from WASM memory back to a Python value.

    Returns: None, bool, float, str, list, or dict.

    #706: ``decode_jobject(caller, wrapper_ptr)`` decodes a JObject's
    ``Map<String, Json>`` from its bucket-as-truth wrapper (there is no
    ``_map_store`` to look up by handle anymore).
    """
    tag = read_i32(caller, ptr)

    if tag == _TAG_JNULL:
        return None

    if tag == _TAG_JBOOL:
        return read_i32(caller, ptr + 4) != 0

    if tag == _TAG_JNUMBER:
        return read_f64(caller, ptr + 8)

    if tag == _TAG_JSTRING:
        s_ptr = read_i32(caller, ptr + 4)
        s_len = read_i32(caller, ptr + 8)
        return read_string(caller, s_ptr, s_len)

    if tag == _TAG_JARRAY:
        arr_ptr = read_i32(caller, ptr + 4)
        arr_len = read_i32(caller, ptr + 8)
        items: list[Any] = []
        for i in range(arr_len):
            elem_ptr = read_i32(caller, arr_ptr + i * 4)
            items.append(read_json(
                caller, elem_ptr, read_i32, read_f64,
                read_string, decode_jobject,
            ))
        return items

    if tag == _TAG_JOBJECT:
        # #706: JObject's i32 field at offset 4 is a Map wrapper
        # pointer whose bucket IS the map (bucket-as-truth).  Decode
        # the ``Map<String, Json>`` directly from the bucket — the
        # values are i32 Json heap pointers.
        wrapper_ptr = read_i32(caller, ptr + 4)
        raw_map = decode_jobject(caller, wrapper_ptr)
        obj: dict[str, Any] = {}
        for k, v in raw_map.items():
            obj[str(k)] = read_json(
                caller, int(v), read_i32, read_f64,
                read_string, decode_jobject,
            )
        return obj

    import warnings
    warnings.warn(
        f"read_json: unknown tag {tag} at pointer {ptr}; "
        "possible memory corruption or unsupported Json layout",
        RuntimeWarning,
        stacklevel=2,
    )
    return None  # Unknown tag — should not happen


# =====================================================================
# Canonical serialization (#1293)
# =====================================================================
#
# ``json_stringify`` has exactly one output form, stated in spec §9.7.1
# and produced identically by both runtimes (§12.9.3).  It is the
# compact form: ``,`` and ``:`` with no padding, and numbers rendered by
# ECMAScript's Number::toString.
#
# The reference host used to reach for ``json.dumps``, which cannot
# produce that form: its separators are configurable but its float
# rendering is ``repr``, hard-wired inside ``json.encoder``.  ``repr``
# and Number::toString disagree on four independent boundaries — the
# fractional part of an integral value, the threshold for switching to
# exponential notation at each end of the range, and the spelling of the
# exponent itself — so matching the canonical form means rendering
# numbers here rather than delegating.
#
# String escaping is *not* reimplemented: ``json.dumps(s,
# ensure_ascii=False)`` and ``JSON.stringify(s)`` already agree byte for
# byte over the escape table, so the one function that is right is the
# one that gets called.
#
# ``_NON_FINITE_NAMES`` — read by ``format_json_number`` below — is defined
# above the accept-domain section, the other half that reads it.


def _non_finite_message(name: str) -> str:
    """The single sentence both runtimes raise for a non-finite number.

    Kept identical to the string in ``vera/browser/runtime.mjs`` so a
    caller reading either host's failure learns the same thing.
    """
    return (
        f"json_stringify: {name} is not representable in JSON — RFC 8259 "
        f"has no NaN or Infinity.  Guard with float_is_nan / "
        f"float_is_infinite before serialising."
    )


def _shortest_digits(value: float) -> tuple[str, int]:
    """Decompose a positive, finite float into ``(digits, n)`` such that
    ``value == int(digits) * 10 ** (n - len(digits))``.

    ``digits`` carries no leading or trailing zeros, which makes it the
    ``s`` of ECMA-262 §6.1.6.1.20 and ``n`` the position of the decimal
    point relative to its first digit.  ``repr`` already yields the
    shortest decimal that reads back as the same double, so the digits
    are taken from it unchanged and only their *placement* is recomputed.
    """
    mantissa, _, exponent = repr(value).partition("e")
    exp = int(exponent) if exponent else 0
    int_part, _, frac_part = mantissa.partition(".")
    digits = int(int_part + frac_part)
    e10 = exp - len(frac_part)
    while digits >= 10 and digits % 10 == 0:
        digits //= 10
        e10 += 1
    text = str(digits)
    return text, e10 + len(text)


def format_json_number(value: float) -> str:
    """Render a JSON number in the canonical form (spec §9.7.1).

    This is ECMA-262 §6.1.6.1.20 Number::toString with radix 10, which
    is what ``JSON.stringify`` uses for numbers.  Non-finite values have
    no JSON representation and raise instead of being coerced.
    """
    if value != value or value in (float("inf"), float("-inf")):
        raise ValueError(_non_finite_message(
            _NON_FINITE_NAMES[repr(value)],
        ))
    if value == 0.0:
        return "0"  # covers -0.0: ECMAScript renders both zeros as "0"
    if value < 0.0:
        return "-" + format_json_number(-value)

    digits, n = _shortest_digits(value)
    k = len(digits)
    if k <= n <= 21:
        # Integral, and short enough to write out: pad with zeros.
        return digits + "0" * (n - k)
    if 0 < n <= 21:
        # Decimal point falls inside the digits.
        return digits[:n] + "." + digits[n:]
    if -6 < n <= 0:
        # Leading zeros, down to but not past 10^-6.
        return "0." + "0" * (-n) + digits
    # Exponential.  The exponent is written with an explicit sign and no
    # zero padding, where ``repr`` writes "1e-07".
    exp = n - 1
    mantissa = digits if k == 1 else digits[0] + "." + digits[1:]
    return f"{mantissa}e{'+' if exp >= 0 else '-'}{abs(exp)}"


def dumps_canonical(value: Any) -> str:
    """Serialize a value read by :func:`read_json` to canonical JSON text.

    The accepted domain is exactly what :func:`read_json` returns —
    ``None``, ``bool``, ``float``, ``str``, ``list``, ``dict`` — and
    anything else raises rather than being coerced, because a value
    outside that set means the ADT walk went wrong and a plausible-looking
    string would hide it.  Object keys keep insertion order, which is
    what both hosts' underlying maps preserve.
    """
    import json as _json

    parts: list[str] = []

    def emit(node: Any) -> None:
        if node is None:
            parts.append("null")
        elif node is True:
            parts.append("true")
        elif node is False:
            parts.append("false")
        elif isinstance(node, float):
            parts.append(format_json_number(node))
        elif isinstance(node, str):
            parts.append(_json.dumps(node, ensure_ascii=False))
        elif isinstance(node, list):
            parts.append("[")
            for i, item in enumerate(node):
                if i:
                    parts.append(",")
                emit(item)
            parts.append("]")
        elif isinstance(node, dict):
            parts.append("{")
            for i, (key, item) in enumerate(node.items()):
                if i:
                    parts.append(",")
                parts.append(_json.dumps(str(key), ensure_ascii=False))
                parts.append(":")
                emit(item)
            parts.append("}")
        else:
            raise TypeError(
                f"json_stringify: read_json produced {type(node).__name__}, "
                f"which is not a Json value; the ADT walk is wrong"
            )

    emit(value)
    return "".join(parts)
