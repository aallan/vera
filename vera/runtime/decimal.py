"""Decimal effect host bindings (§9.6).

Extracted from `execute()` in `vera/codegen/api.py` (#421).  Decimal is the one
host family that keeps a value-typed Python store (`decimal_store`, created in
`execute()` so the shared `host_decref_handle` GC hook can close over it);
`register_decimal` registers it in `host_store_refs` and wires the ops.
"""

from __future__ import annotations

import re
from decimal import MAX_EMAX, MIN_EMIN, ROUND_HALF_EVEN
from decimal import Context as PyContext
from decimal import Decimal as PyDecimal
from decimal import InvalidOperation, Overflow, localcontext

import wasmtime

from vera.runtime.heap import (
    _WRAP_KIND_DECIMAL,
    _alloc_option_none,
    _alloc_option_some_i32,
    _alloc_ordering,
    _alloc_string,
    _read_wasm_string,
    _wrap_handle,
)

# The spec §9.7.2 ``decimal_from_string`` grammar (#856 / PR #877):
# ASCII finite decimals only — no special values (NaN / Infinity /
# sNaN), no digit-group underscores, no non-ASCII digits — applied
# after stripping surrounding whitespace, with the exponent token
# bounded to |exp| <= 999999 (the context's Emax/Emin floor; a literal
# beyond it could never participate in any operation without
# overflowing — CR finding 3518083324, where the browser's parseInt
# silently rounded a beyond-MAX_SAFE_INTEGER exponent while this host
# stored it exactly).  Both runtimes pre-validate with this exact
# grammar (the browser runtime's ``DEC_RE`` + ``decExpTokenInRange``
# in ``runtime.mjs`` recognise the same language), so the accepted
# domain is defined by the spec, not by whatever the host decimal
# library happens to parse (DESIGN.md: explicit over implicit).
_DECIMAL_STRING_RE = re.compile(
    r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE]([+-]?[0-9]+))?"
)
_DECIMAL_EXP_TOKEN_MAX = 999999
# The bound as a digit count, so the token is measured as a STRING and
# never handed to ``int()`` (#1502): a grammar-valid token of 5,000
# leading zeros is the exponent 0, but ``int()`` refuses a string that
# long (CPython's 4,300-digit integer-string limit) and the refusal
# ended the program.  The browser's ``decExpTokenInRange`` has always
# measured the token this way.
_DECIMAL_EXP_TOKEN_DIGITS = len(str(_DECIMAL_EXP_TOKEN_MAX))

# The whitespace §9.7.2 says the grammar is applied "after ignoring
# surrounding whitespace", stated explicitly rather than inherited from
# ``str.strip`` (#1303 review).  Bare ``strip()`` takes Python's whole
# Unicode notion — U+001C..U+001F, U+0085, U+00A0, the Unicode space
# separators — while the browser's ``String.prototype.trim`` takes a
# DIFFERENT set that includes U+FEFF and excludes the first two groups,
# so the accepted domain diverged in both directions.  This is the set
# ``is_whitespace`` already states (spec §9.7.x), which is the one the
# language has: tab, LF, VT, FF, CR, space.
_ASCII_WS = "\t\n\v\f\r "

# Decimal arithmetic, negation, absolute value and comparison run in ONE
# fixed context (#1502), stated here and in spec §9.7.2: the default
# precision (28 significant digits) and rounding (``ROUND_HALF_EVEN``),
# the exponent range widened to the library maximum (``MAX_EMAX`` /
# ``MIN_EMIN`` ~= ±1e18), and no trapped signals.
# ``decimal_from_string`` bounds INPUT exponent tokens to
# |exp| <= 999999, but exact arithmetic can grow the exponent
# (``1e999999 * 1e999999`` -> ``1E+1999998``); under the default Emax of
# 999999 that raised a raw ``decimal.Overflow`` traceback on a check-green
# program, and diverged from the unbounded browser scaled-BigInt engine.
# The widened range is comfortably above any result reachable from
# grammar-conforming operands (worst case ~±2e6), so these ops return the
# SAME exact value the browser produces (#856 / PR #877 CodeRabbit
# finding 3518540519).
#
# No signal traps, because every one of those operations has a total
# signature and the values it is given include the non-finite ones
# ``decimal_from_float`` makes from ``nan()`` and ``infinity()``.  With
# ``InvalidOperation`` trapped, ``∞ − ∞``, ``∞ × 0``, ``∞ ÷ ∞`` and an
# ordering comparison against NaN raised instead of returning, and the
# unary operators, which ran in the DEFAULT context, raised ``Overflow``
# on a grammar-valid ``12345e999999``.  Untrapped, each returns the IEEE
# 754 / General Decimal Arithmetic answer: NaN for an invalid operation,
# a signed infinity past the (unreachable) exponent range.
#
# ``decimal_round`` is the exception, and deliberately so: its quantize
# runs in the default context, whose trapped ``InvalidOperation`` and
# ``Overflow`` are exactly what its return-the-value-unchanged fallback
# catches (and what the browser engine mirrors).
_DECIMAL_WIDE_CTX = PyContext(
    prec=28, rounding=ROUND_HALF_EVEN, Emax=MAX_EMAX, Emin=MIN_EMIN,
    traps=[],
)


def register_decimal(
    linker: wasmtime.Linker,
    ops_used: set[str],
    decimal_store: dict[int, PyDecimal],
    host_store_refs: dict[str, dict[int, object]],
) -> None:
    """Register the requested Decimal host functions on `linker`."""
    _decimal_next_handle = [1]
    # Decimal keeps a value-typed Python store — the only host store
    # remaining after #706 moved Map / Set to bucket-as-truth.
    host_store_refs["decimal"] = decimal_store  # type: ignore[assignment]
    # #695/#706: Decimal is intentionally EXEMPT from the bucket-as-
    # truth migration.  ``PyDecimal`` is value-typed (immutable
    # digit/sign/exponent attributes, no WASM heap pointers inside
    # the stored object), so the silent-UAF window that affects
    # Map<K, T_heap> and Set<T_heap> cannot occur for Decimal.  Its
    # wrapper keeps the #573 tagged-handle layout (initialised by
    # ``_emit_wrap_handle`` / JS ``wrapHandle``), leaves ``bucket_ptr``
    # 0, and ``host_attach_bucket`` accepts only kind=3.

    def _decimal_alloc(d: PyDecimal) -> int:
        h = _decimal_next_handle[0]
        _decimal_next_handle[0] = h + 1
        decimal_store[h] = d
        return h

    if "decimal_from_int" in ops_used:
        def host_decimal_from_int(
            _caller: wasmtime.Caller, v: int,
        ) -> int:
            return _decimal_alloc(PyDecimal(v))
        linker.define_func(
            "vera", "decimal_from_int",
            wasmtime.FuncType([wasmtime.ValType.i64()],
                              [wasmtime.ValType.i32()]),
            host_decimal_from_int, access_caller=True,
        )

    if "decimal_from_float" in ops_used:
        def host_decimal_from_float(
            _caller: wasmtime.Caller, v: float,
        ) -> int:
            return _decimal_alloc(PyDecimal(str(v)))
        linker.define_func(
            "vera", "decimal_from_float",
            wasmtime.FuncType([wasmtime.ValType.f64()],
                              [wasmtime.ValType.i32()]),
            host_decimal_from_float, access_caller=True,
        )

    if "decimal_from_string" in ops_used:
        def host_decimal_from_string(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            s = _read_wasm_string(caller, ptr, length).strip(_ASCII_WS)
            # Pre-validate against the spec §9.7.2 grammar so the
            # accepted domain matches the browser runtime exactly
            # (PyDecimal alone would also accept NaN / Infinity /
            # sNaN / 1_000 / non-ASCII digits).
            m = _DECIMAL_STRING_RE.fullmatch(s)
            if m is None:
                return _alloc_option_none(caller)
            # Exponent-token bound (|exp| <= 999999), measured on the
            # token's significant digits so no ``int()`` is ever asked
            # to convert an arbitrarily long string (#1502).
            exp_tok = m.group(1)
            if exp_tok is not None:
                exp_digits = exp_tok.lstrip("+-").lstrip("0") or "0"
                if len(exp_digits) > _DECIMAL_EXP_TOKEN_DIGITS:
                    return _alloc_option_none(caller)
            try:
                d = PyDecimal(s)
                # #573 phase 3: wrap the Decimal handle so the
                # Option<Decimal>'s Some payload is a wrapper
                # pointer (matching what every other Decimal-
                # producing op now returns).
                raw = _decimal_alloc(d)
                wrapped = _wrap_handle(
                    caller, _WRAP_KIND_DECIMAL, raw,
                )
                return _alloc_option_some_i32(caller, wrapped)
            except InvalidOperation:
                # Unreachable for grammar-conforming strings; kept as a
                # belt-and-braces guard.
                return _alloc_option_none(caller)
        linker.define_func(
            "vera", "decimal_from_string",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_from_string, access_caller=True,
        )

    if "decimal_to_string" in ops_used:
        def host_decimal_to_string(
            caller: wasmtime.Caller, h: int,
        ) -> tuple[int, int]:
            s = str(decimal_store[h])
            return _alloc_string(caller, s)
        linker.define_func(
            "vera", "decimal_to_string",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()]),
            host_decimal_to_string, access_caller=True,
        )

    if "decimal_to_float" in ops_used:
        def host_decimal_to_float(
            _caller: wasmtime.Caller, h: int,
        ) -> float:
            return float(decimal_store[h])
        linker.define_func(
            "vera", "decimal_to_float",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.f64()]),
            host_decimal_to_float, access_caller=True,
        )

    if "decimal_add" in ops_used:
        def host_decimal_add(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            # Widened-exponent context so a finite result that exceeds the
            # default Emax cannot raise Overflow (matches the browser).
            return _decimal_alloc(
                _DECIMAL_WIDE_CTX.add(decimal_store[a], decimal_store[b]))
        linker.define_func(
            "vera", "decimal_add",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_add, access_caller=True,
        )

    if "decimal_sub" in ops_used:
        def host_decimal_sub(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return _decimal_alloc(
                _DECIMAL_WIDE_CTX.subtract(decimal_store[a], decimal_store[b]))
        linker.define_func(
            "vera", "decimal_sub",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_sub, access_caller=True,
        )

    if "decimal_mul" in ops_used:
        def host_decimal_mul(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return _decimal_alloc(
                _DECIMAL_WIDE_CTX.multiply(decimal_store[a], decimal_store[b]))
        linker.define_func(
            "vera", "decimal_mul",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_mul, access_caller=True,
        )

    if "decimal_div" in ops_used:
        def host_decimal_div(
            caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            # #573 phase 3: ``a`` and ``b`` are raw handles
            # (the WASM-side translator unwraps wrapper
            # pointers before this call, matching the
            # pattern for every other Decimal binary op).
            # The result handle is wrapped here because the
            # host constructs ``Option<Decimal>`` internally
            # — its Some payload must be a wrapper pointer
            # to match what user code post-match expects.
            divisor = decimal_store[b]
            if divisor == 0:
                return _alloc_option_none(caller)
            raw = _decimal_alloc(
                _DECIMAL_WIDE_CTX.divide(decimal_store[a], divisor))
            wrapped = _wrap_handle(
                caller, _WRAP_KIND_DECIMAL, raw,
            )
            return _alloc_option_some_i32(caller, wrapped)
        linker.define_func(
            "vera", "decimal_div",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_div, access_caller=True,
        )

    if "decimal_neg" in ops_used:
        def host_decimal_neg(
            _caller: wasmtime.Caller, h: int,
        ) -> int:
            # The fixed context (#1502): the default one overflowed on a
            # grammar-valid ``12345e999999``.
            return _decimal_alloc(_DECIMAL_WIDE_CTX.minus(decimal_store[h]))
        linker.define_func(
            "vera", "decimal_neg",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_neg, access_caller=True,
        )

    if "decimal_compare" in ops_used:
        def host_decimal_compare(
            caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            da, db = decimal_store[a], decimal_store[b]
            # #1502: the ordering operators take their context from the
            # thread, so they run under the fixed one.  An ordering
            # comparison involving a NaN is unordered: it signals
            # ``InvalidOperation``, which is untrapped there, and
            # ``<`` and ``==`` are both false, so the answer is
            # ``Greater`` (spec §9.7.2) rather than a raise.
            with localcontext(_DECIMAL_WIDE_CTX):
                if da < db:
                    tag = 0  # Less
                elif da == db:
                    tag = 1  # Equal
                else:
                    tag = 2  # Greater
            return _alloc_ordering(caller, tag)
        linker.define_func(
            "vera", "decimal_compare",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_compare, access_caller=True,
        )

    if "decimal_eq" in ops_used:
        def host_decimal_eq(
            _caller: wasmtime.Caller, a: int, b: int,
        ) -> int:
            return 1 if decimal_store[a] == decimal_store[b] else 0
        linker.define_func(
            "vera", "decimal_eq",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_eq, access_caller=True,
        )

    if "decimal_round" in ops_used:
        def host_decimal_round(
            _caller: wasmtime.Caller, h: int, places: int,
        ) -> int:
            d = decimal_store[h]
            # Use quantize for precise rounding.  The quantum
            # computation lives INSIDE the try: for places < -Emax
            # (-999999) ``Decimal(10) ** -places`` raises Overflow,
            # which previously escaped as a raw traceback (PR #877
            # fold-in).  Both failure modes fall back to the value
            # unchanged, mirrored by the browser engine's guards.
            try:
                q = PyDecimal(10) ** -places
                return _decimal_alloc(d.quantize(q))
            except (InvalidOperation, Overflow):
                # Extreme exponent — return original value unchanged
                return _decimal_alloc(d)
        linker.define_func(
            "vera", "decimal_round",
            wasmtime.FuncType([wasmtime.ValType.i32(),
                               wasmtime.ValType.i64()],
                              [wasmtime.ValType.i32()]),
            host_decimal_round, access_caller=True,
        )

    if "decimal_abs" in ops_used:
        def host_decimal_abs(
            _caller: wasmtime.Caller, h: int,
        ) -> int:
            return _decimal_alloc(_DECIMAL_WIDE_CTX.abs(decimal_store[h]))
        linker.define_func(
            "vera", "decimal_abs",
            wasmtime.FuncType([wasmtime.ValType.i32()],
                              [wasmtime.ValType.i32()]),
            host_decimal_abs, access_caller=True,
        )
