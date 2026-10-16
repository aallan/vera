"""JSON host bindings (Json built-in type, spec §9.7.1).

Extracted verbatim from `execute()` in `vera/codegen/api.py` (#421);
the host callbacks call the module-level heap helpers in
`vera.runtime.heap` instead of closing over `execute()` locals.
"""

from __future__ import annotations

import wasmtime

from vera.runtime.heap import (
    _ShadowGuard,
    _rooted_read,
    _alloc_jobject_map,
    _alloc_result_err_string,
    _alloc_result_ok_i32,
    _alloc_string,
    _call_alloc,
    _decode_jobject,
    _read_f64,
    _read_i32,
    _read_wasm_string,
    _write_f64,
    _write_i32,
)


def register_json(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested JSON host functions on `linker`."""
    import json as _json

    from vera.wasm.json_serde import (
        non_finite_parse_message,
        dumps_canonical,
        first_domain_violation,
        read_json,
        write_json,
    )

    if "json_parse" in ops_used:
        def host_json_parse(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            # json_parse accepts exactly RFC 8259-valid text that
            # decodes to finite numbers and strings of Unicode scalar
            # values (spec §9.7.1); everything else is a handled Err,
            # identically on both hosts, at the parse.  Vera defines
            # that domain — it does not inherit Python's.  The two gates
            # below are what ``json.loads`` alone would not enforce; the
            # browser's twin sentences live in
            # ``vera/browser/runtime.mjs``.
            text = _read_wasm_string(caller, ptr, length)

            # #1306.  Python's default ``parse_constant`` maps ``NaN`` /
            # ``Infinity`` / ``-Infinity`` onto the matching floats; RFC
            # 8259 has no such literals and ``JSON.parse`` refuses them.
            #
            # The hook RECORDS rather than raises, and the refusal is
            # decided after the parse finishes.  Raising immediately
            # would make the reference host answer a *different
            # question* from the browser: Python's scanner calls the
            # hook as soon as it sees the token, so ``[Infinity_x]`` —
            # malformed for a reason that has nothing to do with the
            # constant — would report the non-finite sentence here while
            # the browser reported a syntax error.  Recording and
            # continuing asks what the browser asks: *would this text be
            # valid JSON if the constants were admitted?*  Only then is
            # the constant the whole story, and only then do both hosts
            # say the same sentence.  The placeholder is inert — the
            # refusal below fires before anything is marshalled.
            seen_constant: list[str] = []

            def record_non_finite(name: str) -> float:
                if not seen_constant:
                    seen_constant.append(name)
                return 0.0

            try:
                parsed = _json.loads(text, parse_constant=record_non_finite)
            except (ValueError, TypeError) as exc:
                return _alloc_result_err_string(caller, str(exc))
            if seen_constant:
                return _alloc_result_err_string(
                    caller, non_finite_parse_message(seen_constant[0]),
                )
            # The two value-level exclusions, in one document-order
            # walk.  A lone surrogate is not a Unicode scalar value, so
            # it has no UTF-8 encoding and cannot become a Vera string
            # at all (#1308).  A number that overflowed to an infinity
            # is the second entry route to a non-finite JNumber, the one
            # the bare-constant gate above cannot see because the text
            # is perfectly good RFC 8259 (#1306).
            #
            # Both are checked on the decoded VALUE, before anything
            # crosses into WASM memory: past this point ``write_json``
            # reaches ``_alloc_string``, whose ``.encode("utf-8")`` is
            # where the surrogate refusal used to arrive as a raw
            # traceback, and ``json_stringify`` is where the overflow
            # one used to arrive — a call too late, and as the same
            # traceback (#1302).
            violation = first_domain_violation(parsed)
            if violation is not None:
                return _alloc_result_err_string(caller, violation)
            # #692: hold the shadow-stack window open across the
            # full tree marshalling AND the final Result.Ok
            # wrapper alloc.  ``guard.__exit__`` restores
            # ``$gc_sp`` on the way out — pops everything we
            # pushed.
            with _ShadowGuard(caller) as guard:
                json_ptr = write_json(
                    caller, _call_alloc, _write_i32, _write_f64,
                    _alloc_string, _alloc_jobject_map, guard, parsed,
                )
                # Push the tree root before the Result.Ok alloc —
                # that alloc could trigger GC and free the
                # otherwise-unrooted tree.
                guard.push(json_ptr)
                return _alloc_result_ok_i32(caller, json_ptr)

        linker.define_func(
            "vera", "json_parse",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_json_parse, access_caller=True,
        )

    if "json_stringify" in ops_used:
        def host_json_stringify(
            caller: wasmtime.Caller, ptr: int,
        ) -> tuple[int, int]:
            value = _rooted_read(caller, ptr, lambda: read_json(
                caller, ptr, _read_i32, _read_f64,
                _read_wasm_string, _decode_jobject,
            ))
            # #1293: one canonical output form, shared with
            # ``vera/browser/runtime.mjs`` and stated in spec §9.7.1.
            # ``dumps_canonical`` also refuses NaN and Infinity, which
            # RFC 8259 cannot represent — the browser used to emit
            # ``null`` for them, silently substituting a different and
            # perfectly valid JSON value.
            text = dumps_canonical(value)
            return _alloc_string(caller, text)

        linker.define_func(
            "vera", "json_stringify",
            wasmtime.FuncType(
                [wasmtime.ValType.i32()],
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
            ),
            host_json_stringify, access_caller=True,
        )
