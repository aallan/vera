"""Math effect host bindings (#467).

Extracted from `execute()` in `vera/codegen/api.py` (#421); stateless --
`register_math` defines and registers the host callbacks on the linker.
"""

from __future__ import annotations

import wasmtime


def register_math(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested `vera.math_*` host functions on `linker`."""
    import math as _math_mod

    _f64_unary = wasmtime.FuncType(
        [wasmtime.ValType.f64()], [wasmtime.ValType.f64()]
    )
    from typing import Callable

    # The log family has a *pole* at zero: IEEE 754 and JS
    # `Math.log(0)` give -Infinity there, distinct from genuine
    # domain errors (`log(-1)` -> NaN).  Python's `math.log(0.0)`
    # raises `ValueError` for BOTH cases, so the wrapper below must
    # tell them apart or the two runtimes silently diverge (#790).
    _log_pole_ops = frozenset({"log", "log2", "log10"})

    def _math_unary_host(
        op_name: str, py_fn: Callable[[float], float],
    ) -> Callable[[wasmtime.Caller, float], float]:
        """Wrap a `math.*` function as a wasmtime host callback.

        Factored into its own function so the captured `py_fn`
        is bound at call time rather than at loop-variable time —
        the classic Python late-binding closure trap.

        Python's `math` module raises `ValueError` on
        out-of-domain inputs (e.g., `math.log(-1)`).  IEEE 754
        and the JavaScript host runtime both return NaN in those
        cases, so we translate the exception into NaN to keep
        the two WASM runtimes observationally equivalent and
        let Vera programs detect the condition via
        `float_is_nan(...)` instead of trapping.  The one
        exception is the log-family zero pole (`log(0.0)`,
        including `-0.0`), where IEEE 754 / JS give -Infinity,
        not NaN — see `_log_pole_ops` above (#790).
        """
        def host(_caller: wasmtime.Caller, x: float) -> float:
            try:
                return py_fn(x)
            except ValueError:
                if op_name in _log_pole_ops and x == 0.0:
                    return float("-inf")
                return float("nan")
        return host

    _math_unary_specs: tuple[tuple[str, Callable[[float], float]], ...] = (
        ("log",   _math_mod.log),
        ("log2",  _math_mod.log2),
        ("log10", _math_mod.log10),
        ("sin",   _math_mod.sin),
        ("cos",   _math_mod.cos),
        ("tan",   _math_mod.tan),
        ("asin",  _math_mod.asin),
        ("acos",  _math_mod.acos),
        ("atan",  _math_mod.atan),
    )
    for op_name, py_fn in _math_unary_specs:
        if op_name in ops_used:
            linker.define_func(
                "vera", op_name, _f64_unary,
                _math_unary_host(op_name, py_fn), access_caller=True,
            )

    if "atan2" in ops_used:
        def host_atan2(
            _caller: wasmtime.Caller, y: float, x: float,
        ) -> float:
            # `math.atan2` doesn't raise for any Float64 input
            # (it's total over the real numbers), but we mirror
            # the unary wrapper's pattern so future changes stay
            # uniform.
            try:
                return _math_mod.atan2(y, x)
            except ValueError:
                return float("nan")
        linker.define_func(
            "vera", "atan2",
            wasmtime.FuncType(
                [wasmtime.ValType.f64(), wasmtime.ValType.f64()],
                [wasmtime.ValType.f64()],
            ),
            host_atan2, access_caller=True,
        )
