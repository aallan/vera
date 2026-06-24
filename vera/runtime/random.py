"""Random effect host bindings (#465).

Extracted from `execute()` in `vera/codegen/api.py` (#421); stateless --
`register_random` defines and registers the host callbacks on the linker.
"""

from __future__ import annotations

import wasmtime


def register_random(linker: wasmtime.Linker, ops_used: set[str]) -> None:
    """Register the requested `vera.random_*` host functions on `linker`."""
    import random as _random_mod

    if "random_int" in ops_used:
        # vera.random_int(low: i64, high: i64) -> i64
        # Inclusive range [low, high].  Caller is required by
        # contract to ensure low <= high; we don't double-check.
        def host_random_int(
            _caller: wasmtime.Caller, low: int, high: int,
        ) -> int:
            # S311 — Random effect is for games / simulations /
            # Monte Carlo, not crypto.  #465 explicitly scopes
            # the effect that way; secure randomness would
            # warrant a separate `Crypto` effect with
            # `secrets.randbelow`.
            return _random_mod.randint(low, high)  # noqa: S311

        linker.define_func(
            "vera", "random_int",
            wasmtime.FuncType(
                [wasmtime.ValType.i64(), wasmtime.ValType.i64()],
                [wasmtime.ValType.i64()],
            ),
            host_random_int, access_caller=True,
        )

    if "random_float" in ops_used:
        # vera.random_float() -> f64 in [0.0, 1.0)
        def host_random_float(_caller: wasmtime.Caller) -> float:
            # S311 — see host_random_int; non-crypto by design.
            return _random_mod.random()  # noqa: S311

        linker.define_func(
            "vera", "random_float",
            wasmtime.FuncType([], [wasmtime.ValType.f64()]),
            host_random_float, access_caller=True,
        )

    if "random_bool" in ops_used:
        # vera.random_bool() -> i32 (0 or 1)
        def host_random_bool(_caller: wasmtime.Caller) -> int:
            # S311 — see host_random_int; non-crypto by design.
            return 1 if _random_mod.random() < 0.5 else 0  # noqa: S311

        linker.define_func(
            "vera", "random_bool",
            wasmtime.FuncType([], [wasmtime.ValType.i32()]),
            host_random_bool, access_caller=True,
        )
