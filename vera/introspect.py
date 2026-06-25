"""Compiler self-introspection payloads for ``vera builtins/effects/errors --json``.

Each builder returns a ``{"schema": ..., "items": [...]}`` dict sourced directly
from the live compiler registries (``vera.errors.ERROR_CODES``, the built-in
function / effect / ability tables in ``vera.environment.TypeEnv``), so a
published count is the registry's own length — never a hand-maintained number
that can drift from the compiler. See #539 (and the doc-consolidation brief,
#528) for the motivation: "the compiler becomes the source of truth for its own
internals."

The ``since`` (version-introduced) field is present on every item for
forward-compatibility; it is populated best-effort in a later layer and is
``None`` where the introduction version is not attributable.
"""

from __future__ import annotations

from vera._since import SINCE
from vera.errors import ERROR_CODES

# Map a diagnostic code's two-character prefix to the compiler phase that emits
# it, mirroring the ``ERROR_CODES`` section banners and the pipeline in
# DESIGN.md (parse -> typecheck -> verify -> codegen; testing is its own phase).
_ERROR_PHASE_BY_PREFIX: dict[str, str] = {
    "W0": "warning",
    "E0": "parse",  # parse & transform
    "E1": "typecheck",  # core & expressions
    "E2": "typecheck",  # calls
    "E3": "typecheck",  # control flow
    "E5": "verify",
    "E6": "codegen",
    "E7": "test",
}


def _error_phase(code: str) -> str:
    """Derive the compiler phase for a diagnostic code from its prefix."""
    return _ERROR_PHASE_BY_PREFIX.get(code[:2], "unknown")


def errors_payload() -> dict[str, object]:
    """Enumerate the diagnostic registry as ``{schema, items}``.

    One item per ``ERROR_CODES`` entry, sorted by code, each carrying its
    derived ``phase`` and human-readable ``title``.
    """
    items: list[dict[str, str | None]] = [
        {
            "code": code,
            "phase": _error_phase(code),
            "title": ERROR_CODES[code],
            "since": SINCE.get(code),
        }
        for code in sorted(ERROR_CODES)
    ]
    return {"schema": "vera-errors/1", "items": items}


def builtins_payload() -> dict[str, object]:
    """Enumerate the built-in function registry as ``{schema, items}``.

    Sourced from ``TypeEnv().functions`` so the count is the live registry's
    length — the hand-maintained "164 built-in functions" claim made canonical.
    ``module`` is ``"core"`` (the standard prelude) and ``kind`` is ``"function"``
    for every entry today; both are carried explicitly for forward-compatibility.
    """
    from vera.environment import TypeEnv

    env = TypeEnv()
    items: list[dict[str, str | None]] = [
        {"name": name, "module": "core", "kind": "function", "since": SINCE.get(name)}
        for name in sorted(env.functions)
    ]
    return {"schema": "vera-builtins/1", "items": items}


# Exn<T> is a parameterised effect recognised specially by the compiler
# (handle[Exn<E>] in codegen — see vera/wasm/calls_handlers.py), not a fixed
# entry in TypeEnv().effects. It is listed here so `vera effects --json` surfaces
# it for discoverability — the one effect not read from the live registry.
_PARAMETERISED_EFFECTS: list[dict[str, object]] = [
    {
        "name": "Exn",
        "kind": "effect",
        "type_params": ["T"],
        "ops": ["throw"],
        "since": SINCE.get("Exn"),
    },
]


def effects_payload() -> dict[str, object]:
    """Enumerate the algebraic effect *and* ability registries as ``{schema, items}``.

    Both the built-in effects and the built-in abilities are listed — the
    language's capability surface (DESIGN.md) — discriminated by ``kind``
    (``"effect"`` / ``"ability"``). Each item carries its declared
    ``type_params`` and the sorted names of its ``ops``.
    """
    from vera.environment import TypeEnv

    env = TypeEnv()
    items: list[dict[str, object]] = []
    for name in sorted(env.effects):
        effect = env.effects[name]
        items.append(
            {
                "name": name,
                "kind": "effect",
                "type_params": list(effect.type_params or ()),
                "ops": sorted(effect.operations),
                "since": SINCE.get(name),
            }
        )
    items.extend(_PARAMETERISED_EFFECTS)
    for name in sorted(env.abilities):
        ability = env.abilities[name]
        items.append(
            {
                "name": name,
                "kind": "ability",
                "type_params": list(ability.type_params or ()),
                "ops": sorted(ability.operations),
                "since": SINCE.get(name),
            }
        )
    return {"schema": "vera-effects/1", "items": items}
