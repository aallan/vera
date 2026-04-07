"""Slot reference table utilities for ``vera check --explain-slots``.

Computes a slot resolution table for a function purely from its parameter
type expressions (no live type-checker environment required).

The De Bruijn convention: @T.0 is the *last* (rightmost) parameter of
type T in the signature; @T.1 is second-to-last; and so on.  For a
function ``fn foo(@Int, @Int -> @Int)``:
  - @Int.0 → parameter 2 (last @Int)
  - @Int.1 → parameter 1 (first @Int)
"""

from __future__ import annotations

from collections import defaultdict

from vera import ast


# ------------------------------------------------------------------
# Internal helpers
# ------------------------------------------------------------------

def _te_slot_name(te: ast.TypeExpr) -> str:
    """Return the canonical slot-matching name for a parameter TypeExpr.

    Mirrors the logic in ``TypeChecker._type_expr_to_slot_name``.
    Type aliases are opaque: @PosInt.0 counts PosInt bindings, not Int.
    """
    if isinstance(te, ast.NamedType):
        if te.type_args:
            inner = ", ".join(_te_slot_name(a) for a in te.type_args)
            return f"{te.name}<{inner}>"
        return te.name
    if isinstance(te, ast.RefinementType):
        return _te_slot_name(te.base_type)
    if isinstance(te, ast.FnType):
        return "Fn"
    return "?"


def _label(tname: str, slot_idx: int, n: int) -> str:
    """Human-readable label for a slot entry, e.g. 'last @Int'."""
    if n == 1:
        return f"only @{tname}"
    if slot_idx == 0:
        return f"last @{tname}"
    if slot_idx == n - 1:
        return f"first @{tname}"
    return f"{n - slot_idx} from last @{tname}"


# ------------------------------------------------------------------
# Public API
# ------------------------------------------------------------------

def slot_table(
    params: tuple[ast.TypeExpr, ...],
) -> dict[str, list[int]]:
    """Return the slot resolution table for a function's parameter list.

    Returns ``{type_name: [1-based param positions, slot-0-first]}``.

    Example: ``(@Int, @Int)`` → ``{"Int": [2, 1]}``
    meaning ``@Int.0`` = parameter 2, ``@Int.1`` = parameter 1.
    """
    by_type: dict[str, list[int]] = defaultdict(list)
    for i, te in enumerate(params, 1):
        by_type[_te_slot_name(te)].append(i)
    return {tname: list(reversed(pos)) for tname, pos in by_type.items()}


def format_slot_table(
    fn_name: str,
    params_str: str,
    table: dict[str, list[int]],
) -> str:
    """Format a human-readable slot environment block for one function.

    Returns a multi-line string suitable for printing to stdout, e.g.::

        fn divide(@Int, @Int -> @Int)
          @Int.0  parameter 2 (last @Int)
          @Int.1  parameter 1 (first @Int)
    """
    lines = [f"  fn {fn_name}({params_str})"]
    for tname in sorted(table):
        positions = table[tname]
        n = len(positions)
        for slot_idx, param_pos in enumerate(positions):
            lines.append(
                f"    @{tname}.{slot_idx}  "
                f"parameter {param_pos} ({_label(tname, slot_idx, n)})"
            )
    return "\n".join(lines)


def slot_table_dict(
    fn_name: str,
    table: dict[str, list[int]],
) -> dict[str, object]:
    """Return a JSON-serialisable slot table for a single function."""
    entries: list[dict[str, object]] = []
    for tname in sorted(table):
        for slot_idx, param_pos in enumerate(table[tname]):
            entries.append({
                "slot": f"@{tname}.{slot_idx}",
                "type": tname,
                "parameter": param_pos,
            })
    return {"function": fn_name, "slots": entries}
