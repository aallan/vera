"""The obligation table (#1695, ROADMAP Stage 27): every obligation site of a
typed program, listed once, which the verifier discharges and code
generation guards.

Built by :func:`build` after :func:`vera.typed.build` and before
:func:`vera.verifier.verify` and :func:`vera.codegen.compile`, with neither
Z3 nor WASM.  A row is one obligation at one node of the typed program:
its kind (today's :data:`vera.obligations.core.ObligationKind`), the place
inside the value it is about (``path``), the function it belongs to, the
type it holds the value to, whether a runtime check can be emitted for it
and, where none can, why.  The design record is the Stage 27 design note.

This module is the table's seam; :func:`build` is filled in by the change
that makes the verifier and code generation read it.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from vera import ast
from vera.obligations.core import ObligationKind

if TYPE_CHECKING:
    from vera.typed import TypedProgram
    from vera.types import Type


@dataclass(frozen=True)
class Guard:
    """Whether code generation emits a runtime check for a row, and why not
    when it does not."""

    check: bool
    reason: str = ""


CHECK = Guard(True)
TRIVIAL = Guard(False, "the clause is trivially true")


@dataclass(frozen=True)
class Row:
    """One obligation site of the typed program."""

    id: int
    node: ast.Node
    kind: ObligationKind
    fn: str
    target: Type | None
    guard: Guard
    path: tuple[str, ...] = ()
    evaluation: tuple[object, ...] = ("body",)


@dataclass
class ObligationTable:
    """Every row of one typed program, in the order they were listed."""

    rows: list[Row] = field(default_factory=list)

    def rows_at(self, node: ast.Node) -> list[Row]:
        """The rows standing at *node*."""
        ident = node.node_id
        return [row for row in self.rows if row.node.node_id == ident]


def build(typed: TypedProgram) -> ObligationTable:
    """The obligation table of *typed*."""
    raise NotImplementedError("the obligation table is not built yet (#1695)")
