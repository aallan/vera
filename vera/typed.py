"""The typed program: every type derived once (#1679, ROADMAP Stage 26).

The checker types every node of the entry file, of each module the program
reaches and of the prelude, and records each generic call's instantiation,
the type arguments it inferred there.  Those records are keyed by a node's
identity (:attr:`vera.ast.Node.node_id`), not its span: a span cannot tell a
clone's node from its template's or from another clone's.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from vera.types import Type


@dataclass(frozen=True)
class Instantiation:
    """A generic call's instantiation, as the checker inferred it.

    *callee* is the link name of the generic declaration the call binds to
    (:attr:`vera.binding.DeclId.link_name`), *forall_vars* the callee's type
    variables in its declared order, and *mapping* the type each variable
    the call fixed is instantiated at.  A type in *mapping* can name a type
    variable of the function the call is written in, which an instantiation
    of that function binds."""

    callee: str
    forall_vars: tuple[str, ...]
    mapping: Mapping[str, Type]
