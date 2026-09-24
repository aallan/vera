"""Which declaration each call names, as the checker resolved it (#1494).

The checker resolves every bare call lexically — the nearest ``where``
helper, then the namespace's own top-level declaration, then the flat
registry of built-ins, the prelude and imports — and that resolution is the
program's meaning.  Code generation and the verifier's instantiation
discovery must bind each call to the SAME declaration, so they read it from
here rather than re-deriving it from name sets of their own: a second
derivation is how a ``where`` helper under a generic function came to count
as a namespace-wide declaration, and a module's calls ran the entry's
namesake (R-1507 round 1, finding 2).

:class:`CallResolution` is the checker's answer for one program: for each
imported module, the target of every call in its bodies, keyed by the call's
span; and for the entry program, which module's declaration each bare name
the entry reaches through an import denotes — the owner of that bare name.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field

#: The call resolved to a ``where`` helper in scope — local to its parent.
HELPER = "helper"
#: The call resolved to a top-level declaration of the namespace itself.
TOP = "top"
#: The call resolved to an imported module's declaration (``path``).
IMPORT = "import"
#: The call resolved to the prelude's function.
PRELUDE = "prelude"
#: The call resolved to a built-in the compiler implements.
BUILTIN = "builtin"

SpanKey = tuple[int, int, int, int]


@dataclass(frozen=True)
class CallTarget:
    """What one call denotes: its kind and, for an import, the module."""

    kind: str
    path: tuple[str, ...] = ()


@dataclass(frozen=True)
class CallResolution:
    """The checker's resolution of one program's calls.

    ``entry_owners`` maps each bare name the entry program resolves to an
    imported declaration onto that declaration's module: the owner of the
    entry's bare name (§8.5.2.1).  ``module_targets`` maps each resolved
    module's path to the target of every call in its bodies, keyed by
    :func:`vera.ast.span_key`.
    """

    entry_owners: Mapping[str, tuple[str, ...]] = field(default_factory=dict)
    module_targets: Mapping[tuple[str, ...], Mapping[SpanKey, CallTarget]] = (
        field(default_factory=dict)
    )
