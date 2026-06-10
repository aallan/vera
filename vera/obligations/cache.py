"""Incremental invalidation + discharge cache (#222 Phase B).

The warm session (Phase A) re-verified every function on every call.
Phase B adds a per-function discharge cache behind the same API: a
function whose verification *inputs* are unchanged replays its cached
obligations, diagnostics, and summary delta instead of re-entering Z3.

Soundness model — what a function's verification reads, and therefore
what its cache key must cover:

1. **The function itself** (``fn_structural_hash``): the full ``FnDecl``
   subtree *including spans*.  Spans are not incidental: cached
   diagnostics carry ``location`` + ``source_line`` and cached
   obligations carry line/column, so exact replay is only valid when
   the function is byte-identical *at the same position*.  A function
   that merely shifts down a line is a cache miss by design —
   conservative, and required for the differential oracle to hold
   exactly.
2. **Direct callees' interfaces** (``callee_component``): verifying
   ``f`` checks each callee's preconditions at the call site and
   assumes its postconditions, so a callee *contract or signature*
   change must invalidate ``f``.  A callee *body* change must not —
   bodies are never read across the call boundary.  Only direct local
   callees matter: transitive callees are read only by their own
   callers.
3. **Program context** (``program_context_hash``): ADT / type-alias /
   effect / ability declarations (pattern translation, sort creation,
   type resolution), imported-module contracts (C7d), the solver
   timeout, and the file name (baked into diagnostic locations).  Any
   change here invalidates every function — deliberately coarse;
   per the plan, when in doubt invalidate MORE.

Never cached: per the #222 plan hard rail, a function whose slice
contains any ``timeout``-status obligation is re-verified every run —
solver-timeout outcomes are load-dependent and must not be replayed.

Hashing uses ``repr()`` of the frozen-dataclass AST: every node is a
frozen dataclass of tuples / strs / ints / enums with deterministic,
content-only reprs (no ids, no dict iteration order), so equal trees
hash equal across runs and processes.
"""

from __future__ import annotations

import hashlib

from dataclasses import dataclass, fields, is_dataclass
from typing import Iterator

from vera import ast
from vera.errors import Diagnostic
from vera.obligations.core import ProofObligation


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def walk_nodes(node: object) -> Iterator[ast.Node]:
    """Yield every AST node in a subtree, including *node* itself.

    Generic dataclass-field walk rather than a per-type isinstance
    chain, so new AST node classes are covered automatically (the
    walker-completeness lesson from #597 applied structurally).
    """
    if isinstance(node, ast.Node):
        yield node
    if is_dataclass(node) and not isinstance(node, type):
        for f in fields(node):
            yield from walk_nodes(getattr(node, f.name))
    elif isinstance(node, tuple):
        for item in node:
            yield from walk_nodes(item)


def direct_callee_names(decl: ast.FnDecl) -> frozenset[str]:
    """Names of functions called anywhere in *decl* (body, contracts,
    where-blocks).  Local plain calls only — module-qualified calls'
    contracts are covered by the program context hash, and builtin
    names harmlessly miss the top-level function map.
    """
    return frozenset(
        n.name for n in walk_nodes(decl) if isinstance(n, ast.FnCall)
    )


def fn_structural_hash(decl: ast.FnDecl) -> str:
    """Hash the complete function subtree, spans included.

    ``Node.span`` is declared ``repr=False`` (and ``compare=False``),
    so ``repr(decl)`` alone is position-blind — a function shifted down
    a line would hash identically and replay cached output carrying
    stale line numbers (caught by
    ``test_span_shift_invalidates_conservatively``).  The span digest
    below restores position sensitivity: every node's span participates
    in source order.
    """
    spans = ",".join(
        (
            f"{n.span.line}:{n.span.column}:"
            f"{n.span.end_line}:{n.span.end_column}"
            if n.span is not None
            else "-"
        )
        for n in walk_nodes(decl)
    )
    return _sha(repr(decl) + "\x1f" + spans)


def callee_component(
    decl: ast.FnDecl,
    fn_map: dict[str, ast.FnDecl],
) -> str:
    """Hash the *interfaces* of every direct callee of *decl*.

    Interface = signature + contracts + type parameters — everything
    the caller's verification reads.  Callee bodies are excluded so a
    body-only edit in a callee does not invalidate its callers.
    Unresolvable names (builtins, module-qualified targets) contribute
    nothing here; the program context hash covers module contracts.
    """
    parts: list[str] = []
    for name in sorted(direct_callee_names(decl)):
        callee = fn_map.get(name)
        if callee is not None and callee is not decl:
            parts.append(
                f"{name}\x1f{callee.params!r}\x1f{callee.return_type!r}"
                f"\x1f{callee.contracts!r}\x1f{callee.forall_vars!r}"
            )
    return _sha("\x1e".join(parts))


def program_context_hash(
    program: ast.Program,
    timeout_ms: int,
    file: str | None,
    resolved_module_reprs: tuple[str, ...],
) -> str:
    """Hash everything outside the function bodies that verification
    reads: non-function declarations, imported-module contract
    surfaces, the solver timeout, and the file name (which is baked
    into every cached diagnostic's location).
    """
    non_fn = [
        repr(tld)
        for tld in program.declarations
        if not isinstance(tld.decl, ast.FnDecl)
    ]
    return _sha(
        "\x1e".join(non_fn)
        + f"\x1ftimeout={timeout_ms}\x1ffile={file!r}\x1f"
        + "\x1e".join(resolved_module_reprs)
    )


def fn_cache_key(
    decl: ast.FnDecl,
    fn_map: dict[str, ast.FnDecl],
    context_hash: str,
) -> str:
    """The complete invalidation key for one top-level function."""
    return _sha(
        fn_structural_hash(decl)
        + callee_component(decl, fn_map)
        + context_hash
    )


@dataclass
class FnCacheEntry:
    """One function's cached verification output.

    Replay appends these lists verbatim (the entries are treated as
    immutable after creation — nothing in the session or verifier
    mutates a recorded Diagnostic or ProofObligation) and adds the
    summary deltas to the run's summary.
    """

    diagnostics: list[Diagnostic]
    obligations: list[ProofObligation]
    tier1_delta: int
    tier3_delta: int
    total_delta: int


class DischargeCache:
    """Bounded FIFO map from fn_cache_key → FnCacheEntry.

    The bound is a backstop against pathological session lifetimes
    (an editor session re-verifying thousands of distinct program
    states); real projects hold one live entry per top-level function
    plus recently superseded ones.
    """

    def __init__(self, max_entries: int = 4096) -> None:
        self._max = max_entries
        self._entries: dict[str, FnCacheEntry] = {}

    def get(self, key: str) -> FnCacheEntry | None:
        return self._entries.get(key)

    def put(self, key: str, entry: FnCacheEntry) -> None:
        if any(o.status == "timeout" for o in entry.obligations):
            # Hard rail: solver-timeout outcomes are load-dependent;
            # never replay them.
            return
        if key not in self._entries and len(self._entries) >= self._max:
            oldest = next(iter(self._entries))
            del self._entries[oldest]
        self._entries[key] = entry

    def __len__(self) -> int:
        return len(self._entries)
