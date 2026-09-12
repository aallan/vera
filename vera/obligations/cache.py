"""Incremental invalidation + discharge cache (#222 Phase B).

The warm session (Phase A) re-verified every function on every call.
Phase B adds a per-function discharge cache behind the same API: a
function whose verification *inputs* are unchanged replays its cached
obligations and diagnostics instead of re-entering Z3 (the summary is
derived from the replayed obligations, #967).

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
2. **The interface CLOSURE** (``callee_component``): verifying ``f``
   checks each callee's preconditions at the call site and assumes its
   postconditions, so a callee *contract or signature* change must
   invalidate ``f``.  A callee *body* change must not — bodies are
   never read across the call boundary.

   The closure is not the direct callees alone.  A callee's CONTRACT
   may name further functions, and interpreting that contract reads
   THEIR interfaces too: with ``f`` declaring
   ``ensures(@Int.result == g(()))``, a caller of ``f`` reads ``g``'s
   contract without calling ``g`` at all.  Hashing direct callees only
   left such a caller replaying a proof after the fact it rested on had
   changed — warm reported `verified` where a fresh session reports
   `violated`/E500 (#1441).  So the component walks contract references
   transitively, and terminates on a visited set because contracts may
   be mutually recursive.
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

from dataclasses import dataclass, field, fields, is_dataclass
from typing import Any, Iterable, Iterator

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


def _type_reference_calls(
    type_exprs: Iterable[object],
    type_defs: dict[str, tuple[ast.TypeExpr, ...]],
    out: set[str],
) -> None:
    """Collect functions read while INTERPRETING *type_exprs*.

    A refinement predicate may call a function — ``{ @Int | @Int.0 < cap(()) }``
    — so reading a type reads that function's contract.  A NAMED type hides
    the predicate behind a declaration, so the walk resolves names through
    *type_defs* until it reaches the refinements themselves.  Both kinds of
    declaration carry one: a `type` alias names its target (and #1453 made
    alias CHAINS real), and a `data` declaration's constructor FIELDS are
    types the program reads whenever it builds or destructures a value
    (#1458 review) — a refinement is equally live behind either.

    ``seen`` terminates it, and a name enters it BEFORE its definition is
    pushed, so a recursive ``data List<T> { Nil, Cons(T, List<T>) }`` is
    walked once rather than forever.  An alias cycle is refused elsewhere
    (E-coded at check time), but this runs over whatever map it is handed
    and must be total regardless.
    """
    seen: set[str] = set()
    stack: list[object] = list(type_exprs)
    while stack:
        current = stack.pop()
        for node in walk_nodes(current):
            if isinstance(node, ast.FnCall):
                out.add(node.name)
            elif isinstance(node, ast.NamedType) and node.name not in seen:
                seen.add(node.name)
                stack.extend(type_defs.get(node.name, ()))


def interface_closure_names(
    decl: ast.FnDecl,
    fn_map: dict[str, ast.FnDecl],
    type_defs: dict[str, tuple[ast.TypeExpr, ...]],
) -> frozenset[str]:
    """Every function whose INTERFACE is read while verifying *decl*.

    The direct callees, plus everything reachable from there through what a
    caller READS of each: its CONTRACTS, and the refinement predicates of its
    SIGNATURE types.  A caller assumes a callee's postcondition, checks its
    precondition, and takes the refinements on its parameter and return types
    — so a function named in any of those is one whose contract the caller
    reads without calling it.

    Bodies are never followed: a body is read only by its own function's
    verification, which is the distinction that keeps a body-only edit from
    invalidating callers.

    Terminates on *seen* rather than on the call graph's shape: contracts may
    refer to each other in a cycle, and a caller of a cyclic pair reads both.
    """
    seen: set[str] = set()
    work: set[str] = set(direct_callee_names(decl))
    # EVERY type this declaration references, from ONE walk of its subtree —
    # not an enumeration of the positions a type can be written in.  A
    # refinement is read wherever its type is: on a parameter or a return,
    # on a `where` helper's signature, on a `let` annotation, and through an
    # ADT field at construction and at destructure.  Enumerating positions
    # left four of those out, each a warm-clean replay where a fresh session
    # refutes (#1458 review), and would leave the next position out too; a
    # walk covers a position added later by construction.
    #
    # The other two routes cannot reach these: a `NamedType` is not a call,
    # so `direct_callee_names` sees nothing through it, and neither a
    # `where` helper nor a type declaration is in `fn_map`, so the walk
    # below never resolves the name at all.
    referenced_types = [
        node for node in walk_nodes(decl) if isinstance(node, ast.TypeExpr)
    ]
    _type_reference_calls(referenced_types, type_defs, work)
    todo = list(work)
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        callee = fn_map.get(name)
        if callee is None:            # builtin, or module-qualified
            continue
        found: set[str] = set()
        for contract in callee.contracts:
            found.update(
                n.name for n in walk_nodes(contract)
                if isinstance(n, ast.FnCall)
            )
        _type_reference_calls(
            (*callee.params, callee.return_type), type_defs, found)
        todo.extend(n for n in found if n not in seen)
    return frozenset(seen)


def callee_component(
    decl: ast.FnDecl,
    fn_map: dict[str, ast.FnDecl],
    type_defs: dict[str, tuple[ast.TypeExpr, ...]],
) -> str:
    """Hash the *interfaces* of everything *decl*'s verification reads.

    Interface = signature + contracts + type parameters — everything
    the caller's verification reads.  Callee bodies are excluded so a
    body-only edit in a callee does not invalidate its callers.
    Unresolvable names (builtins, module-qualified targets) contribute
    nothing here; the program context hash covers module contracts.

    Over the CLOSURE rather than the direct callees: see this module's
    header, and #1441 for the stale replay that distinguishes them.
    """
    parts: list[str] = []
    for name in sorted(
            interface_closure_names(decl, fn_map, type_defs)):
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
    resolved_module_keys: tuple[str, ...],
) -> str:
    """Hash everything outside the function bodies that verification
    reads: non-function declarations, imported-module surfaces, the
    solver timeout, and the file name (which is baked into every
    cached diagnostic's location).

    *resolved_module_keys* are stable per-module digests supplied by
    the session — (module path, source hash) pairs rather than
    ``repr(ResolvedModule)``, which would bake in absolute filesystem
    paths (canonicalisation-sensitive) and the full parsed AST
    (expensive, and derived from the source anyway).
    """
    non_fn = [
        repr(tld)
        for tld in program.declarations
        if not isinstance(tld.decl, ast.FnDecl)
    ]
    return _sha(
        "\x1e".join(non_fn)
        + f"\x1ftimeout={timeout_ms}\x1ffile={file!r}\x1f"
        + "\x1e".join(resolved_module_keys)
    )


def fn_cache_key(
    decl: ast.FnDecl,
    fn_map: dict[str, ast.FnDecl],
    context_hash: str,
    type_defs: dict[str, tuple[ast.TypeExpr, ...]],
) -> str:
    """The complete invalidation key for one top-level function."""
    return _sha(
        fn_structural_hash(decl)
        + callee_component(decl, fn_map, type_defs)
        + context_hash
    )


@dataclass
class FnCacheEntry:
    """One function's cached verification output.

    Replay appends these lists verbatim (the entries are treated as
    immutable after creation — nothing in the session or verifier
    mutates a recorded Diagnostic or ProofObligation).  The run's
    :class:`~vera.verifier.VerifySummary` is *derived* from the assembled
    obligation stream at report-assembly time (#967), so no per-function
    summary deltas are cached — the cached ``obligations`` are the count.

    ``result_disclosed`` is the one datum that is NOT recoverable from the
    two lists (#1407): a function that merely hands on a disclosed value
    contributes no obligation saying so, and the cold path collects it while
    translating the body — which a replay does not do.  Left uncached, a
    replayed wrapper would drop out of the disclosed set and the warm run
    would prove at Tier 1 what the cold run demotes.

    It is the slice's WHOLE contribution — every key `_verify_fn` added to
    `ContractVerifier._result_disclosed_fns` while verifying this
    declaration, mapped to the import sites a caller's demotion should cite
    (#1418 review F2).  A bool about the top-level name was not enough:
    verifying a declaration also verifies its `where` helpers, and a helper
    that forwards a disclosed value is never itself a `decl.name` in the
    session's loop, so the warm disclosed set omitted it and the fixpoint
    settled one hop early — warm proving at Tier 1 exactly what cold demoted,
    on one of the ten spellings.  Caching the contribution rather than a fact
    about the name means a future kind of contributor is carried by existing
    code instead of needing a new field.  An empty dict is a slice that
    contributed nothing.
    """

    diagnostics: list[Diagnostic]
    obligations: list[ProofObligation]
    result_disclosed: dict[str, list[Any]] = field(default_factory=dict)


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
