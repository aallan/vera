"""Reconcile the verifier's runtime-guard claims with the checks code
generation emits (the audit's T2a).

A ``tier3`` obligation says its property is checked at run time, and
``vera verify`` counts it in ``tier3_runtime``.  The verifier and code
generation decide that separately: ``vera compile`` never reads the
verifier's result, so the status is a prediction about a module nothing
compares it with.  Both halves already leave a per-site record —
:class:`~vera.obligations.core.ProofObligation` for every obligation the
verifier discharged, :class:`~vera.trap_registry.EmittedCheck` for every
check the compiled module holds — and :func:`reconcile` joins them:

* ``recorded_unguarded`` — a record whose status claims a runtime check
  (``tier3``, ``timeout``) that no emitted check answers.  The claim is
  false, so ``vera verify`` reports it as an error (E541).
* ``guarded_unrecorded`` — an emitted check that no record accounts for:
  either no record of its kind stands at its site, or the only one says
  the site has no guard (``tier3_unguarded``).  The value is checked, but
  the account omits the check, so it is a warning (W004).
* ``no_mapping`` — a record or check the join cannot place: a record
  located at no node of the program, a check at a node of a class no rule
  below covers, a record of a kind no emitter serves.  Reported under the
  code of its direction (E541 for a record, W004 for a check), never
  skipped, so a gap in the join is as loud as a gap in the module.

Which records a check answers
-----------------------------

The kinds a check is the runtime half of are its emitter's row in
:data:`~vera.trap_registry.TRAP_EMITTERS` (``TrapEmitter.obligations``),
read as data rather than restated.  Where the check stands is the node its
emitter handed :meth:`~vera.wasm.context.WasmContext._emit_trap`, whose
span the per-module record keeps, and the class of that node decides which
record sites the check answers.  The verifier locates each record at the
node its expression text comes from, or at the call a measure or a
precondition is evaluated at (``ContractVerifier._evaluation_site``).

=================  ====================================  =====================================
Location class     Emitters that locate a check there    Records the check answers
=================  ====================================  =====================================
``clause``         ``codegen/contracts.py``:             a record of its kinds at the clause;
                   ``_compile_preconditions``,           and, for a ``requires``, the
                   ``_compile_postconditions``,          ``call_pre`` record at each call
                   ``_compile_decreases_entry``,         reaching its function that quotes
                   ``_dec_self_tail_prefix``             that precondition
                   (``at=contract``)
``parameter``      ``codegen/functions.py`` and          a record at the place its path names
                   ``codegen/closures.py`` boundary      inside the matching argument of a
                   guards (``at=param_te``)              call that reaches the function
                                                         (``_reached_decl``)
``return``         ``codegen/contracts.py`` and          a record at the place its path names
                   ``codegen/closures.py`` return        inside the function's body
                   guards (``at=...return_type``)
``binder``         ``wasm/data.py`` destructure and      a record at the value the binder
                   pattern guards (``at=te``,            takes apart, or at the field it
                   ``at=pattern``, ``at=sub_pat``);      binds where that value is a
                   a refined ``let``'s guard             construction the verifier sees into
                   (``at=stmt``)                         (:func:`_binder_value`)
``value``          every guard handed the value it       a record at the value; and, as one
                   checks or the operation it performs   arm, a record at a join the value is
                   (a measure component's range check    an arm of, once every arm that can
                   included)                             break the property has its check
``prelude``        a check inside a prelude or           none: the verifier records no
                   built-in function's body              obligation such a check answers
=================  ====================================  =====================================

A record and a check with the same span always pair.  ``state_decl`` is
excluded: its record is violated-or-absent, and no runtime check stands
for it (:data:`EXCLUDED_KINDS`).

One check per obligation site
-----------------------------

A location can hold several checks — a signature's top-level predicate and
each of its components' and elements', a join's arms, a pattern's
binders — and each record must be answered by the check of its own site,
never a sibling's (PR #1630 review).  Three things keep them apart:

* **Paths.**  A signature's guards all stand at its type, so each names
  where inside the value it checks (``EmittedCheck.path``: ``Tuple.0`` for
  a component, ``array element`` for an element), and answers only the
  record at that place: where it is built, or the value the verifier could
  not see into and so records it at (:func:`_stands_for`).
* **Arms.**  A record at a join is answered by its arms' checks only when
  every arm has one, or is a ``nat_bind`` arm code generation decided
  narrows nothing (:func:`_left_unguarded`, its own record of that
  decision).
* **Matching.**  The records at one span (two narrowed fields of a scrutinee
  the verifier cannot see into are both recorded at it) are matched one to
  one with the sites the checks there stand for (:func:`_match_sites`), so
  one check never answers two records.  The copies of one check — in a
  generic's clones, spliced twice — are one site.

Where the verifier records one obligation for a whole value it cannot see
into (an opaque argument of a tuple-typed parameter), the join can match
that record with any of the value's component checks, and cannot tell a
partial set of them from a whole one: that needs the set of guarded
components, which only code generation's decomposition states (#1642).

Scope
-----

A record names a claim of THIS verification run, so every record that
claims a guard must find one, with one exception: a record inside a
function the module has no code for (a generic no program instantiates, a
function code generation dropped) is ``absent``: there is no code for the
claim to be about.  A check needs a record only where this run verified
the code it sits in: a prelude body is never verified, and an imported
module's body is verified by that module's own run, so its checks are
``out_of_scope`` here, unless the declaration is a generic this run
verified through its clone (its records carry the module's file).

The join is per SITE, not per clone: the verifier aggregates a generic's
instances into one record per source site (worst status first), so a
record stands for every clone and a check in any clone answers it.
"""

from __future__ import annotations

import re
from collections.abc import Iterable, Iterator
from dataclasses import dataclass, field, fields
from pathlib import Path
from typing import TYPE_CHECKING, Literal, get_args

from vera import ast, narrowing
from vera.errors import Diagnostic, SourceLocation, VeraError
from vera.obligations.core import ObligationKind, ProofObligation
from vera.trap_registry import TRAP_EMITTERS, EmittedCheck

if TYPE_CHECKING:
    from vera.typed import TypedProgram
    from vera.codegen.api import CompileResult
    from vera.resolver import ResolvedModule
    from vera.verifier import VerifyResult

MismatchKind = Literal["recorded_unguarded", "guarded_unrecorded", "no_mapping"]

#: The statuses that claim a runtime check: the ones ``tier3_runtime``
#: counts (CLAUDE.md's partition table, ``summarize``).
CLAIMS_GUARD: frozenset[str] = frozenset({"tier3", "timeout"})

#: The status that says the site has NO runtime check.  A check standing at
#: a site recorded this way contradicts its record.
DENIES_GUARD = "tier3_unguarded"

#: Obligation kinds with no guard concept, excluded from the join by name.
#: A ``state_decl`` record is violated-or-absent (``ObligationKind``'s own
#: comment): it is an E533 refusal, never a runtime check.
EXCLUDED_KINDS: frozenset[str] = frozenset({"state_decl"})


def _emitters_by_kind() -> dict[str, frozenset[str]]:
    """Every per-site emitter that answers each obligation kind, read off
    :data:`~vera.trap_registry.TRAP_EMITTERS`."""
    out: dict[str, set[str]] = {}
    for key, row in TRAP_EMITTERS.items():
        if not row.per_site:
            continue
        for kind in row.obligations:
            out.setdefault(kind, set()).add(key)
    return {kind: frozenset(keys) for kind, keys in out.items()}


#: Obligation kind -> the emitters whose checks are its runtime half.
EMITTERS_BY_KIND: dict[str, frozenset[str]] = _emitters_by_kind()

#: Every obligation kind the verifier records.
OBLIGATION_KINDS: frozenset[str] = frozenset(get_args(ObligationKind))


@dataclass(frozen=True)
class Mismatch:
    """One disagreement between the obligation records and the module."""

    kind: MismatchKind
    obligation: str
    """The record's kind, or the kinds the check is the runtime half of
    (comma-separated)."""

    file: str | None
    line: int
    column: int
    function: str
    """The record's function (``fn_name``), or the WASM function the check
    sits in."""

    status: str = ""
    """The record's status; empty for a check."""

    emitter: str = ""
    """The check's emitter (a :data:`TRAP_EMITTERS` key); empty for a
    record."""

    detail: str = ""
    """Why it is a mismatch, in words."""

    def to_dict(self) -> dict[str, object]:
        """A JSON-compatible form (field names as keys)."""
        return {
            "kind": self.kind,
            "obligation": self.obligation,
            "file": self.file,
            "line": self.line,
            "column": self.column,
            "function": self.function,
            "status": self.status,
            "emitter": self.emitter,
            "detail": self.detail,
        }


@dataclass(frozen=True, eq=False)
class EntryCall:
    """One call that reaches the function an entry check guards (a
    `requires` clause, a refined parameter's guard)."""

    callers: frozenset[str]
    """The module functions the call is written in: the function whose
    region of the source holds it, every clone of a generic one."""

    records: tuple[ProofObligation, ...]
    """The records at the call the check stands for: none where the
    verifier discharged the call's obligation and recorded nothing, as it
    does for the precondition of a call into a user function."""


@dataclass
class Reconciliation:
    """The join's whole result: the mismatches, and what agreed."""

    mismatches: list[Mismatch] = field(default_factory=list)
    pairs: list[tuple[ProofObligation, EmittedCheck]] = field(
        default_factory=list)
    """Every (record, check) the join paired, the check answering the
    record."""

    absent: list[ProofObligation] = field(default_factory=list)
    """Records claiming a guard inside a function the module has no code
    for."""

    out_of_scope: list[EmittedCheck] = field(default_factory=list)
    """Checks in code this run did not verify (prelude and imported
    bodies)."""

    answers: list[tuple[ProofObligation, EmittedCheck]] = field(
        default_factory=list)
    """Every (record, check) the join relates, whatever the record's status:
    the check stands for the record's site, or for one arm of the join the
    record stands at.  Wider than ``pairs`` in three ways: a record that
    claims no runtime check is related too; each of several records at one
    site is related to every check that site offers, before the one-to-one
    matching (:func:`_match_sites`) gives each its own; and an arm's check is
    related to the join's record whether or not every arm has one.  It is
    what ``vera test --distrust`` reads a trap against
    (``vera.tester._TrapIndex``)."""

    entry: list[EmittedCheck] = field(default_factory=list)
    """The checks a function makes on entry for the call that entered it:
    each `requires` clause and each refined parameter's guard.  Each stands
    for the records at the calls that reach the function, never for one of
    the function's own."""

    entry_calls: dict[EmittedCheck, list[EntryCall]] = field(
        default_factory=dict)
    """Each entry check's calls: every call in the programs the run covered
    that reaches the check's function, with the module functions it is
    written in and the records at it the check stands for (``answers``,
    narrowed to the call).  A run of a function makes only the calls written
    in the functions it reaches, so what a trapped check stands for in that
    run is those calls' records, and a reached call with no record is a
    proof no record names (``vera.tester._TrapIndex``)."""


# =====================================================================
# The program, indexed by span
# =====================================================================

def _file_key(file: str | None) -> str | None:
    """One spelling per file: both halves name a file as they were handed
    it, so a relative and an absolute spelling of one path must meet."""
    if not file:
        return None
    try:
        return str(Path(file).resolve())
    except (OSError, RuntimeError):  # pragma: no cover — an unresolvable name
        return file


def _child_nodes(value: object) -> Iterator[ast.Node]:
    if isinstance(value, ast.Node):
        yield value
    elif isinstance(value, (tuple, list)):
        for item in value:
            yield from _child_nodes(item)


def _children(node: ast.Node) -> Iterator[ast.Node]:
    for f in fields(node):
        if f.name == "span":
            continue
        yield from _child_nodes(getattr(node, f.name))


Span4 = tuple[int, int, int, int]


class _Index:
    """Every spanned node of the programs the run covered, by file and span,
    with its parent, the function declaration it sits in, and the top-level
    declaration it belongs to; and, per file, its top-level functions."""

    def __init__(self) -> None:
        self.by_span: dict[tuple[str, Span4], list[ast.Node]] = {}
        self.parent: dict[int, ast.Node] = {}
        self.fn_of: dict[int, ast.FnDecl] = {}
        self.top_of: dict[int, ast.Node] = {}
        self.file_of: dict[int, str] = {}
        #: The files of the entry program (every top-level declaration in
        #: them is one this run verified).
        self.entry_files: set[str] = set()
        #: file -> name -> the top-level functions it declares by that name.
        self.top_fns: dict[str, dict[str, list[ast.FnDecl]]] = {}
        #: A resolved module's path (`lib`, `vera.math`) -> its file.
        self.module_files: dict[tuple[str, ...], str] = {}
        #: The files of the modules the entry program imports directly: the
        #: ones whose public names a bare call there can reach (§8.6.4).
        self.direct_files: set[str] = set()
        self._keys: dict[str, str | None] = {}
        self._closures: dict[int, set[int]] = {}

    def key(self, file: str | None) -> str | None:
        """:func:`_file_key`, once per spelling."""
        if not file:
            return None
        if file not in self._keys:
            self._keys[file] = _file_key(file)
        return self._keys[file]

    def closure(self, node: ast.Node) -> set[int]:
        """:func:`_flow_closure`, once per node."""
        if id(node) not in self._closures:
            self._closures[id(node)] = _flow_closure(node)
        return self._closures[id(node)]

    def add(self, file: str | None, program: ast.Program, *,
            entry: bool, module_path: tuple[str, ...] | None = None,
            direct: bool = False) -> None:
        key = self.key(file)
        if key is None:
            return
        if entry:
            self.entry_files.add(key)
        if module_path is not None:
            self.module_files[module_path] = key
        if direct:
            self.direct_files.add(key)
        by_name = self.top_fns.setdefault(key, {})
        for tld in program.declarations:
            decl = tld.decl
            if isinstance(decl, ast.FnDecl):
                by_name.setdefault(decl.name, []).append(decl)
            self._walk(key, decl, None, None, decl)

    def _walk(self, key: str, node: ast.Node, parent: ast.Node | None,
              fn: ast.FnDecl | None, top: ast.Node) -> None:
        if isinstance(node, ast.FnDecl):
            fn = node
        nid = id(node)
        if parent is not None:
            self.parent[nid] = parent
        if fn is not None:
            self.fn_of[nid] = fn
        self.top_of[nid] = top
        self.file_of[nid] = key
        span = node.span
        if span is not None:
            self.by_span.setdefault(
                (key, (span.line, span.column, span.end_line, span.end_column)),
                [],
            ).append(node)
        for child in _children(node):
            self._walk(key, child, node, fn, top)

    def nodes_at(self, file: str | None, span: Span4) -> list[ast.Node]:
        key = self.key(file)
        if key is None:
            return []
        return self.by_span.get((key, span), [])


def _span_of(item: ProofObligation | EmittedCheck) -> Span4:
    return (item.line, item.column, item.end_line, item.end_column)


def _within(inner: Span4, outer: Span4) -> bool:
    return ((outer[0], outer[1]) <= (inner[0], inner[1])
            and (inner[2], inner[3]) <= (outer[2], outer[3]))


def _node_span(node: ast.Node) -> Span4 | None:
    sp = node.span
    if sp is None:
        return None
    return (sp.line, sp.column, sp.end_line, sp.end_column)


def _flow_closure(node: ast.Node) -> set[int]:
    """*node* and every value it joins, read through the ``"flow"`` forms
    both components descend (:func:`vera.narrowing.flow_arms`).  Never a
    construction's field, a call's argument or an operation's operand: each
    of those is a site of its own."""
    out: set[int] = set()
    todo = [node]
    while todo:
        cur = todo.pop()
        if id(cur) in out:
            continue
        out.add(id(cur))
        if isinstance(cur, ast.Expr):
            arms = narrowing.flow_arms(cur)
            if arms:
                todo.extend(arms)
    return out


# =====================================================================
# Store positions: where a value sits inside the value that holds it
# =====================================================================
#
# A path is one step per level, read from the outer value down: a
# constructor's field as ``"<Ctor>.<k>"`` (a tuple's component is
# ``"Tuple.<k>"``), an array literal's element as ``"array element"``.  A
# join's arm is no step: the arm IS the join's value when it is taken.
# These are the steps a signature's guard names in ``EmittedCheck.path``.

Step = str


def _store_step(index: _Index, node: ast.Node) -> tuple[ast.Node, Step | None] | None:
    """The value *node* is stored in (a constructor's field, an array
    element) or joined into (an arm of a ``"flow"`` form), with the step
    that names its place there (None for an arm), or None."""
    parent = index.parent.get(id(node))
    if isinstance(parent, ast.ConstructorCall):
        for k, arg in enumerate(parent.args):
            if arg is node:
                return parent, f"{parent.name}.{k}"
        return None
    if isinstance(parent, ast.ArrayLit):
        if any(e is node for e in parent.elements):
            return parent, "array element"
        return None
    if isinstance(parent, (ast.MatchArm, ast.HandlerClause)):
        if parent.body is not node:
            return None
        parent = index.parent.get(id(parent))
    if isinstance(parent, ast.Expr):
        arms = narrowing.flow_arms(parent)
        if arms and any(a is node for a in arms):
            return parent, None
    return None


def _path_below(
    index: _Index, root: ast.Node, node: ast.Node,
) -> tuple[Step, ...] | None:
    """The path from *root* down to *node* through stores and joins, or
    None when *node* is not a value *root* holds."""
    steps: list[Step] = []
    cur = node
    while cur is not root:
        up = _store_step(index, cur)
        if up is None:
            return None
        cur, step = up
        if step is not None:
            steps.append(step)
    return tuple(reversed(steps))


def _joins_above(index: _Index, node: ast.Node) -> Iterator[ast.Node]:
    """Every join *node*'s value is an arm of, innermost first: the
    ``"flow"`` forms whose value *node* can be."""
    cur = node
    while True:
        up = _store_step(index, cur)
        if up is None or up[1] is not None:
            return
        cur = up[0]
        yield cur


def _hides(node: ast.Node, step: Step) -> bool:
    """Whether *node*'s value can hide the place *step* names: some value it
    can be is not built here with that place.  The verifier records a
    component of a value it cannot see into at the value itself (a call, a
    slot), and one it can see into where the component is built; a join
    with one opaque arm has that arm's component recorded at the join (PR
    #1630 review, round 2)."""
    if not isinstance(node, ast.Expr):
        return True
    ctor, _, k = step.rpartition(".")
    for leaf in narrowing.value_leaves(node):
        if step == "array element" and isinstance(leaf, ast.ArrayLit):
            continue
        if (isinstance(leaf, ast.ConstructorCall) and leaf.name == ctor
                and k.isdigit() and int(k) < len(leaf.args)):
            continue
        return True
    return False


def _stands_for(
    check_path: tuple[Step, ...], record_path: tuple[Step, ...],
    rnode: ast.Node,
) -> bool:
    """Whether a check of the value at *check_path* is the one a record at
    *record_path* (whose node is *rnode*) needs: the same place, or a place
    inside a value the record's node hides, which the verifier records as
    that value."""
    if record_path == check_path:
        return True
    depth = len(record_path)
    return (depth < len(check_path) and check_path[:depth] == record_path
            and _hides(rnode, check_path[depth]))


# =====================================================================
# Where a check stands
# =====================================================================

LocationClass = Literal["clause", "parameter", "return", "binder", "value",
                        "prelude"]


@dataclass(frozen=True)
class _Located:
    """A check's place: its location class and the node it stands at."""

    where: LocationClass
    node: ast.Node | None
    owner: ast.Node | None = None
    """The function (`FnDecl` / `AnonFn`) a parameter or return belongs to,
    or the statement / match a binder takes apart."""

    position: int = -1
    """The parameter's index, or the destructure binding's."""

    steps: tuple[tuple[str, int], ...] = ()
    """For a match binder, the constructor fields from the arm's pattern
    down to the binder: ``MkPair(MkPair(@Int, _), _)``'s inner binder is
    ``(("MkPair", 0), ("MkPair", 0))``; empty for the arm's own binder."""


def _locate(index: _Index, check: EmittedCheck) -> _Located | None:
    """The location class of *check*, from the node its span names; None
    when no node of the program stands there, or none of a class a rule
    covers.  Several nodes can share one span (a block and its only
    expression); they are read innermost first, as a record's node is."""
    if check.prelude:
        return _Located("prelude", None)
    nodes = list(reversed(index.nodes_at(check.file, _span_of(check))))
    for node in nodes:
        if isinstance(node, ast.Contract):
            return _Located("clause", node)
    for node in nodes:
        if not isinstance(node, ast.TypeExpr):
            continue
        parent = index.parent.get(id(node))
        if isinstance(parent, (ast.FnDecl, ast.AnonFn)):
            if node is parent.return_type:
                return _Located("return", node, parent)
            for k, param in enumerate(parent.params):
                if node is param:
                    return _Located("parameter", node, parent, k)
        if isinstance(parent, ast.LetDestruct):
            for k, binding in enumerate(parent.type_bindings):
                if node is binding:
                    return _Located("binder", node, parent, k)
    for node in nodes:
        if isinstance(node, ast.Pattern):
            found = _pattern_steps(index, node)
            if found is not None:
                match, steps = found
                return _Located("binder", node, match, steps=steps)
    for node in nodes:
        if isinstance(node, ast.Expr):
            return _Located("value", node)
    for node in nodes:
        # A refined `let` is guarded at the statement itself
        # (`wasm/context.py` `_emit_bind_refine_guard(..., stmt, ...)`,
        # #765): it checks the value the statement binds.
        if isinstance(node, (ast.LetStmt, ast.LetDestruct)):
            return _Located("binder", node, node)
    return None


def _pattern_steps(
    index: _Index, pattern: ast.Node,
) -> tuple[ast.MatchExpr, tuple[tuple[str, int], ...]] | None:
    """The `match` whose arm pattern *pattern* is, or sits inside, with the
    constructor fields from that arm's pattern down to *pattern*."""
    steps: list[tuple[str, int]] = []
    cur: ast.Node = pattern
    while True:
        parent = index.parent.get(id(cur))
        if isinstance(parent, ast.MatchArm) and cur is parent.pattern:
            grand = index.parent.get(id(parent))
            if not isinstance(grand, ast.MatchExpr):
                return None
            return grand, tuple(reversed(steps))
        if not isinstance(parent, ast.ConstructorPattern):
            return None
        for k, sub in enumerate(parent.sub_patterns):
            if sub is cur:
                steps.append((parent.name, k))
                break
        else:  # pragma: no cover — a pattern's parent holds it
            return None
        cur = parent


# =====================================================================
# Calls
# =====================================================================

def _argument_site(
    index: _Index, node: ast.Node,
) -> tuple[ast.FnCall | ast.ModuleCall, int, tuple[Step, ...]] | None:
    """(the call, argument position, the path from the argument down to
    *node*) when *node* is an argument of a call or a value one stores or
    joins (a pipe ``a |> f(x)`` is the call ``f(a, x)`` from the transform
    on, so it needs no reading of its own here)."""
    steps: list[Step] = []
    cur: ast.Node = node
    while True:
        parent = index.parent.get(id(cur))
        if isinstance(parent, (ast.FnCall, ast.ModuleCall)):
            for k, arg in enumerate(parent.args):
                if arg is cur:
                    return parent, k, tuple(reversed(steps))
            return None
        up = _store_step(index, cur)
        if up is None:
            return None
        cur, step = up
        if step is not None:
            steps.append(step)


def _call_node(node: ast.Node) -> ast.FnCall | ast.ModuleCall | None:
    """The call a call site makes: the call itself (a pipe is that call
    from the transform on, so there is no stage to look through)."""
    if isinstance(node, (ast.FnCall, ast.ModuleCall)):
        return node
    return None


def _reached_decl(
    index: _Index, call: ast.FnCall | ast.ModuleCall,
) -> ast.FnDecl | None:
    """The declaration *call* reaches, or None when it reaches none of the
    program's (a built-in, a prelude function, an ambiguous name).

    A module call reaches the function of that name in the module its path
    names.  A bare call reaches, in order, a `where` helper of a function
    on its enclosing chain (or that function itself, recursing), its own
    file's top-level function, then the one top-level function of that name
    among the modules the call can see — for the entry program its direct
    imports (§8.6.4), for a module's body the other modules.  So two
    declarations sharing a name — a local function and an imported one, two
    functions' helpers — never stand for each other.
    """
    if isinstance(call, ast.ModuleCall):
        key = index.module_files.get(tuple(call.path))
        found = index.top_fns.get(key, {}).get(call.name, []) if key else []
        return found[0] if len(found) == 1 else None
    fn = index.fn_of.get(id(call))
    while fn is not None:
        for helper in fn.where_fns or ():
            if helper.name == call.name:
                return helper
        if fn.name == call.name:
            return fn
        owner = index.parent.get(id(fn))
        fn = owner if isinstance(owner, ast.FnDecl) else None
    key = index.file_of.get(id(call))
    local = index.top_fns.get(key, {}).get(call.name, []) if key else []
    if local:
        return local[0] if len(local) == 1 else None
    visible = (index.direct_files if key in index.entry_files
               else set(index.top_fns) - index.entry_files - {key})
    found = [decl for other in sorted(visible)
             for decl in index.top_fns.get(other, {}).get(call.name, [])]
    return found[0] if len(found) == 1 else None


# =====================================================================
# The join
# =====================================================================

class _Records:
    """The run's records, located in the program."""

    def __init__(self, index: _Index, records: Iterable[ProofObligation]):
        self.all = list(records)
        self.node: dict[int, ast.Node] = {}
        #: node id -> the records standing at it.
        self.at_node: dict[int, list[ProofObligation]] = {}
        for record in self.all:
            nodes = index.nodes_at(record.file, _span_of(record))
            if nodes:
                node = _record_node(record, nodes)
                self.node[id(record)] = node
                self.at_node.setdefault(id(node), []).append(record)

    def located(self, record: ProofObligation) -> ast.Node | None:
        return self.node.get(id(record))


def _record_node(record: ProofObligation, nodes: list[ast.Node]) -> ast.Node:
    """The node a record stands at, among the nodes sharing its span: the
    contract for a clause's own kind, else the innermost expression."""
    if record.kind in ("requires", "ensures", "decreases"):
        for node in nodes:
            if isinstance(node, ast.Contract):
                return node
    for node in reversed(nodes):
        if isinstance(node, ast.Expr):
            return node
    return nodes[-1]


#: The obligation site a check stands for, as the join compares sites: two
#: checks with one key are one site (the copies of a check in a generic's
#: clones, a check spliced twice), two keys are two sites.
SiteKey = tuple[object, ...]


def _site_key(
    index: _Index, located: _Located, check: EmittedCheck,
    record: ProofObligation, rnode: ast.Node | None,
) -> SiteKey | None:
    """The obligation site *check* stands for when it is the runtime half
    of *record* (whose node is *rnode*), or None when it is not."""
    if record.kind not in check.obligations:
        return None
    rfile = index.key(record.file)
    same_file = rfile is not None and rfile == index.key(check.file)
    if same_file and _span_of(record) == _span_of(check):
        return ("at", check.emitter, _span_of(check), check.path)
    if rnode is None:
        return None
    where = located.where
    if where == "clause":
        return _key_from_clause(index, located, check, record, rnode)
    if where == "parameter":
        return _key_from_parameter(index, located, check, rnode)
    if where == "return":
        return _key_from_return(index, located, check, rnode)
    if where == "binder" and same_file:
        return _key_from_binder(index, located, check, rnode)
    if where == "value":
        # A value check answers the record at its own node (above), through
        # its arm the record at a join it is an arm of (`_arm_coverage`),
        # and, standing in a `decreases` measure, the measure's evaluation
        # at a tail call (`_key_from_measure`).
        return _key_from_measure(index, located, check, record, rnode)
    # A prelude body's check answers no record: no prelude function's check
    # is the runtime half of an obligation the verifier records at a call.
    return None


def _key_from_clause(
    index: _Index, located: _Located, check: EmittedCheck,
    record: ProofObligation, rnode: ast.Node,
) -> SiteKey | None:
    clause = located.node
    # A `requires` is checked once, in its function's prologue
    # (`_compile_preconditions`), for every caller: the runtime half of each
    # `call_pre` recorded at a call to that function.  The record is
    # located at the call and quotes the precondition it is about.  Every
    # other record inside a clause (a call's precondition written in a
    # `requires`, a measure component) is answered at its own site.
    if record.kind == "call_pre" and isinstance(clause, ast.Requires):
        fn = index.fn_of.get(id(clause))
        call = _call_node(rnode)
        if (fn is not None and call is not None
                and _reached_decl(index, call) is fn
                and record.expr_text == ast.format_expr(clause.expr)):
            return ("clause", check.emitter, id(clause))
    return None


def _key_from_parameter(
    index: _Index, located: _Located, check: EmittedCheck, rnode: ast.Node,
) -> SiteKey | None:
    # A refined parameter is checked once, in its function's prologue
    # (`codegen/functions.py` `at=param_te`), for every caller: the runtime
    # half of the narrowing recorded at each call's argument, for the calls
    # that reach that function (`_reached_decl`), at the place inside the
    # argument the guard's path names; a closure's parameter has no
    # declaration a call names, so it answers no call site.
    owner = located.owner
    if not isinstance(owner, ast.FnDecl):
        return None
    found = _argument_site(index, rnode)
    if found is None:
        return None
    call, position, path = found
    if (position != located.position
            or _reached_decl(index, call) is not owner
            or not _stands_for(check.path, path, rnode)):
        return None
    return ("parameter", check.emitter, id(located.node), check.path)


def _key_from_return(
    index: _Index, located: _Located, check: EmittedCheck, rnode: ast.Node,
) -> SiteKey | None:
    # A refined return is checked once, in the epilogue
    # (`codegen/contracts.py` `at=decl.return_type`), on the value the body
    # returns: the narrowing the verifier records at the place inside the
    # body's value that the guard's path names.
    owner = located.owner
    if not isinstance(owner, (ast.FnDecl, ast.AnonFn)):
        return None
    path = _path_below(index, owner.body, rnode)
    if path is None or not _stands_for(check.path, path, rnode):
        return None
    return ("return", check.emitter, id(located.node), check.path)


def _enclosing_contract(index: _Index, node: ast.Node) -> ast.Contract | None:
    """The contract clause *node* is written in, or None outside every
    clause."""
    cur: ast.Node | None = node
    while cur is not None and not isinstance(cur, ast.FnDecl):
        if isinstance(cur, ast.Contract):
            return cur
        cur = index.parent.get(id(cur))
    return None


def _key_from_measure(
    index: _Index, located: _Located, check: EmittedCheck,
    record: ProofObligation, rnode: ast.Node,
) -> SiteKey | None:
    # Code generation evaluates a `decreases` measure on entry, on the
    # function's own arguments (`_compile_decreases_entry`), and before each
    # self tail call, on the call's arguments (`_dec_self_tail_prefix`): both
    # with the checks it spans at the measure's own nodes.  The verifier
    # records the entry's evaluation at those nodes, and the tail call's at
    # the call, quoting the measure's text (`ContractVerifier.
    # _evaluation_site`).  So a check at a node of a function's measure
    # answers the record at a call reaching that function which quotes the
    # node; each call is a site of its own.
    node = located.node
    if not isinstance(node, ast.Expr) or not isinstance(
            _enclosing_contract(index, node), ast.Decreases):
        return None
    fn = index.fn_of.get(id(node))
    call = _call_node(rnode)
    if (fn is None or call is None or _reached_decl(index, call) is not fn
            or record.expr_text != ast.format_expr(node)):
        return None
    return ("measure", check.emitter, id(call), _span_of(check), check.path)


def _binder_value(located: _Located) -> ast.Node | None:
    """The value a binder's record stands at: what the verifier records a
    bind's narrowing at.  A `let` binds its value.  A destructure binding,
    and a match binder one constructor below the arm's pattern, bind a
    field: the verifier records it at that field when the value taken apart
    is a construction it can see into, and otherwise at the value itself,
    as it records every binder below that depth."""
    owner = located.owner
    if isinstance(owner, ast.LetStmt):
        return owner.value
    if isinstance(owner, ast.LetDestruct):
        value: ast.Node = owner.value
        if (located.position >= 0
                and isinstance(value, ast.ConstructorCall)
                and len(value.args) == len(owner.type_bindings)):
            return value.args[located.position]
        return value
    if isinstance(owner, ast.MatchExpr):
        scrutinee = owner.scrutinee
        if (len(located.steps) == 1
                and isinstance(scrutinee, ast.ConstructorCall)
                and scrutinee.name == located.steps[0][0]
                and located.steps[0][1] < len(scrutinee.args)):
            return scrutinee.args[located.steps[0][1]]
        return scrutinee
    return None


def _key_from_binder(
    index: _Index, located: _Located, check: EmittedCheck, rnode: ast.Node,
) -> SiteKey | None:
    # A destructure or a pattern guards what it binds (`wasm/data.py`
    # `at=te` / `at=pattern` / `at=sub_pat`, and a refined `let`'s guard at
    # the statement, `_emit_bind_refine_guard(..., stmt, ...)`).
    value = _binder_value(located)
    if value is None or id(rnode) not in index.closure(value):
        return None
    return ("binder", check.emitter, id(located.node))


def _left_unguarded(
    compile_result: CompileResult,
) -> set[tuple[str | None, Span4]]:
    """(file, span) of every arm code generation decided needs no narrowing
    guard (``CompileResult.unguarded_return_leaves``): the narrowing-leaf
    descent's own decision, which reads a generic call's instantiation that
    no declaration states (PR #1630 review, round 2)."""
    return {(_file_key(file), span)
            for file, span in compile_result.unguarded_return_leaves}


# =====================================================================
# Which code the module holds, and which code this run verified
# =====================================================================

_WAT_FN_DEF_RE = re.compile(r"^\s*\(func \$:?([^\s()]+)", re.MULTILINE)


def _function_regions(
    compile_result: CompileResult,
) -> dict[tuple[str, int, int], frozenset[str]]:
    """(file, first line, last line) of every function the module defines,
    from the trap source map code generation keeps for each of them, with
    the module functions compiled from it — a clone under its generic's
    entry, as the record of checks reads it."""
    out: dict[tuple[str, int, int], set[str]] = {}
    source = compile_result.fn_source_map
    for match in _WAT_FN_DEF_RE.finditer(compile_result.wat):
        name = match.group(1)
        entry = source.get(name) or source.get(name.rsplit("$", 1)[0])
        if entry is None:
            continue
        key = _file_key(entry[0])
        if key is not None:
            out.setdefault((key, entry[1], entry[2]), set()).add(name)
    return {region: frozenset(names) for region, names in out.items()}


def _compiled_regions(
    compile_result: CompileResult,
) -> set[tuple[str, int, int]]:
    """The regions of :func:`_function_regions`, without their names."""
    return set(_function_regions(compile_result))


def _written_in(
    index: _Index, regions: dict[tuple[str, int, int], frozenset[str]],
    node: ast.Node,
) -> frozenset[str]:
    """The module functions *node* is written in: those of the innermost
    region that holds its line (a closure's, inside its function's), or
    none when no region holds it."""
    key = index.file_of.get(id(node))
    span = node.span
    if key is None or span is None:
        return frozenset()
    holding = [(end - start, names) for (rkey, start, end), names in regions.items()
               if rkey == key and start <= span.line <= end]
    if not holding:
        return frozenset()
    narrowest = min(extent for extent, _ in holding)
    return frozenset().union(
        *(names for extent, names in holding if extent == narrowest))


def _record_call(
    index: _Index, records: _Records, record: ProofObligation,
    where: str,
) -> ast.FnCall | ast.ModuleCall | None:
    """The call a record an entry check stands for sits at, by the check's
    class (*where*): for a `requires` clause the call its `call_pre` stands
    at, and for a refined parameter the call whose argument holds the
    narrowing, which stands at a place inside the argument and so at an
    inner call when the argument is one (PR #1754 review, CodeRabbit)."""
    rnode = records.located(record)
    if rnode is None:
        return None
    if where == "clause":
        return _call_node(rnode)
    found = _argument_site(index, rnode)
    return found[0] if found is not None else None


def _entry_calls(
    index: _Index, records: _Records,
    answers: list[tuple[ProofObligation, EmittedCheck]],
    entry_decls: dict[EmittedCheck, tuple[ast.FnDecl, str]],
    regions: dict[tuple[str, int, int], frozenset[str]],
) -> dict[EmittedCheck, list[EntryCall]]:
    """Each entry check's calls (``Reconciliation.entry_calls``): every call
    the index holds that reaches the check's function, each with the module
    functions it is written in and the records at it the check stands for."""
    calls: dict[int, list[ast.FnCall | ast.ModuleCall]] = {}
    for nodes in index.by_span.values():
        for node in nodes:
            if isinstance(node, (ast.FnCall, ast.ModuleCall)):
                reached = _reached_decl(index, node)
                if reached is not None:
                    calls.setdefault(id(reached), []).append(node)
    standing: dict[EmittedCheck, dict[int, list[ProofObligation]]] = {}
    for record, check in answers:
        if check not in entry_decls:
            continue
        call = _record_call(index, records, record, entry_decls[check][1])
        if call is not None:
            standing.setdefault(check, {}).setdefault(id(call), []).append(record)
    out: dict[EmittedCheck, list[EntryCall]] = {}
    for check, (decl, _) in entry_decls.items():
        at_call = standing.get(check, {})
        out[check] = [
            EntryCall(_written_in(index, regions, call),
                      tuple(at_call.get(id(call), ())))
            for call in calls.get(id(decl), [])
        ]
    return out


def _has_code(
    index: _Index, regions: set[tuple[str, int, int]], node: ast.Node,
) -> bool:
    """Whether the module holds code for the function *node* sits in (a
    node outside every function — a refinement predicate — always does:
    each guard of the type evaluates it)."""
    fn = index.fn_of.get(id(node))
    if fn is None or fn.span is None:
        return True
    key = index.file_of.get(id(fn))
    return key is not None and (key, fn.span.line, fn.span.end_line) in regions


def _verified_here(
    index: _Index, located_node: ast.Node | None,
    records_by_top: dict[int, int],
) -> bool:
    """Whether this run verified the declaration *located_node* sits in:
    every declaration of the entry program, and an imported one this run
    recorded obligations inside (a generic verified through its clone)."""
    if located_node is None:
        return False
    key = index.file_of.get(id(located_node))
    if key in index.entry_files:
        return True
    top = index.top_of.get(id(located_node))
    return top is not None and records_by_top.get(id(top), 0) > 0


# =====================================================================
# The entry points
# =====================================================================

def join(
    verify_result: VerifyResult,
    compile_result: CompileResult,
    *,
    program: ast.Program,
    file: str | None,
    resolved_modules: Iterable[ResolvedModule] = (),
) -> Reconciliation:
    """Join *verify_result*'s records with *compile_result*'s checks.

    *program* and *file* are the entry program the two were produced from,
    *resolved_modules* the modules it imports: the join locates both
    records and checks in them (see the module docstring).
    """
    index = _Index()
    # The entry program's own module path, when it declares one: a module
    # call written inside it (`ma::f(...)` in module `ma`) reaches its own
    # function through that path (PR #1630 review, CodeRabbit).
    index.add(file, program, entry=True,
              module_path=(tuple(program.module.path)
                           if program.module is not None else None))
    for module in resolved_modules:
        index.add(str(module.file_path), module.program, entry=False,
                  module_path=tuple(module.path), direct=module.direct)

    records = _Records(index, verify_result.obligations)
    checks = list(compile_result.emitted_checks)
    out = Reconciliation()
    regions = _compiled_regions(compile_result)

    records_by_top: dict[int, int] = {}
    for record in records.all:
        rnode = records.located(record)
        if rnode is not None:
            top = index.top_of.get(id(rnode))
            if top is not None:
                records_by_top[id(top)] = records_by_top.get(id(top), 0) + 1

    # A check answers only records of the kinds its emitter's row names.
    by_kind: dict[str, list[ProofObligation]] = {}
    for record in records.all:
        by_kind.setdefault(record.kind, []).append(record)

    #: Each entry check -> the function whose entry it guards, and the
    #: check's class (`parameter` or `clause`).
    entry_decls: dict[EmittedCheck, tuple[ast.FnDecl, str]] = {}
    #: record id -> the obligation sites the checks offer it, each with the
    #: checks standing for that site.
    offers: dict[int, dict[SiteKey, list[EmittedCheck]]] = {}
    #: record id at a join -> leaf id -> the arm checks covering that leaf.
    covered: dict[int, dict[int, list[EmittedCheck]]] = {}
    unrecorded: list[tuple[EmittedCheck, list[ProofObligation]]] = []
    for check in checks:
        located = _locate(index, check)
        if located is None:
            out.mismatches.append(_check_mismatch(
                "no_mapping", check,
                "a node of the program stands at the check's span, but no "
                "rule pairs a check standing at a node of its class"
                if index.nodes_at(check.file, _span_of(check)) else
                "no node of the program stands at the check's span"))
            continue
        if located.where == "parameter" or (
                located.where == "clause"
                and isinstance(located.node, ast.Requires)):
            out.entry.append(check)
            guarded = (located.owner if located.where == "parameter"
                       else index.fn_of.get(id(located.node)))
            if isinstance(guarded, ast.FnDecl):
                entry_decls[check] = (guarded, located.where)
        standing: list[ProofObligation] = []
        for kind in check.obligations:
            for record in by_kind.get(kind, ()):
                key = _site_key(index, located, check, record,
                                records.located(record))
                if key is not None:
                    offers.setdefault(id(record), {}).setdefault(
                        key, []).append(check)
                    standing.append(record)
        if located.where == "value" and located.node is not None:
            standing.extend(_arm_coverage(index, records, located.node, check,
                                          covered))
        if check.prelude or not _verified_here(
                index, located.node, records_by_top):
            out.out_of_scope.append(check)
            continue
        unrecorded.append((check, standing))

    # A record at a join is answered by its arms' checks when every arm has
    # one, or is an arm code generation decided narrows nothing
    # (`_left_unguarded`): one site, the join.
    left_unguarded = _left_unguarded(compile_result)
    unchecked_arm: dict[int, ast.Expr] = {}
    for record in records.all:
        leaves_covered = covered.get(id(record))
        rnode = records.located(record)
        if not leaves_covered or not isinstance(rnode, ast.Expr):
            continue
        missing = [leaf for leaf in narrowing.value_leaves(rnode)
                   if id(leaf) not in leaves_covered
                   and not (record.kind == "nat_bind"
                            and (index.file_of.get(id(leaf)),
                                 _node_span(leaf)) in left_unguarded)]
        if missing:
            unchecked_arm[id(record)] = missing[0]
            continue
        offers.setdefault(id(record), {})[("arms", id(rnode))] = [
            c for found in leaves_covered.values() for c in found]

    # The relation itself, every record with every check standing for its
    # site or for an arm of its join, before the matching below picks one
    # site per record.
    for record in records.all:
        related: dict[int, EmittedCheck] = {}
        for site_checks in (*offers.get(id(record), {}).values(),
                            *covered.get(id(record), {}).values()):
            for check in site_checks:
                related.setdefault(id(check), check)
        out.answers.extend((record, check) for check in related.values())
    out.entry_calls = _entry_calls(index, records, out.answers, entry_decls,
                                   _function_regions(compile_result))

    for check, standing in unrecorded:
        if any(record.status != DENIES_GUARD for record in standing):
            continue
        out.mismatches.append(_check_mismatch(
            "guarded_unrecorded", check,
            "the only record at the site says it has no runtime check "
            "(tier3_unguarded)" if standing else
            "this run recorded no obligation of that kind at the site"))

    answered, shortfall = _match_sites(records.all, offers)
    for record in records.all:
        if record.status not in CLAIMS_GUARD or record.kind in EXCLUDED_KINDS:
            continue
        found = answered.get(id(record))
        if found:
            out.pairs.extend((record, check) for check in found)
            continue
        rnode = records.located(record)
        if record.kind not in EMITTERS_BY_KIND:
            out.mismatches.append(_record_mismatch(
                "no_mapping", record,
                "no emitter in vera.trap_registry.TRAP_EMITTERS answers "
                "this obligation kind"))
        elif rnode is None:
            out.mismatches.append(_record_mismatch(
                "no_mapping", record,
                "no node of the program stands at the record's span"))
        elif not _has_code(index, regions, rnode):
            out.absent.append(record)
        elif id(record) in unchecked_arm:
            leaf = unchecked_arm[id(record)]
            where = (f" at {leaf.span.line}:{leaf.span.column}"
                     if leaf.span is not None else "")
            out.mismatches.append(_record_mismatch(
                "recorded_unguarded", record,
                f"the module checks other arms of the join it is recorded "
                f"at, and holds no check on the arm{where}"))
        elif id(record) in shortfall:
            held, standing_here = shortfall[id(record)]
            out.mismatches.append(_record_mismatch(
                "recorded_unguarded", record,
                f"{standing_here} obligations of this kind stand at this "
                f"site, and the module holds checks for {held} of them"))
        else:
            out.mismatches.append(_record_mismatch(
                "recorded_unguarded", record,
                "the compiled module holds no check that answers it"))
    # One check-side mismatch per site: a check spliced twice into one
    # function (a handler clause inlined at each of its operation's calls)
    # is two entries of the record of checks and one disagreement.  A
    # record-side mismatch is one per record, so two records at one site
    # that are both unanswered stay two.
    seen: set[Mismatch] = set()
    kept: list[Mismatch] = []
    for m in out.mismatches:
        if not m.status and m in seen:
            continue
        seen.add(m)
        kept.append(m)
    out.mismatches = sorted(kept, key=_mismatch_order)
    return out


def _arm_coverage(
    index: _Index, records: _Records, node: ast.Node, check: EmittedCheck,
    covered: dict[int, dict[int, list[EmittedCheck]]],
) -> list[ProofObligation]:
    """Credit a value check with the leaves of *node* at every join above
    it whose record is of one of its kinds; return those records.

    Code generation guards a narrowing pushed down a join at each arm that
    narrows (``_collect_narrowing_return_leaves``), where the verifier
    records the join once.  The check stands for its own arm only: the
    join's record is answered once every arm that can break the property
    has a check (:func:`_left_unguarded`), so a missing arm guard is never
    covered by a sibling arm's."""
    if not isinstance(node, ast.Expr):
        return []
    leaves = narrowing.value_leaves(node)
    found: list[ProofObligation] = []
    for join_node in _joins_above(index, node):
        for record in records.at_node.get(id(join_node), ()):
            if (record.kind not in check.obligations
                    or index.key(record.file) != index.key(check.file)):
                continue
            arms = covered.setdefault(id(record), {})
            for leaf in leaves:
                arms.setdefault(id(leaf), []).append(check)
            found.append(record)
    return found


def _match_sites(
    all_records: list[ProofObligation],
    offers: dict[int, dict[SiteKey, list[EmittedCheck]]],
) -> tuple[dict[int, list[EmittedCheck]],
           dict[int, tuple[int, int]]]:
    """Match the records at each site with the obligation sites the checks
    there stand for, one to one.

    The records of one kind at one span are indistinguishable to the join
    (an opaque scrutinee's two narrowed fields are recorded at the
    scrutinee, twice), so each needs a site of its own: one check never
    answers two of them, and a missing one cannot hide behind its sibling.
    A record that claims no runtime check is matched first, so where the
    sites fall short the shortfall lands on the claims, which is the
    direction that reports it.  Returns each answered record's checks (all
    that offer it a site), and for each record left over (held sites,
    records at its site)."""
    groups: dict[tuple[object, ...], list[ProofObligation]] = {}
    for record in all_records:
        groups.setdefault(
            (record.file, record.kind, *_span_of(record)), []).append(record)
    answered: dict[int, list[EmittedCheck]] = {}
    shortfall: dict[int, tuple[int, int]] = {}
    for group in groups.values():
        ordered = sorted(group, key=lambda r: r.status in CLAIMS_GUARD)
        owner: dict[SiteKey, ProofObligation] = {}

        def assign(record: ProofObligation, seen: set[SiteKey]) -> bool:
            for key in offers.get(id(record), {}):
                if key in seen:
                    continue
                seen.add(key)
                holder = owner.get(key)
                if holder is None or assign(holder, seen):
                    owner[key] = record
                    return True
            return False

        for record in ordered:
            assign(record, set())
        # An answered record is paired with every check offering it a site:
        # the one its site was matched to, and any surplus (a guard at entry
        # and at each tail call, both checking one measure).
        for record in {id(r): r for r in owner.values()}.values():
            answered[id(record)] = [
                check for found in offers[id(record)].values()
                for check in found]
        sites = len({key for record in group
                     for key in offers.get(id(record), {})})
        for record in group:
            if id(record) not in answered and offers.get(id(record)):
                shortfall[id(record)] = (sites, len(group))
    return answered, shortfall


def _check_mismatch(
    kind: MismatchKind, check: EmittedCheck, detail: str,
) -> Mismatch:
    return Mismatch(
        kind=kind, obligation=",".join(check.obligations), file=check.file,
        line=check.line, column=check.column, function=check.function,
        emitter=check.emitter, detail=detail,
    )


def _record_mismatch(
    kind: MismatchKind, record: ProofObligation, detail: str,
) -> Mismatch:
    return Mismatch(
        kind=kind, obligation=record.kind, file=record.file,
        line=record.line, column=record.column,
        function=(f"{record.owner}.{record.fn_name}" if record.owner
                  else record.fn_name),
        status=record.status, detail=detail,
    )


def _mismatch_order(m: Mismatch) -> tuple[str, int, int, str, str]:
    return (m.file or "", m.line, m.column, m.kind, m.obligation)


def reconcile(
    verify_result: VerifyResult,
    compile_result: CompileResult,
    *,
    program: ast.Program,
    file: str | None,
    resolved_modules: Iterable[ResolvedModule] = (),
) -> list[Mismatch]:
    """Every mismatch between *verify_result*'s records and the checks
    *compile_result* holds (see :func:`join` for the arguments)."""
    return join(
        verify_result, compile_result, program=program, file=file,
        resolved_modules=resolved_modules,
    ).mismatches


# =====================================================================
# Diagnostics
# =====================================================================

def mismatch_diagnostics(
    mismatches: Iterable[Mismatch], sources: dict[str, str],
) -> list[Diagnostic]:
    """One diagnostic per mismatch: E541 (an error) for a record whose
    runtime-check claim the module does not answer, W004 (a warning) for a
    check no record accounts for.  A ``no_mapping`` takes the code of its
    direction — a record the join cannot place is a claim it could not
    confirm, a check it cannot place one it could not account for — and
    says so in its description.  *sources* maps each file to its text, for
    the source line."""
    texts = {_file_key(f): text.splitlines() for f, text in sources.items()}
    out: list[Diagnostic] = []
    for m in mismatches:
        lines = texts.get(_file_key(m.file), [])
        source_line = lines[m.line - 1] if 1 <= m.line <= len(lines) else ""
        location = SourceLocation(file=m.file, line=m.line, column=m.column)
        if m.status:
            what = (
                f"but {m.detail}" if m.kind == "recorded_unguarded" else
                f"and the reconciliation cannot place it: {m.detail}"
            )
            out.append(Diagnostic(
                description=(
                    f"The '{m.obligation}' obligation in '{m.function}' is "
                    f"recorded as checked at run time ({m.status}), {what}."
                ),
                location=location,
                source_line=source_line,
                rationale=(
                    "`vera verify` counts a `tier3` or `timeout` obligation as "
                    "runtime-guarded: code generation is meant to emit a check "
                    "that traps when the property fails.  The verifier and "
                    "code generation decide that separately, and this run "
                    "compiled the program and found no emitted check for "
                    "this obligation, so the claim is not true of the "
                    "compiled module."
                    if m.kind == "recorded_unguarded" else
                    "`vera verify` counts a `tier3` or `timeout` obligation as "
                    "runtime-guarded: code generation is meant to emit a check "
                    "that traps when the property fails.  This run "
                    "compiled the program but could not relate this record "
                    "to the program or to any emitter, so it cannot say "
                    "whether the module checks it: the claim is unconfirmed, "
                    "which the reconciliation reports rather than skips."
                ),
                fix=(
                    "This is a disagreement inside the compiler, not an error "
                    "in the program: report it with the program attached.  "
                    "Until it is fixed, do not rely on a runtime check here — "
                    "make the property provable instead, with a `requires` "
                    "clause or an `if` guard around the operation, so it is "
                    "discharged at Tier 1."
                ),
                spec_ref='Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
                severity="error",
                error_code="E541",
                tier=3,
            ))
            continue
        what = (
            m.detail if m.kind == "guarded_unrecorded" else
            f"the reconciliation cannot place the check: {m.detail}"
        )
        out.append(Diagnostic(
            description=(
                f"The compiled module checks this site in '{m.function}' "
                f"(the runtime half of '{m.obligation}'), but {what}."
            ),
            location=location,
            source_line=source_line,
            rationale=(
                "Every runtime check in the compiled module is meant to be "
                "the runtime half of an obligation `vera verify` recorded, so "
                "that the verification summary accounts for each check the "
                "program performs.  The module checks this site at run time "
                "and no record of this run answers the check, so the summary "
                "omits it.  The check still runs: it is a dead guard on a "
                "value the checker already typed, a check at a site that "
                "cannot fail, or a gap in the verifier's accounting."
                if m.kind == "guarded_unrecorded" else
                "Every runtime check in the compiled module is meant to be "
                "the runtime half of an obligation `vera verify` recorded.  "
                "This run could not relate this check to a site of the "
                "program it knows how to pair, so it cannot say which record "
                "accounts for it; the check still runs, and the "
                "reconciliation reports the gap rather than skips it."
            ),
            spec_ref='Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
            severity="warning",
            error_code="W004",
        ))
    return out


def report_dict(reconciliation: Reconciliation | None) -> dict[str, object]:
    """The ``reconciliation`` object of ``vera verify --json``: whether the
    module compiled, the counts, and every mismatch.  None stands for a
    compile that failed, which leaves nothing to join."""
    if reconciliation is None:
        return {"compiled": False, "matched": 0, "recorded_unguarded": 0,
                "guarded_unrecorded": 0, "no_mapping": 0, "absent": 0,
                "out_of_scope": 0, "mismatches": []}
    kinds = [m.kind for m in reconciliation.mismatches]
    return {
        "compiled": True,
        "matched": len({id(record) for record, _ in reconciliation.pairs}),
        "recorded_unguarded": kinds.count("recorded_unguarded"),
        "guarded_unrecorded": kinds.count("guarded_unrecorded"),
        "no_mapping": kinds.count("no_mapping"),
        "absent": len(reconciliation.absent),
        "out_of_scope": len(reconciliation.out_of_scope),
        "mismatches": [m.to_dict() for m in reconciliation.mismatches],
    }


def summary_line(reconciliation: Reconciliation) -> str | None:
    """The one-line reconciliation summary ``vera verify`` prints after the
    verification summary, or None when the program claims no runtime check
    (Tier 3), which leaves nothing to say."""
    matched = len({id(record) for record, _ in reconciliation.pairs})
    claims = matched + len(reconciliation.absent) + sum(
        1 for m in reconciliation.mismatches if m.status)
    if not claims:
        return None
    text = (
        f"Reconciliation: {matched} of {claims} runtime checks (Tier 3) "
        f"found in the compiled module"
    )
    if reconciliation.absent:
        text += (
            f", {len(reconciliation.absent)} in a function the module holds "
            f"no code for"
        )
    return text


# =====================================================================
# The pipeline, as `vera verify` runs it
# =====================================================================

#: The code generation refusal a join is skipped for rather than failed on:
#: a program holding typed holes (E614).  `vera check` accepts one with a
#: W001 per hole, and the verifier verifies the rest of it; code generation
#: compiles nothing until every hole is filled, so there is no module to
#: join, and refusing the verification would take the hole workflow's
#: feedback away (spec Section 4.17).
SKIPPED_FOR = "E614"


@dataclass
class Reconciled:
    """What ``vera verify`` adds to a verification unless
    ``--no-reconcile``: the program compiled as ``vera compile`` compiles
    it, the join, and the diagnostics the two give."""

    compile_result: CompileResult
    reconciliation: Reconciliation | None
    """None when code generation refused the program: nothing to join."""

    diagnostics: list[Diagnostic]
    """The compile's own diagnostics, then one per mismatch
    (:func:`mismatch_diagnostics`); for a program holding typed holes, the
    one W005 warning that says the join was skipped."""

    skipped: str = ""
    """Why the join did not run although ``--no-reconcile`` was not given:
    the program holds typed holes.  Empty when it ran, or the compile
    refused the program for another reason."""

    def report(self) -> dict[str, object]:
        """The ``reconciliation`` object of ``vera verify --json``."""
        if self.skipped:
            return {"skipped": self.skipped}
        return report_dict(self.reconciliation)


def compile_for_reconcile(
    typed: TypedProgram, source: str, file: str | None,
) -> CompileResult:
    """Compile the typed program exactly as ``vera compile`` does."""
    from vera.codegen import compile as codegen_compile

    return codegen_compile(typed, source=source, file=file)


def _holes_skip(holes: list[Diagnostic], source: str) -> Diagnostic:
    """The W005 warning for a join skipped because the program holds typed
    holes, located at the first."""
    first = holes[0]
    lines = source.splitlines()
    line = first.location.line
    count = (f"{len(holes)} typed holes" if len(holes) > 1
             else "a typed hole")
    return Diagnostic(
        description=(
            f"The runtime checks are not reconciled: the program holds "
            f"{count}, and code generation compiles a program only once every "
            f"hole is filled (E614), so there is no compiled module to hold "
            f"its Tier 3 claims to."
        ),
        location=SourceLocation(
            file=first.location.file, line=line, column=first.location.column),
        source_line=lines[line - 1] if 1 <= line <= len(lines) else "",
        rationale=(
            "`vera verify` compiles the program in process and joins each "
            "runtime-check claim (`tier3`, `timeout`) with the check the "
            "compiled module holds for it.  A typed hole has no runtime "
            "behaviour, so code generation refuses the program, and the "
            "verification of the rest of it stands on its own: every proof "
            "and every disclosure above is the verifier's, and no Tier 3 "
            "claim has been held to a compiled check."
        ),
        fix=(
            "Fill each hole with an expression of the type its W001 warning "
            "names; `vera verify` then compiles the program and reconciles "
            "its runtime checks."
        ),
        spec_ref='Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
        severity="warning",
        error_code="W005",
    )


def reconcile_verified(
    typed: TypedProgram,
    source: str,
    file: str | None,
    verify_result: VerifyResult,
) -> Reconciled:
    """Compile the typed program and join *verify_result*'s records with the
    checks the module holds, as ``vera verify`` does unless
    ``--no-reconcile``.

    A program code generation refuses leaves nothing to join: its refusal
    is the answer, with one exception, a program holding typed holes, for
    which the join is skipped with a W005 warning (:data:`SKIPPED_FOR`)."""
    program, resolved_modules = typed.program, typed.modules
    compiled = compile_for_reconcile(typed, source, file)
    holes = [d for d in compiled.diagnostics
             if d.severity == "error" and d.error_code == SKIPPED_FOR]
    if holes:
        return Reconciled(
            compiled, None, [_holes_skip(holes, source)],
            skipped="the program holds typed holes, which code generation "
                    "refuses (E614)")
    diagnostics = list(compiled.diagnostics)
    if not compiled.ok:
        return Reconciled(compiled, None, diagnostics)
    joined = join(verify_result, compiled, program=program, file=file,
                  resolved_modules=resolved_modules)
    sources = {str(module.file_path): module.source
               for module in resolved_modules}
    if file is not None:
        sources[file] = source
    diagnostics += mismatch_diagnostics(joined.mismatches, sources)
    return Reconciled(compiled, joined, diagnostics)


@dataclass
class ReconcileRun:
    """One program through check, verify, compile and the join."""

    path: Path
    check_errors: list[str] = field(default_factory=list)
    compile_errors: list[str] = field(default_factory=list)
    program: ast.Program | None = None
    resolved_modules: list[ResolvedModule] = field(default_factory=list)
    verify_result: VerifyResult | None = None
    compile_result: CompileResult | None = None
    reconciliation: Reconciliation | None = None

    @property
    def mismatches(self) -> list[Mismatch]:
        """The join's mismatches; empty when the pipeline stopped early."""
        return [] if self.reconciliation is None else (
            self.reconciliation.mismatches)


def reconcile_file(
    path: str | Path, timeout_ms: int | None = None,
) -> ReconcileRun:
    """Check, verify, compile and join the program at *path*, in process,
    with the same calls ``vera verify`` makes.  A compile refusal, a typed
    hole's included, stops the run before the join."""
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse, read_source
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.typed import build
    from vera.verifier import verify

    p = Path(path)
    run = ReconcileRun(path=p)
    try:
        source = read_source(p)
        program = transform(parse(source, file=str(p)))  # pragma: no mutate — the label reaches only a refusal's location, and reconcile_file records its description
    except VeraError as exc:
        # A source that is not UTF-8 (E024), or a parse or transform
        # refusal, is the program's own: a stop before the join, as `vera
        # verify` reports it, never an exception.
        run.check_errors = [exc.diagnostic.description]
        return run
    resolver = ModuleResolver(_root=p.parent)
    resolved = resolver.resolve_imports(program, p)
    run.program, run.resolved_modules = program, resolved
    check_diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(p), resolved_modules=resolved,
    )
    run.check_errors = [
        d.description for d in resolver.errors + check_diags
        if d.severity == "error"
    ]
    if run.check_errors:
        return run
    typed = build(program, resolved, artifacts)
    run.verify_result = verify(typed, source, file=str(p),
                               timeout_ms=timeout_ms)
    reconciled = reconcile_verified(typed, source, str(p), run.verify_result)
    run.compile_result = reconciled.compile_result
    run.compile_errors = [
        d.description for d in run.compile_result.diagnostics
        if d.severity == "error"
    ]
    run.reconciliation = reconciled.reconciliation
    return run
