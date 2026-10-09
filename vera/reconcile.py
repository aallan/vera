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
  false, so ``vera verify --reconcile`` reports it as an error (E541).
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
  every arm has one, or cannot break the property: for ``nat_bind``, an arm
  no narrowing reaches, read from the program alone
  (:func:`_needs_no_check`).
* **Matching.**  The records at one span (two widened fields of a scrutinee
  the verifier cannot see into are both recorded at it) are matched one to
  one with the sites the checks there stand for (:func:`_match_sites`), so
  one check never answers two records.  The copies of one check — in a
  generic's clones, spliced twice — are one site.

Where the verifier records one obligation for a whole value it cannot see
into (an opaque argument of a tuple-typed parameter), the join can match
that record with any of the value's component checks, and cannot tell a
partial set of them from a whole one: that needs the set of guarded
components, which only code generation's decomposition states.

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
    from vera.checker.core import CheckArtifacts
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
    """Whether *node*'s value hides the place *step* names: no value it can
    be is built here with that place.  The verifier records a component of
    a value it cannot see into at the value itself (a call, a slot), and
    one it can see into where the component is built."""
    if not isinstance(node, ast.Expr):
        return True
    ctor, _, k = step.rpartition(".")
    for leaf in narrowing.value_leaves(node):
        if step == "array element" and isinstance(leaf, ast.ArrayLit):
            return False
        if (isinstance(leaf, ast.ConstructorCall) and leaf.name == ctor
                and k.isdigit() and int(k) < len(leaf.args)):
            return False
    return True


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
    joins, read through the pipe's desugaring (``a |> f(x)`` is
    ``f(a, x)``, ``narrowing``'s and code generation's one reading of it)."""
    steps: list[Step] = []
    cur: ast.Node = node
    while True:
        parent = index.parent.get(id(cur))
        if isinstance(parent, (ast.FnCall, ast.ModuleCall)):
            for k, arg in enumerate(parent.args):
                if arg is cur:
                    piped = _pipe_of_call(index, parent)
                    return parent, k + (1 if piped else 0), tuple(
                        reversed(steps))
            return None
        if (isinstance(parent, ast.BinaryExpr)
                and parent.op == ast.BinOp.PIPE and cur is parent.left
                and isinstance(parent.right, (ast.FnCall, ast.ModuleCall))):
            return parent.right, 0, tuple(reversed(steps))
        up = _store_step(index, cur)
        if up is None:
            return None
        cur, step = up
        if step is not None:
            steps.append(step)


def _pipe_of_call(index: _Index, call: ast.Node) -> bool:
    parent = index.parent.get(id(call))
    return (isinstance(parent, ast.BinaryExpr)
            and parent.op == ast.BinOp.PIPE and call is parent.right)


def _call_node(node: ast.Node) -> ast.FnCall | ast.ModuleCall | None:
    """The call a call site makes: the call itself, or the stage of a pipe
    (whose desugared call keeps the pipe's span)."""
    if isinstance(node, (ast.FnCall, ast.ModuleCall)):
        return node
    if (isinstance(node, ast.BinaryExpr) and node.op == ast.BinOp.PIPE
            and isinstance(node.right, (ast.FnCall, ast.ModuleCall))):
        return node.right
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
    # A value check answers the record at its own node (above) and, through
    # its arm, the record at a join it is an arm of (`_arm_coverage`).  A
    # prelude body's check answers no record: no prelude function's check
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


def _needs_no_check(index: _Index, leaf: ast.Expr, kind: str) -> bool:
    """Whether an arm of a join cannot break *kind*'s property, so the
    join's record needs no check on it: for ``nat_bind``, a value no
    narrowing reaches — a non-negative literal, a ``@Nat`` slot, a call of
    a declared ``@Nat`` function, and arithmetic over those (a subtraction
    with ``@Nat`` provenance is its own guarded site).  Read from the
    program alone, so a form whose type only the checker knows needs its
    check."""
    if kind != "nat_bind":
        return False

    def declared(call: ast.Expr) -> str | None:
        if not isinstance(call, (ast.FnCall, ast.ModuleCall)):
            return None
        decl = _reached_decl(index, call)
        ret = decl.return_type if decl is not None else None
        if isinstance(ret, ast.NamedType) and not ret.type_args:
            return ret.name
        return None

    def provenance(expr: ast.Expr) -> bool:
        if isinstance(expr, ast.SlotRef):
            return expr.type_name == "Nat"
        if isinstance(expr, (ast.FnCall, ast.ModuleCall)):
            return declared(expr) == "Nat"
        if isinstance(expr, ast.BinaryExpr):
            return provenance(expr.left) or provenance(expr.right)
        return False

    return (narrowing.is_static_nat_typed(leaf, declared)
            and not narrowing.has_underflow_leaf(leaf, provenance))


# =====================================================================
# Which code the module holds, and which code this run verified
# =====================================================================

_WAT_FN_DEF_RE = re.compile(r"^\s*\(func \$([^\s()]+)", re.MULTILINE)


def _compiled_regions(
    compile_result: CompileResult,
) -> set[tuple[str, int, int]]:
    """(file, first line, last line) of every function the module defines,
    from the trap source map code generation keeps for each of them —
    a clone under its generic's entry, as the record of checks reads it."""
    out: set[tuple[str, int, int]] = set()
    source = compile_result.fn_source_map
    for match in _WAT_FN_DEF_RE.finditer(compile_result.wat):
        name = match.group(1)
        entry = source.get(name) or source.get(name.rsplit("$", 1)[0])
        if entry is None:
            continue
        key = _file_key(entry[0])
        if key is not None:
            out.add((key, entry[1], entry[2]))
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

    # A record at a join is answered by its arms' checks when every arm that
    # can break the property has one (`_arm_coverage`): one site, the join.
    unchecked_arm: dict[int, ast.Expr] = {}
    for record in records.all:
        leaves_covered = covered.get(id(record))
        rnode = records.located(record)
        if not leaves_covered or not isinstance(rnode, ast.Expr):
            continue
        missing = [leaf for leaf in narrowing.value_leaves(rnode)
                   if id(leaf) not in leaves_covered
                   and not _needs_no_check(index, leaf, record.kind)]
        if missing:
            unchecked_arm[id(record)] = missing[0]
            continue
        offers.setdefault(id(record), {})[("arms", id(rnode))] = [
            c for found in leaves_covered.values() for c in found]

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
    has a check (:func:`_needs_no_check`), so a missing arm guard is never
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
    (an opaque scrutinee's two widened fields are recorded at the
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
                    "code generation decide that separately, and "
                    "`--reconcile` compiled this program and found no emitted "
                    "check for this obligation, so the claim is not true of "
                    "the compiled module."
                    if m.kind == "recorded_unguarded" else
                    "`vera verify` counts a `tier3` or `timeout` obligation as "
                    "runtime-guarded: code generation is meant to emit a check "
                    "that traps when the property fails.  `--reconcile` "
                    "compiled this program but could not relate this record "
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
                "`--reconcile` could not relate this check to a site of the "
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
    """The ``reconciliation`` object of ``vera verify --reconcile --json``:
    whether the module compiled, the counts, and every mismatch.  None
    stands for a compile that failed, which leaves nothing to join."""
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


def summary_line(reconciliation: Reconciliation) -> str:
    """The one-line reconciliation summary ``vera verify --reconcile``
    prints after the verification summary."""
    matched = len({id(record) for record, _ in reconciliation.pairs})
    claims = matched + len(reconciliation.absent) + sum(
        1 for m in reconciliation.mismatches if m.status)
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
# The pipeline, as `vera verify --reconcile` runs it
# =====================================================================

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


def compile_for_reconcile(
    program: ast.Program,
    source: str,
    file: str,
    resolved_modules: list[ResolvedModule],
    artifacts: CheckArtifacts,
) -> CompileResult:
    """Compile *program* exactly as ``vera compile`` does, with the
    checker's *artifacts*."""
    from vera.codegen import compile as codegen_compile

    return codegen_compile(
        program, source=source, file=file, resolved_modules=resolved_modules,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )


def reconcile_file(
    path: str | Path, timeout_ms: int | None = None,
) -> ReconcileRun:
    """Check, verify, compile and join the program at *path*, in process,
    with the same calls ``vera verify --reconcile`` makes."""
    from vera.checker import typecheck_with_artifacts
    from vera.parser import parse
    from vera.resolver import ModuleResolver
    from vera.transform import transform
    from vera.verifier import verify

    p = Path(path)
    run = ReconcileRun(path=p)
    source = p.read_text(encoding="utf-8")
    try:
        program = transform(parse(source, file=str(p)))
    except VeraError as exc:
        # A parse or transform refusal is the program's own: a stop before
        # the join, as `vera verify` reports it, never an exception.
        run.check_errors = [exc.diagnostic.description]
        return run
    resolver = ModuleResolver(_root=p.parent)
    resolved = resolver.resolve_imports(program, p)
    run.program, run.resolved_modules = program, resolved
    check_diags, artifacts = typecheck_with_artifacts(
        program, source, file=str(p), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    run.check_errors = [
        d.description for d in resolver.errors + check_diags
        if d.severity == "error"
    ]
    if run.check_errors:
        return run
    run.verify_result = verify(
        program, source, file=str(p), timeout_ms=timeout_ms,
        resolved_modules=resolved,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    run.compile_result = compile_for_reconcile(
        program, source, str(p), resolved, artifacts)
    run.compile_errors = [
        d.description for d in run.compile_result.diagnostics
        if d.severity == "error"
    ]
    if run.compile_errors:
        return run
    run.reconciliation = join(
        run.verify_result, run.compile_result, program=program,
        file=str(p), resolved_modules=resolved,
    )
    return run
