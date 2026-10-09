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
precondition is evaluated at (``ContractVerifier._evaluation_site``).  A
value's *store positions* below are the value, the arms it joins
(``narrowing.flow_arms``) and the fields and elements a construction there
stores: the positions the verifier's construction descent obligates, never
a call's argument or an operation's operand, which are sites of their own.

=================  ====================================  =====================================
Location class     Emitters that locate a check there    Records the check answers
=================  ====================================  =====================================
``clause``         ``codegen/contracts.py``:             a record of its kinds at the clause;
                   ``_compile_preconditions``,           the ``@Nat`` components
                   ``_compile_postconditions``,          ``_dec_bound_check_pairs`` checks,
                   ``_compile_decreases_entry``,         recorded where each is written inside
                   ``_dec_self_tail_prefix``,            its ``decreases``; and, for a
                   ``_dec_bound_check_pairs``            ``requires``, the ``call_pre`` record
                   (``at=contract``)                     at each call to its function quoting
                                                         that precondition
``parameter``      ``codegen/functions.py`` and          a record at a store position of the
                   ``codegen/closures.py`` boundary      matching argument of a call to the
                   guards (``at=param_te``)              function, by its declared name
``return``         ``codegen/contracts.py`` and          a record at a store position of the
                   ``codegen/closures.py`` return        function's body
                   guards (``at=...return_type``)
``binder``         ``wasm/data.py`` destructure and      a record at a store position of the
                   pattern guards (``at=te``,            value the binder takes apart: the
                   ``at=pattern``, ``at=sub_pat``);      component it binds when that value
                   a refined ``let`` or destructure's    is a construction, else the whole
                   guard (``at=stmt``)                   value or scrutinee
``value``          every guard handed the value it       a record at the value, at a join the
                   checks or the operation it performs   value is an arm of, or at an arm the
                                                         value joins; for a widening, a record
                                                         at the operation the value is an
                                                         operand of
``prelude``        a check inside a prelude or           a record at a call to that prelude
                   built-in function's body              function
=================  ====================================  =====================================

A record and a check with the same span always pair.  ``state_decl`` is
excluded: its record is violated-or-absent, and no runtime check stands
for it (:data:`EXCLUDED_KINDS`).

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
        self._closures: dict[tuple[int, bool], set[int]] = {}

    def key(self, file: str | None) -> str | None:
        """:func:`_file_key`, once per spelling."""
        if not file:
            return None
        if file not in self._keys:
            self._keys[file] = _file_key(file)
        return self._keys[file]

    def closure(self, node: ast.Node, *, stores: bool = False) -> set[int]:
        """:func:`_flow_closure`, once per node."""
        memo = (id(node), stores)
        if memo not in self._closures:
            self._closures[memo] = _flow_closure(node, stores=stores)
        return self._closures[memo]

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


def _flow_closure(node: ast.Node, *, stores: bool = False) -> set[int]:
    """*node* and every value it joins, read through the ``"flow"`` forms
    both components descend (:func:`vera.narrowing.flow_arms`).

    With *stores*, also every value a construction inside it stores — a
    constructor's field, an array literal's element — the positions the
    verifier's construction descent obligates a component at
    (``_descend_construction_container``).  Never a call's argument or an
    operation's operand: a narrowing written there is its own site, with its
    own guard."""
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
        if stores and isinstance(cur, ast.ConstructorCall):
            todo.extend(cur.args)
        if stores and isinstance(cur, ast.ArrayLit):
            todo.extend(cur.elements)
    return out


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
    """The parameter's index, or the binder's component index."""


def _locate(index: _Index, check: EmittedCheck) -> _Located | None:
    """The location class of *check*, from the node its span names; None
    when no node of the program stands there.  Several nodes can share one
    span (a block and its only expression); they are read innermost
    first, as a record's node is."""
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
            match = _enclosing_match(index, node)
            if match is not None:
                return _Located("binder", node, match)
    for node in nodes:
        if isinstance(node, ast.Expr):
            return _Located("value", node)
    for node in nodes:
        # A refined `let` or destructure is guarded at the statement itself
        # (`wasm/context.py` / `wasm/data.py` `_emit_bind_refine_guard(...,
        # stmt, ...)`, #765): it checks the value the statement binds.
        if isinstance(node, (ast.LetStmt, ast.LetDestruct)):
            return _Located("binder", node, node)
    return None


def _enclosing_match(index: _Index, pattern: ast.Node) -> ast.MatchExpr | None:
    """The `match` whose arm pattern *pattern* is, or sits inside."""
    cur: ast.Node | None = pattern
    while cur is not None:
        parent = index.parent.get(id(cur))
        if isinstance(parent, ast.MatchArm) and cur is parent.pattern:
            grand = index.parent.get(id(parent))
            return grand if isinstance(grand, ast.MatchExpr) else None
        if not isinstance(parent, ast.Pattern):
            return None
        cur = parent
    return None  # pragma: no cover — the loop always returns


# =====================================================================
# Calls
# =====================================================================

def _call_of_argument(
    index: _Index, node: ast.Node,
) -> tuple[ast.FnCall | ast.ModuleCall, int] | None:
    """(the call, argument position) when *node* is an argument of a call,
    or a value one stores or joins (a constructor's field, an array element,
    an arm), read through the pipe's desugaring (``a |> f(x)`` is
    ``f(a, x)``, ``narrowing``'s and code generation's one reading of it)."""
    cur: ast.Node | None = node
    while cur is not None:
        parent = index.parent.get(id(cur))
        if isinstance(parent, (ast.FnCall, ast.ModuleCall)):
            for k, arg in enumerate(parent.args):
                if arg is cur:
                    piped = _pipe_of_call(index, parent)
                    return parent, k + (1 if piped else 0)
            return None
        if (isinstance(parent, ast.BinaryExpr)
                and parent.op == ast.BinOp.PIPE and cur is parent.left
                and isinstance(parent.right, (ast.FnCall, ast.ModuleCall))):
            return parent.right, 0
        cur = _store_parent(index, cur)
    return None


def _store_parent(index: _Index, node: ast.Node) -> ast.Node | None:
    """The value *node* is stored in (a constructor's field, an array
    element) or joined into (an arm of a `flow` form), or None."""
    parent = index.parent.get(id(node))
    if isinstance(parent, ast.ConstructorCall):
        return parent if any(a is node for a in parent.args) else None
    if isinstance(parent, ast.ArrayLit):
        return parent if any(e is node for e in parent.elements) else None
    if isinstance(parent, (ast.MatchArm, ast.HandlerClause)):
        if parent.body is not node:
            return None
        parent = index.parent.get(id(parent))
    if isinstance(parent, ast.Expr):
        arms = narrowing.flow_arms(parent)
        if arms and any(a is node for a in arms):
            return parent
    return None


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
        for record in self.all:
            nodes = index.nodes_at(record.file, _span_of(record))
            if nodes:
                self.node[id(record)] = _record_node(record, nodes)

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


def _answers(
    index: _Index, located: _Located, check: EmittedCheck,
    record: ProofObligation, rnode: ast.Node | None,
) -> bool:
    """Whether *check*, standing at *located*, is the runtime half of
    *record* (whose node is *rnode*)."""
    if record.kind not in check.obligations:
        return False
    rfile = index.key(record.file)
    same_file = rfile is not None and rfile == index.key(check.file)
    if same_file and _span_of(record) == _span_of(check):
        return True
    if rnode is None:
        return False
    where = located.where
    if where == "clause":
        return _answers_from_clause(index, located, record, rnode, same_file)
    if where == "parameter":
        return _answers_from_parameter(index, located, rnode)
    if where == "return":
        return _answers_from_return(index, located, rnode)
    if where == "binder":
        return same_file and _answers_from_binder(index, located, rnode)
    if where == "value":
        return same_file and _answers_from_value(index, located, record, rnode)
    if where == "prelude":
        return _answers_from_prelude(check, rnode)
    return False  # pragma: no cover — every class is handled above


def _answers_from_clause(
    index: _Index, located: _Located, record: ProofObligation,
    rnode: ast.Node, same_file: bool,
) -> bool:
    clause = located.node
    assert clause is not None  # noqa: S101 — a clause is always located
    cspan = _node_span(clause)
    rspan = _node_span(rnode)
    # `_dec_bound_check_pairs` is handed the whole `decreases` clause for
    # each `@Nat` component it range-checks (`_dec_measure_bound_check`,
    # `_dec_bound_checks_only`: `at=contract`); the verifier records each
    # component where it is written.  That emitter alone stands at a clause
    # for records inside it: any other record inside a clause (a call's
    # precondition written in a `requires`) is answered elsewhere.
    if (record.kind == "decreases_bound" and isinstance(clause, ast.Decreases)
            and same_file and cspan is not None and rspan is not None
            and _within(rspan, cspan)):
        return True
    # A `requires` is checked once, in its function's prologue
    # (`_compile_preconditions`), for every caller: the runtime half of each
    # `call_pre` recorded at a call to that function.  The record is
    # located at the call and quotes the precondition it is about.
    if record.kind == "call_pre" and isinstance(clause, ast.Requires):
        fn = index.fn_of.get(id(clause))
        call = _call_node(rnode)
        return (fn is not None and call is not None
                and _reached_decl(index, call) is fn
                and record.expr_text == ast.format_expr(clause.expr))
    return False


def _answers_from_parameter(
    index: _Index, located: _Located, rnode: ast.Node,
) -> bool:
    # A refined parameter is checked once, in its function's prologue
    # (`codegen/functions.py` `at=param_te`), for every caller: the runtime
    # half of the narrowing recorded at each call's argument, for the calls
    # that reach that function (`_reached_decl`); a closure's parameter has
    # no declaration a call names, so it answers no call site.
    owner = located.owner
    if not isinstance(owner, ast.FnDecl):
        return False
    found = _call_of_argument(index, rnode)
    if found is None:
        return False
    call, position = found
    return position == located.position and _reached_decl(index, call) is owner


def _answers_from_return(
    index: _Index, located: _Located, rnode: ast.Node,
) -> bool:
    # A refined return is checked once, in the epilogue
    # (`codegen/contracts.py` `at=decl.return_type`), on the value the body
    # returns: the narrowing the verifier records at the body or at a value
    # the body joins.
    owner = located.owner
    if not isinstance(owner, (ast.FnDecl, ast.AnonFn)):
        return False
    return id(rnode) in index.closure(owner.body, stores=True)


def _answers_from_binder(
    index: _Index, located: _Located, rnode: ast.Node,
) -> bool:
    # A destructure or a pattern guards what it binds (`wasm/data.py`
    # `at=te` / `at=pattern` / `at=sub_pat`, and a refined statement's guard
    # at the statement, `_emit_bind_refine_guard(..., stmt, ...)`); the
    # verifier records the narrowing at the value taken apart, or at the
    # component a construction there stores — the component the binder
    # binds, when the value is a construction it can see into.
    owner = located.owner
    if isinstance(owner, ast.LetStmt):
        return id(rnode) in index.closure(owner.value, stores=True)
    if isinstance(owner, ast.LetDestruct):
        value: ast.Node = owner.value
        if (located.position >= 0
                and isinstance(value, ast.ConstructorCall)
                and len(value.args) == len(owner.type_bindings)):
            value = value.args[located.position]
        return id(rnode) in index.closure(value, stores=True)
    if isinstance(owner, ast.MatchExpr):
        return id(rnode) in index.closure(owner.scrutinee, stores=True)
    return False


def _answers_from_value(
    index: _Index, located: _Located, record: ProofObligation,
    rnode: ast.Node,
) -> bool:
    cnode = located.node
    assert cnode is not None  # noqa: S101 — a value is always located
    # A narrowing pushed to the arms of a join (`_collect_narrowing_return_
    # leaves`, the per-arm widenings), or a whole body guarded where the
    # verifier records an arm: one value either way, through the joins
    # `narrowing.flow_arms` names.
    if id(cnode) in index.closure(rnode) or id(rnode) in index.closure(cnode):
        return True
    # A `@Nat` operand an `@Int` operation widens is guarded where it is
    # evaluated (`narrowing.widened_nat_operands`).
    if record.kind == "nat_to_int_coerce" and isinstance(rnode, ast.BinaryExpr):
        return (id(cnode) in index.closure(rnode.left)
                or id(cnode) in index.closure(rnode.right))
    return False


def _answers_from_prelude(check: EmittedCheck, rnode: ast.Node) -> bool:
    # A built-in written in the prelude carries its own checks: a call to it
    # is answered by the check in its body (`float_to_string`'s truncation,
    # which the verifier obligates at the call, `_FLOAT_CONVERSIONS`).
    base = check.function.split("$", 1)[0]
    call = _call_node(rnode)
    return call is not None and call.name == base


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
    index.add(file, program, entry=True)
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

    answered: dict[int, list[EmittedCheck]] = {}
    for check in checks:
        located = _locate(index, check)
        if located is None:
            out.mismatches.append(_check_mismatch(
                "no_mapping", check,
                "no node of the program stands at the check's span"))
            continue
        answering = [
            record
            for kind in check.obligations
            for record in by_kind.get(kind, ())
            if _answers(index, located, check, record,
                        records.located(record))
        ]
        for record in answering:
            answered.setdefault(id(record), []).append(check)
        if check.prelude or not _verified_here(
                index, located.node, records_by_top):
            out.out_of_scope.append(check)
            continue
        if any(record.status != DENIES_GUARD for record in answering):
            continue
        out.mismatches.append(_check_mismatch(
            "guarded_unrecorded", check,
            "the only record at the site says it has no runtime check "
            "(tier3_unguarded)" if answering else
            "this run recorded no obligation of that kind at the site"))

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
        else:
            out.mismatches.append(_record_mismatch(
                "recorded_unguarded", record,
                "the compiled module holds no check that answers it"))
    # One mismatch per site: a check spliced twice into one function (a
    # handler clause inlined at each of its operation's calls) is two
    # entries of the record of checks and one disagreement.
    out.mismatches = sorted(dict.fromkeys(out.mismatches), key=_mismatch_order)
    return out


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
                "program performs.  This one has no such record: the summary "
                "omits it, and a value the verifier could have refused "
                "statically is caught only at run time."
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
