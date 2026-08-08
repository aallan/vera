"""Skill-layer workflows: enforced edit sequences (#222 Phase F).

The skill layer applies the 2026-04-20 design notes' observation that
*"agents ignore raw tool primitives and call them out of sequence"*:
instead of exposing verify and apply as separate steps an agent could
skip or reorder, each method here runs a whole edit → verify → apply
sequence server-side.  An agent cannot apply an unverified edit,
because applying *is* the final step of verifying — the
mandatory-contracts philosophy applied to tooling.

``vera/proposeEdit`` (Phase F1) — request params (plain JSON)::

    {"uri": "<document uri>", "text": "<full proposed source>",
     "force": false}

Response (plain JSON)::

    {
      "applied": true,           # the edit passed the gate (or force)
      "ok": true,                # proposed source parsed + checked
      "proof_delta": {...},      # Phase E shape; null if not compiled
      "diagnostics": <count of error diagnostics in the proposed state>,
    }

The gate: apply iff the proof delta has no ``newly_undischarged``
obligations AND the proposed state has no error diagnostics.
``force: true`` overrides both — "this edit knowingly weakens a proof"
(or doesn't compile yet) is sometimes the intent, but it must be said
out loud; the default is the enforced gate.

On apply, three things happen, in order: a ``workspace/applyEdit``
request (the LSP-native mechanism — the *client* owns the buffer, so
the server must round-trip the edit rather than silently diverge), the
canonical :class:`~vera.lsp.documents.DocumentStore` text updates, and
the document re-analyzes + republishes diagnostics.  The client's
echoed ``didChange`` then replays as a no-op from the warm session's
discharge cache — the pre-warming Phase E was designed around.  The
``applyEdit`` request is fire-and-forget: the response's ``applied``
reports the *gate* verdict, not the client's asynchronous answer, and
canonical state is not rolled back if the client declines — a
declining client's buffer re-converges on its next full-sync
``didChange``, and blocking the handler on the client round-trip
would serialise every proposal on editor latency.  On refuse,
canonical state is untouched: same isolation guarantee as
``vera/speculativeEdit``.

``vera/addEffect`` (Phase F3) — request params::

    {"uri": "<document uri>", "fn": "<top-level function name>",
     "effect": "<effect ref, e.g. IO or State<Int>>"}

The genuinely multi-site workflow: adding an effect to a function's
row invalidates the row of every **transitive caller** (each call
site would otherwise fail effect checking), so the inverse call graph
— built from the Phase B ``direct_callee_names`` walker — determines
the propagation set, every affected ``effects(...)`` clause is
rewritten by span (``pure`` → ``<E>``, ``<A>`` → ``<A, E>``,
functions already naming the effect are skipped), and ONE multi-site
candidate runs through the proposeEdit pipeline.  The response adds
``rewritten``: the affected functions in declaration order; if it is
empty the row state was already satisfied and nothing ran
(``applied: false, ok: true, proof_delta: null`` — the no-op shape).
Propagation is bounded at handlers (#725): a call site inside a
``handle[E]`` body contributes no edge, so a caller that discharges
the effect around every one of its call sites is left unrewritten.  A
caller that also reaches the callee on an unhandled path is still
rewritten — the effect genuinely escapes along that path.  A call in a
handler *clause* is not discharged by that handler (clause bodies run
outside it), so it propagates.  A handler only bounds the propagation
when its effect matches instance-for-instance — ``handle[State<Nat>]``
does not discharge ``State<Int>`` — and any mismatch keeps the edge.
Propagation remains single-file (module-qualified calls do not
propagate across the file boundary).  Row identity, separately, is the
base name before any type arguments, so ``State<Int>`` will not be
added next to an existing ``State<Bool>``.

``vera/strengthenContract`` (Phase F2) — request params::

    {"uri": "<document uri>", "fn": "<top-level function name>",
     "kind": "requires" | "ensures", "expr": "<new contract expr>"}

Locates the first *kind* clause of the named top-level function in the
canonical document, splices *expr* over that clause's expression by
span, and runs the candidate through the proposeEdit pipeline — same
response shape, no ``force`` (an agent that wants to push through a
breaking contract change can construct the full text and call
``vera/proposeEdit`` with ``force`` explicitly; the dedicated workflow
exists to make the *audited* path the easy one).  The call-site audit
IS the proof delta: a tightened precondition some caller no longer
satisfies surfaces as ``newly_undischarged`` ``call_pre`` items at the
call sites (Phase A keys obligations by call-site span precisely for
this), and the gate refuses.  Functions nested in ``where`` blocks are
not addressable — top-level names only, matching the single-file
project model.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from lsprotocol import types as lsp

from vera import ast
from vera.lsp.documents import Document
from vera.lsp.extensions import speculative_edit
from vera.obligations.cache import direct_callee_names, walk_nodes
from vera.obligations.core import ProofObligation
from vera.obligations.session import VerificationSession

if TYPE_CHECKING:
    from vera.lsp.server import VeraLanguageServer


def propose_edit(
    session: VerificationSession,
    baseline: list[ProofObligation],
    uri: str,
    text: str,
    force: bool = False,
) -> tuple[bool, dict[str, Any]]:
    """Pure decision: speculative verify *text*, then the apply gate.

    Returns ``(should_apply, response)``.  The caller owns the side
    effects of applying; this function only verifies and decides, so
    the gate logic is testable without a server.
    """
    speculative = speculative_edit(session, baseline, uri, text)
    delta = speculative["proof_delta"]
    clean = (
        delta is not None
        and not delta["newly_undischarged"]
        and speculative["diagnostics"] == 0
    )
    should_apply = force or clean
    return should_apply, {
        "applied": should_apply,
        "ok": speculative["ok"],
        "proof_delta": delta,
        "diagnostics": speculative["diagnostics"],
    }


def full_document_range(doc: Document | None) -> lsp.Range:
    """The whole-document replacement range for a full-text edit.

    With an open document the end position is computed exactly (last
    line, UTF-16 end column, via the document's cached line index).
    Without one — ``proposeEdit`` on a URI the client never opened —
    fall back to the maximum LSP line number; the spec requires clients
    to clamp out-of-range positions to the document end, which makes
    the sentinel a correct whole-file range over unknown content.
    """
    if doc is None:
        return lsp.Range(
            start=lsp.Position(line=0, character=0),
            end=lsp.Position(line=2**31 - 1, character=0),
        )
    end_line0 = doc.text.count("\n")
    last_segment = doc.text.rsplit("\n", 1)[-1]
    return lsp.Range(
        start=lsp.Position(line=0, character=0),
        end=lsp.Position(
            line=end_line0,
            character=doc.index.cp_to_utf16(end_line0, len(last_segment)),
        ),
    )


def apply_propose_edit(
    server: VeraLanguageServer,
    uri: str,
    text: str,
    force: bool = False,
) -> dict[str, Any]:
    """Run the full proposeEdit workflow against *server* state.

    The decision runs under ``analysis_lock`` (one Z3 session, strictly
    serialised).  The apply path then releases the lock before
    ``analyze_and_publish`` re-acquires it — the re-analysis replays
    the just-verified state from the discharge cache, so the second
    pass is cheap by construction.
    """
    with server.analysis_lock:
        baseline_analysis = server.analyses.get(uri)
        baseline = (
            baseline_analysis.obligations
            if baseline_analysis is not None
            else []
        )
        should_apply, response = propose_edit(
            server.session, baseline, uri, text, force,
        )
    if not should_apply:
        return response

    doc = server.store.get(uri)
    server.workspace_apply_edit(
        lsp.ApplyWorkspaceEditParams(
            edit=lsp.WorkspaceEdit(
                changes={
                    uri: [
                        lsp.TextEdit(
                            range=full_document_range(doc),
                            new_text=text,
                        ),
                    ],
                },
            ),
        ),
    )
    server.store.change(
        uri, text, version=(doc.version + 1) if doc is not None else 0,
    )
    server.analyze_and_publish(uri, text)
    return response


def span_offsets(text: str, span: ast.Span) -> tuple[int, int]:
    """``ast.Span`` (1-based line, 1-based code-point column,
    exclusive end) → ``[start, end)`` offsets into *text*.

    Columns count code points, which are exactly Python string
    indices, so no UTF-16 transcoding is involved — that wrinkle only
    exists at the LSP wire boundary.  Spans come from a program parsed
    from this very text, so they are in range by construction.
    """
    line_starts = [0]
    for i, ch in enumerate(text):
        if ch == "\n":
            line_starts.append(i + 1)
    start = line_starts[span.line - 1] + (span.column - 1)
    end = line_starts[span.end_line - 1] + (span.end_column - 1)
    return start, end


_CONTRACT_KINDS: dict[str, type[ast.Requires] | type[ast.Ensures]] = {
    "requires": ast.Requires,
    "ensures": ast.Ensures,
}


def splice_contract(
    program: ast.Program,
    text: str,
    fn_name: str,
    kind: str,
    expr: str,
) -> str | None:
    """Candidate text with *expr* replacing the first *kind* clause
    expression of top-level function *fn_name*; ``None`` if no such
    function/clause exists.

    Vera contracts are mandatory, so every function has at least one
    clause of each kind; with multiple clauses (they conjoin), the
    first is the deterministic splice target and the rest are
    untouched.
    """
    contract_type = _CONTRACT_KINDS[kind]
    for top in program.declarations:
        decl = top.decl  # TopLevelDecl wraps the declaration proper
        if not isinstance(decl, ast.FnDecl) or decl.name != fn_name:
            continue
        for contract in decl.contracts:
            if (
                isinstance(contract, contract_type)
                and contract.expr.span is not None
            ):
                start, end = span_offsets(text, contract.expr.span)
                return text[:start] + expr + text[end:]
        return None
    return None


def strengthen_contract(
    server: VeraLanguageServer,
    uri: str,
    fn_name: str,
    kind: str,
    expr: str,
) -> dict[str, Any]:
    """Run the full strengthenContract workflow against *server* state.

    Splices against the canonical analysis (read under the lock), then
    delegates to :func:`apply_propose_edit` — which re-verifies the
    *candidate* from scratch, so a ``didChange`` racing the window
    between splice and apply degrades to last-writer-wins, exactly the
    full-document-sync semantics every other path already has.

    Raises ``ValueError`` for requests that cannot name a splice
    target (no analysis for the URI, document does not parse, unknown
    function); the handler maps these to JSON-RPC InvalidParams.
    """
    with server.analysis_lock:
        analysis = server.analyses.get(uri)
    if analysis is None:
        raise ValueError(
            f"no analysis for {uri!r} — open the document first",
        )
    if analysis.program is None:
        raise ValueError(
            f"document {uri!r} does not parse; "
            "contracts cannot be located",
        )
    candidate = splice_contract(
        analysis.program, analysis.text, fn_name, kind, expr,
    )
    if candidate is None:
        raise ValueError(
            f"no top-level function {fn_name!r} with a {kind} clause",
        )
    return apply_propose_edit(server, uri, candidate, force=False)


def _top_level_fns(program: ast.Program) -> dict[str, ast.FnDecl]:
    """Top-level functions by name, in declaration order (dicts
    preserve insertion order)."""
    fns: dict[str, ast.FnDecl] = {}
    for top in program.declarations:
        decl = top.decl
        if isinstance(decl, ast.FnDecl):
            fns[decl.name] = decl
    return fns


def _effect_base(ref_text: str) -> str:
    """Effect identity: the reference text before any type arguments
    (``State<Int>`` → ``State``; ``Mod.IO`` → ``Mod.IO``)."""
    return ref_text.split("<", 1)[0].strip()


def _effect_instance_key(ref_text: str) -> str:
    """Full-instance effect identity: the reference text with all
    whitespace removed and type arguments **kept**
    (``State< Int >`` → ``State<Int>``).

    Deliberately not :func:`_effect_base`.  The row rewrite wants the
    base name, because appending ``State<Int>`` beside an existing
    ``State<Bool>`` would give one function two ``State`` rows — a
    same-base match there suppresses a duplicate, a harmless no-op.
    Handler discharge is the opposite direction: it *asserts* the
    effect is gone.  The checker discharges against
    :class:`~vera.types.EffectInstance`, whose equality includes
    ``type_args``, so ``handle[State<Nat>]`` leaves ``State<Int>``
    escaping and a caller around it still needs the row (#725).
    """
    return "".join(ref_text.split())


def _handled_effect_key(ref: ast.EffectRefNode) -> str:
    """The ``handle[...]`` head's full-instance identity, in the same
    spelling :func:`_effect_instance_key` produces from a request
    string.

    Anything this cannot spell exactly is spelled *unmatchably* — a
    string no request can equal — so the call site is left unpruned.
    That is the safe direction: an unpruned edge writes a row the
    program may not strictly need, which still type-checks, while a
    wrongly pruned one leaves the caller on ``pure`` and the whole
    candidate dies on E125.  An almost-right spelling is the trap, so
    the refinement case below is pushed onto the unmatchable path
    rather than allowed to collide with a base-type request.
    """
    if isinstance(ref, ast.QualifiedEffectRef):
        base, args = f"{ref.module}.{ref.name}", ref.type_args
    elif isinstance(ref, ast.EffectRef):
        base, args = ref.name, ref.type_args
    else:  # pragma: no cover — the parser produces only those two
        return ""
    if not args:
        return base
    if any(
        isinstance(n, ast.RefinementType)
        for a in args
        for n in walk_nodes(a)
    ):
        # ``format_type_expr`` drops a refinement's predicate, so
        # ``Exn<{ @Int | p }>`` renders as ``Exn<Int>`` — the checker
        # keeps those two instances distinct (the call site fails E125
        # without its own row), so a collapsed key would prune an edge
        # the program needs.  The walk covers a refinement nested
        # inside an argument (``Exn<Array<{ @Int | p }>>``), which
        # collapses exactly the same way.
        return f"{base}<?>"
    # ``format_type_expr`` spells parameter position (``@Int``); an
    # effect argument is written bare.  A shape it cannot render comes
    # back as "@?", which survives as "?" — never a valid request.
    rendered = ",".join(
        _effect_instance_key(ast.format_type_expr(a)).replace("@", "")
        for a in args
    )
    return f"{base}<{rendered}>"


def _unhandled_callee_names(
    decl: ast.FnDecl, effect: str | None,
) -> frozenset[str]:
    """Direct callees of *decl*, minus those a ``handle[effect]``
    block in *decl* already discharges (#725).

    With *effect* ``None`` this is exactly
    :func:`direct_callee_names` — the handler-unaware call graph.

    Containment is structural (the handled sub-tree) rather than
    span-arithmetic: identical answers where both apply, and no
    special case for nodes carrying no span.  Only the handler's
    ``body`` is pruned.  Its clauses and state initialiser are not —
    a clause body runs *outside* its own handler, so an effect
    performed there still escapes to the enclosing function.

    Handler identity is the full instance including type arguments
    (:func:`_handled_effect_key`); any mismatch keeps the edge.
    """
    if effect is None:
        return direct_callee_names(decl)
    want = _effect_instance_key(effect)
    # Identity by object, not by value: two structurally equal calls
    # at different sites are distinct nodes, and every node stays
    # reachable from *decl* for the duration of the comprehension.
    handled = {
        id(n)
        for h in walk_nodes(decl)
        if isinstance(h, ast.HandleExpr)
        and _handled_effect_key(h.effect) == want
        for n in walk_nodes(h.body)
    }
    return frozenset(
        n.name
        for n in walk_nodes(decl)
        if isinstance(n, ast.FnCall) and id(n) not in handled
    )


def transitive_callers(
    program: ast.Program, fn_name: str, effect: str | None = None,
) -> list[str] | None:
    """*fn_name* plus every top-level function that transitively calls
    it, in declaration order; ``None`` if no such top-level function.

    The inverse closure over the Phase B call walker: plain ``FnCall``
    names only, so module-qualified calls never propagate across the
    file boundary, and calls inside ``where`` blocks attribute to
    their containing top-level function.

    *effect* bounds the closure at handlers (#725): a call site inside
    a ``handle[effect]`` body contributes no edge, because the handler
    discharges the effect and the caller needs no row of its own.  A
    caller that reaches the callee on *any* unhandled path keeps its
    edge — the deliberately conservative reading, since the effect
    genuinely escapes along that path.  Handler identity is the full
    effect instance, type arguments included: ``handle[State<Nat>]``
    does **not** bound a ``State<Int>`` propagation, because the
    checker discharges against ``EffectInstance`` equality and the
    call site would fail E125 without the row.  Only an exact match
    prunes; every other outcome keeps the edge.
    """
    fns = _top_level_fns(program)
    if fn_name not in fns:
        return None
    callees = {
        name: _unhandled_callee_names(decl, effect) & fns.keys()
        for name, decl in fns.items()
    }
    affected = {fn_name}
    changed = True
    while changed:
        changed = False
        for name, called in callees.items():
            if name not in affected and called & affected:
                affected.add(name)
                changed = True
    return [name for name in fns if name in affected]


def _row_names(row: ast.EffectSet) -> set[str]:
    names: set[str] = set()
    for ref in row.effects:
        if isinstance(ref, ast.EffectRef):
            names.add(ref.name)
        elif isinstance(ref, ast.QualifiedEffectRef):
            names.add(f"{ref.module}.{ref.name}")
    return names


def effect_row_rewrite(
    text: str, decl: ast.FnDecl, effect: str,
) -> tuple[int, int, str] | None:
    """``(start, end, replacement)`` adding *effect* to *decl*'s row,
    or ``None`` if the row already names it (idempotence).

    Span facts this relies on (verified against the parser):
    ``PureEffect.span`` covers exactly ``pure``; ``EffectSet.span``
    covers the whole ``<...>`` including brackets, so the append
    splice reuses the original source verbatim up to the closing
    bracket.
    """
    row = decl.effect
    if row.span is None:
        return None
    if isinstance(row, ast.PureEffect):
        start, end = span_offsets(text, row.span)
        return start, end, f"<{effect}>"
    if isinstance(row, ast.EffectSet):
        if _effect_base(effect) in {
            _effect_base(n) for n in _row_names(row)
        }:
            return None
        start, end = span_offsets(text, row.span)
        return start, end, text[start : end - 1] + f", {effect}>"
    return None


def add_effect(
    server: VeraLanguageServer,
    uri: str,
    fn_name: str,
    effect: str,
) -> dict[str, Any]:
    """Run the full addEffect workflow against *server* state.

    Same locking/racing model as :func:`strengthen_contract`.  Raises
    ``ValueError`` when the request cannot name a target (no analysis,
    unparseable document, unknown top-level function).
    """
    with server.analysis_lock:
        analysis = server.analyses.get(uri)
    if analysis is None:
        raise ValueError(
            f"no analysis for {uri!r} — open the document first",
        )
    if analysis.program is None:
        raise ValueError(
            f"document {uri!r} does not parse; "
            "effect rows cannot be located",
        )
    affected = transitive_callers(analysis.program, fn_name, effect)
    if affected is None:
        raise ValueError(f"no top-level function {fn_name!r}")

    fns = _top_level_fns(analysis.program)
    rewrites: list[tuple[int, int, str]] = []
    rewritten: list[str] = []
    for name in affected:
        rewrite = effect_row_rewrite(analysis.text, fns[name], effect)
        if rewrite is not None:
            rewrites.append(rewrite)
            rewritten.append(name)
    if not rewrites:
        # Every affected row already names the effect: nothing to
        # verify, nothing to apply — the documented no-op shape.
        return {
            "applied": False,
            "ok": True,
            "proof_delta": None,
            "diagnostics": 0,
            "rewritten": [],
        }

    candidate = analysis.text
    for start, end, replacement in sorted(rewrites, reverse=True):
        candidate = candidate[:start] + replacement + candidate[end:]
    response = apply_propose_edit(server, uri, candidate, force=False)
    response["rewritten"] = rewritten
    return response
