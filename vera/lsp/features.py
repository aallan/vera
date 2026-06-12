"""Language features over the obligation core (#222 Phase D).

Every feature here is a pure backing function over an
:class:`Analysis` — the bundled result of one pipeline run (parse →
typecheck-with-artifacts → warm incremental verify).  The server layer
(``server.py``) owns *when* analysis runs and serialises it through one
lock (Z3 contexts are not thread-safe); this module owns *what* the
features compute, transport-free, which is where the tests live.

Feature scope (per the #222 plan):

- **Diagnostics**: parse/transform errors, type-check diagnostics, and
  verification diagnostics (tier-annotated via ``Diagnostic.tier``),
  plus a synthesised per-function verification-tier Hint computed from
  the obligation stream (decision R3 — the verifier itself stays
  silent about successes; the Hint is an LSP-layer presentation).
- **Hover**: the type of the smallest recorded expression span under
  the cursor (the Phase D ``expr_types`` side-table, decision R4).
- **Definition**: ``@T.n`` under the cursor → the parameter it
  resolves to, via :func:`vera.slots.slot_table`.  Slot references
  introduced by ``let`` / ``match`` bindings have no single
  signature-level definition site and return None (documented
  limitation; #181's refactoring engine is the eventual owner of full
  binding resolution).
- **Completion**: at a typed hole, the in-scope bindings recorded by
  the checker (each with its type), ranked innermost-first.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from lsprotocol import types as lsp

from vera import ast
from vera.checker.core import CheckArtifacts
from vera.errors import Diagnostic, ParseError, TransformError
from vera.lsp.convert import (
    LineIndex,
    location_to_range,
    span_to_range,
)
from vera.obligations.cache import walk_nodes
from vera.obligations.core import ProofObligation
from vera.obligations.session import VerificationSession
from vera.slots import slot_table

_SEVERITY = {
    "error": lsp.DiagnosticSeverity.Error,
    "warning": lsp.DiagnosticSeverity.Warning,
}


@dataclass
class Analysis:
    """Everything one document analysis produced."""

    uri: str
    text: str
    index: LineIndex
    diagnostics: list[Diagnostic] = field(default_factory=list)
    obligations: list[ProofObligation] = field(default_factory=list)
    artifacts: CheckArtifacts | None = None
    program: ast.Program | None = None


def analyze(
    session: VerificationSession, uri: str, text: str,
) -> Analysis:
    """Run the full pipeline for one document on the warm session.

    Parse/transform failures stop the pipeline and surface as the
    single diagnostic those exceptions carry — matching the CLI, where
    a parse error precludes everything downstream.
    """
    from vera.checker.core import typecheck_with_artifacts
    from vera.parser import parse
    from vera.transform import transform

    index = LineIndex(text)
    analysis = Analysis(uri=uri, text=text, index=index)
    try:
        program = transform(parse(text, file=uri))
    except (ParseError, TransformError) as exc:
        analysis.diagnostics = [exc.diagnostic]
        return analysis

    analysis.program = program
    check_diags, artifacts = typecheck_with_artifacts(program, text, file=uri)
    analysis.artifacts = artifacts
    analysis.diagnostics = list(check_diags)

    if not any(d.severity == "error" for d in check_diags):
        result = session.verify_source(text, file=uri)
        analysis.diagnostics += result.verify_diagnostics
        analysis.obligations = result.obligations
    return analysis


def _tier_hints(analysis: Analysis) -> list[lsp.Diagnostic]:
    """Per-function verification-tier Hint diagnostics (decision R3).

    Synthesised from the obligation stream — one Hint per function
    that produced obligations, placed at the function's first
    obligation site.  ``violated`` obligations already have their own
    error diagnostics, so they exclude a function from getting a
    cheerful Tier-1 hint without re-stating the failure.
    """
    by_fn: dict[str, list[ProofObligation]] = {}
    for ob in analysis.obligations:
        by_fn.setdefault(ob.fn_name, []).append(ob)

    hints: list[lsp.Diagnostic] = []
    for fn_name, obs in by_fn.items():
        if any(o.status == "violated" for o in obs):
            continue
        runtime = sum(1 for o in obs if o.status in ("tier3", "timeout"))
        if runtime == 0:
            message = f"{fn_name}: Tier 1 — all contracts proven by Z3"
        else:
            message = (
                f"{fn_name}: Tier 3 — {runtime} of {len(obs)} "
                f"obligation(s) fall back to runtime checks"
            )
        first = min(obs, key=lambda o: (o.line, o.column))
        line0 = max(0, first.line - 1)
        hints.append(lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=line0, character=0),
                end=lsp.Position(line=line0, character=0),
            ),
            message=message,
            severity=lsp.DiagnosticSeverity.Hint,
            source="vera",
            code="tier",
        ))
    return hints


def to_lsp_diagnostics(analysis: Analysis) -> list[lsp.Diagnostic]:
    """Map Vera diagnostics (+ synthesised tier hints) to LSP shape."""
    out: list[lsp.Diagnostic] = []
    for d in analysis.diagnostics:
        data = {"tier": d.tier} if d.tier is not None else None
        # The editor surface honours the same diagnostics-as-
        # instructions contract as --json: description, then the
        # rationale paragraph, then the Fix: paragraph (#728).
        message = d.description
        if d.rationale:
            message += f"\n\n{d.rationale}"
        if d.fix:
            message += f"\n\nFix: {d.fix}"
        out.append(lsp.Diagnostic(
            range=location_to_range(d.location, analysis.index),
            message=message,
            severity=_SEVERITY.get(d.severity, lsp.DiagnosticSeverity.Error),
            source="vera",
            code=d.error_code or None,
            data=data,
        ))
    out.extend(_tier_hints(analysis))
    return out


def _span_contains(
    span: ast.Span, line1: int, col1: int,
) -> bool:
    """Is the 1-based (line, column) position inside *span*?

    Span end columns are exclusive (Lark convention).
    """
    if (line1, col1) < (span.line, span.column):
        return False
    return (line1, col1) < (span.end_line, span.end_column)


def hover_at(
    analysis: Analysis, position: lsp.Position,
) -> lsp.Hover | None:
    """Type of the smallest recorded expression span under the cursor."""
    if analysis.artifacts is None:
        return None
    line1 = position.line + 1
    col1 = analysis.index.utf16_to_cp(position.line, position.character) + 1

    best: tuple[int, int, int, int] | None = None
    best_size: tuple[int, int] | None = None
    for key in analysis.artifacts.expr_types:
        span = ast.Span(*key)
        if _span_contains(span, line1, col1):
            size = (
                span.end_line - span.line,
                span.end_column - span.column,
            )
            if best_size is None or size < best_size:
                best, best_size = key, size
    if best is None:
        return None
    type_str = analysis.artifacts.expr_types[best]
    return lsp.Hover(
        contents=lsp.MarkupContent(
            kind=lsp.MarkupKind.Markdown,
            value=f"```vera\n{type_str}\n```",
        ),
        range=span_to_range(ast.Span(*best), analysis.index),
    )


def definition_at(
    analysis: Analysis, position: lsp.Position,
) -> lsp.Location | None:
    """``@T.n`` under the cursor → the parameter binding it names.

    Signature-level resolution only: when the slot index exceeds the
    parameter count for that type (the reference binds to a ``let`` or
    ``match`` binding deeper in the body), there is no single
    definition site to jump to and None is returned.
    """
    if analysis.program is None:
        return None
    line1 = position.line + 1
    col1 = analysis.index.utf16_to_cp(position.line, position.character) + 1

    # Resolve against the INNERMOST function containing the cursor —
    # a slot inside a `where`-block function names that function's
    # parameters, not the enclosing top-level function's.
    enclosing: ast.FnDecl | None = None
    enclosing_size: tuple[int, int] | None = None
    for tld in analysis.program.declarations:
        for node in walk_nodes(tld.decl):
            if (
                isinstance(node, ast.FnDecl)
                and node.span is not None
                and _span_contains(node.span, line1, col1)
            ):
                size = (
                    node.span.end_line - node.span.line,
                    node.span.end_column - node.span.column,
                )
                if enclosing_size is None or size < enclosing_size:
                    enclosing, enclosing_size = node, size
    if enclosing is None:
        return None

    slot: ast.SlotRef | None = None
    for node in walk_nodes(enclosing):
        if (
            isinstance(node, ast.SlotRef)
            and node.span is not None
            and _span_contains(node.span, line1, col1)
        ):
            slot = node
            break
    if slot is None:
        return None

    table = slot_table(enclosing.params)
    positions = table.get(slot.type_name, [])
    if slot.index >= len(positions):
        return None  # binds to a let/match binding, not a parameter
    param = enclosing.params[positions[slot.index] - 1]
    if param.span is None:
        return None
    return lsp.Location(
        uri=analysis.uri,
        range=span_to_range(param.span, analysis.index),
    )


def completion_at(
    analysis: Analysis, position: lsp.Position,
) -> lsp.CompletionList | None:
    """At a typed hole: the in-scope bindings, innermost first."""
    if analysis.artifacts is None:
        return None
    line1 = position.line + 1
    col1 = analysis.index.utf16_to_cp(position.line, position.character) + 1

    for hole in analysis.artifacts.holes:
        span = ast.Span(
            hole.line, hole.column, hole.end_line, hole.end_column,
        )
        # The cursor sits inside the hole or immediately after it
        # (clients place the caret after `?` when completing).
        after = (line1, col1) == (span.end_line, span.end_column)
        if _span_contains(span, line1, col1) or after:
            items = [
                lsp.CompletionItem(
                    label=ref,
                    kind=lsp.CompletionItemKind.Variable,
                    detail=type_str,
                    sort_text=f"{i:04d}",
                )
                for i, (ref, type_str) in enumerate(hole.bindings)
            ]
            return lsp.CompletionList(
                is_incomplete=False,
                items=items,
            )
    return None
