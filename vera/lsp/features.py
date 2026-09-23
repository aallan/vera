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

from collections.abc import Mapping
from dataclasses import dataclass, field

from lsprotocol import types as lsp

from vera import ast, naming
from vera.checker.core import CheckArtifacts
from vera.errors import (
    Diagnostic,
    ParseError,
    SourceLocation,
    TransformError,
)
from vera.lsp.convert import (
    LineIndex,
    location_to_range,
    span_to_range,
    uri_to_path,
)
from vera.lsp.documents import DocumentStore
from vera.obligations.cache import walk_nodes
from vera.obligations.core import ProofObligation
from vera.obligations.session import VerificationSession
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.slots import fn_scopes, fn_slot_scope, slot_table

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
    #: The filesystem path ``uri`` names, and the ``file=`` the pipeline was
    #: actually driven with (:func:`vera.lsp.convert.uri_to_path`).  Kept
    #: beside ``uri`` rather than replacing it because the two answer
    #: different questions: ``uri`` is what the CLIENT is told (a
    #: ``textDocument/definition`` Location must carry a URI), ``path`` is
    #: what the compiler was told, so it is what an obligation's or a
    #: diagnostic's ``file`` is comparable against.
    path: str = ""
    diagnostics: list[Diagnostic] = field(default_factory=list)
    obligations: list[ProofObligation] = field(default_factory=list)
    artifacts: CheckArtifacts | None = None
    program: ast.Program | None = None
    # #1208: the document's naming environment, lifted out of `artifacts` so
    # the slot-table and hover renderers can name against the checker's own
    # alias table.  Empty when the pipeline stopped at parse/transform — there
    # is no check, so there are no aliases to name against.
    alias_env: AliasEnv = EMPTY_ALIAS_ENV


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
    # The pipeline is driven with the PATH, never the URI (#1246): the
    # module resolver reads imports from `Path(file).parent`, and a
    # `file://` URI makes that the directory `file:`, so a document with
    # imports resolved none of them and was silently left unverified.
    path = uri_to_path(uri)
    analysis = Analysis(uri=uri, text=text, index=index, path=path)
    try:
        program = transform(parse(text, file=path))
    except (ParseError, TransformError) as exc:
        analysis.diagnostics = [exc.diagnostic]
        return analysis

    analysis.program = program
    check_diags, artifacts = typecheck_with_artifacts(program, text, file=path)
    analysis.artifacts = artifacts
    analysis.alias_env = artifacts.alias_env
    analysis.diagnostics = list(check_diags)

    if not any(d.severity == "error" for d in check_diags):
        result = session.verify_source(text, file=path)
        # The check above ran module-BLIND (no `resolved_modules`), and
        # `verify_source` re-checks module-AWARE.  Only the second sees the
        # resolver's errors and any error that needs an imported signature
        # to detect, and it hands them back as `check_diagnostics` — which
        # was discarded, so `glib::takes_int("nope")` published a warning,
        # produced no obligations, and said nothing about the E202 that had
        # stopped verification (PR #1282 review).  Appended here, minus
        # anything the blind check already reported: the module-aware pass
        # re-derives those, and a straight append shows each twice.
        seen = {_diag_key(d) for d in analysis.diagnostics}
        analysis.diagnostics += [
            d for d in result.check_diagnostics if _diag_key(d) not in seen
        ]
        analysis.diagnostics += result.verify_diagnostics
        analysis.obligations = result.obligations
    return analysis


def _diag_key(d: Diagnostic) -> tuple[object, ...]:
    """Identity of a diagnostic for de-duplication across two passes."""
    return (
        d.error_code, d.severity, d.description,
        d.location.line, d.location.column,
    )


def _tier_hints(analysis: Analysis) -> list[lsp.Diagnostic]:
    """Per-function verification-tier Hint diagnostics (decision R3).

    Synthesised from the obligation stream — one Hint per function
    that produced obligations, placed at the function's first
    obligation site.  ``violated`` obligations already have their own
    error diagnostics, so they exclude a function from getting a
    cheerful Tier-1 hint without re-stating the failure.

    Only obligations belonging to THIS document contribute (#1246).
    Verifying an entry program verifies the modules it imports, so the
    stream carries their functions too, and their line numbers index
    their own files — placed here they land on whatever this document
    happens to have on that line, or past its end.  ``publishDiagnostics``
    is per-URI, so an imported module's hint is not this document's to
    publish under any line.  ``file is None`` means the record came from
    outside a verifier run (see :class:`ProofObligation`), never from
    another module, so it keeps its hint rather than losing one silently.

    The comparison is against ``analysis.path``, not ``analysis.uri``:
    ``path`` is the ``file=`` the pipeline was given, so it is the same
    string the verifier stamped onto every obligation it reified.
    """
    by_fn: dict[str, list[ProofObligation]] = {}
    for ob in analysis.obligations:
        if ob.file is not None and ob.file != analysis.path:
            continue
        by_fn.setdefault(ob.fn_name, []).append(ob)

    hints: list[lsp.Diagnostic] = []
    for fn_name, obs in by_fn.items():
        if any(o.status == "violated" for o in obs):
            continue
        runtime = sum(1 for o in obs if o.status in ("tier3", "timeout"))
        # #1451: an obligation discharged in no tier is not a proof, and a
        # function whose premises have no model has a whole slice of them.
        # `runtime == 0` alone called that "all contracts proven by Z3" — the
        # editor's own copy of the false Tier 1 the premise check exists to
        # stop (#1457 review, Medium 2).
        unproved = sum(1 for o in obs if o.status == "tier3_unguarded")
        if unproved:
            message = (
                f"{fn_name}: not verified — {unproved} of {len(obs)} "
                f"obligation(s) were neither proved nor guarded"
            )
        elif runtime == 0:
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


def current_analysis(
    store: DocumentStore, analyses: Mapping[str, Analysis], uri: str,
) -> Analysis | None:
    """The analysis of the text the client's buffer holds for *uri*, or
    ``None`` if there is none.

    The one reader of the per-URI analysis table (#1444).  Hover,
    definition, completion, the proof delta and the edit workflows all
    read through here, so none of them answers from an analysis of a
    text the buffer has left.  ``analyze_and_publish`` keeps the table
    that way -- an analysis that raises removes the entry instead of
    leaving the previous text's -- and this checks it again at the read:
    an entry whose text is not the open document's is not returned.
    """
    analysis = analyses.get(uri)
    doc = store.get(uri)
    if analysis is None or doc is None or analysis.text != doc.text:
        return None
    return analysis


def _to_lsp(d: Diagnostic, index: LineIndex) -> lsp.Diagnostic:
    """One Vera diagnostic in LSP shape.

    The editor surface honours the same diagnostics-as-instructions
    contract as --json: description, then the rationale paragraph, then
    the Fix: paragraph (#728).
    """
    message = d.description
    if d.rationale:
        message += f"\n\n{d.rationale}"
    if d.fix:
        message += f"\n\nFix: {d.fix}"
    return lsp.Diagnostic(
        range=location_to_range(d.location, index),
        message=message,
        severity=_SEVERITY.get(d.severity, lsp.DiagnosticSeverity.Error),
        source="vera",
        code=d.error_code or None,
        data={"tier": d.tier} if d.tier is not None else None,
    )


def to_lsp_diagnostics(analysis: Analysis) -> list[lsp.Diagnostic]:
    """Map Vera diagnostics (+ synthesised tier hints) to LSP shape."""
    out = [_to_lsp(d, analysis.index) for d in analysis.diagnostics]
    out.extend(_tier_hints(analysis))
    return out


def analysis_failure(
    uri: str, text: str, exc: BaseException,
) -> list[lsp.Diagnostic]:
    """What is published for *uri* when analysing *text* raised: one
    ``E699``, naming the failure and what it stops.

    The same diagnostic the CLI's backstop builds for an exception that
    escapes a command, so the client learns there was a compiler bug
    rather than seeing the previous text's diagnostics stay up, or none.
    """
    path = uri_to_path(uri)
    return [_to_lsp(Diagnostic(
        description=(
            f"Internal compiler error while analysing '{path}': "
            f"{type(exc).__name__}: {exc}"
        ),
        location=SourceLocation(file=path, line=0, column=0),
        rationale=(
            "The compiler raised an unexpected exception. This is a bug in "
            "the compiler, not a property of the program -- the text may "
            "well be valid. Until a change the server can analyse, it has "
            "no analysis of this document: hover, go-to-definition and "
            "completion answer nothing, a proof delta has no baseline, and "
            "the edit methods refuse."
        ),
        fix=(
            "Please file a bug report with the offending program at "
            "https://github.com/aallan/vera/issues"
        ),
        spec_ref='Chapter 0, Section 0.5.1 "Diagnostic Structure"',
        severity="error",
        error_code="E699",
    ), LineIndex(text))]


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
    # `fn_scopes` (vera/slots.py) pairs each function with the type
    # parameters in scope OVER it — a `where` helper inside a generic sees
    # the outer function's variables too (`_check_fn` saves and restores one
    # shared map rather than replacing it) — so taking the INNERMOST function
    # containing the cursor takes its accumulated scope with it.  Shared with
    # `vera check --explain-slots` (#1217): the two surfaces answer the same
    # question about the same helper, so they accumulate in one place.
    in_scope_vars: tuple[str, ...] = ()
    for tld in analysis.program.declarations:
        if not isinstance(tld.decl, ast.FnDecl):
            continue
        for fn, fn_vars, _path in fn_scopes(tld.decl):
            if fn.span is None or not _span_contains(fn.span, line1, col1):
                continue
            size = (
                fn.span.end_line - fn.span.line,
                fn.span.end_column - fn.span.column,
            )
            if enclosing_size is None or size < enclosing_size:
                enclosing, enclosing_size = fn, size
                in_scope_vars = fn_vars
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

    # #1208: BOTH sides render through :mod:`vera.naming`, in ONE scope —
    # this module's env (the document being analysed owns `enclosing`)
    # narrowed by `fn_slot_scope`, the same narrowing `slot_table` applies to
    # the binding side, so the two cannot be scoped differently.  The
    # reference used to be keyed by its bare HEAD, so `@Option<Int>.0` looked
    # up `Option` in a table keyed `Option<Int>` and go-to-definition
    # silently returned nothing for every parameterised slot.
    scope = fn_slot_scope(analysis.alias_env, in_scope_vars)
    table = slot_table(enclosing.params, analysis.alias_env, in_scope_vars)
    positions = table.get(naming.slot_ref_key(slot, scope), [])
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
