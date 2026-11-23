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
from pathlib import Path

from lsprotocol import types as lsp

from vera import ast, naming
from vera.checker.core import CheckArtifacts
from vera.errors import (
    Diagnostic,
    ParseError,
    SourceLocation,
    TransformError,
    partial_diagnostics,
)
from vera.lsp.convert import (
    LineIndex,
    location_to_range,
    span_to_range,
    uri_to_path,
)
from vera.lsp.documents import Document
from vera.obligations.cache import walk_nodes
from vera.obligations.core import ProofObligation
from vera.obligations.session import (
    VerificationSession,
    resolve_document_imports,
)
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.parser import source_text
from vera.resolver import ResolvedModule, own_module_path
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
    #: #1558: the path that names this document's own file in a qualified
    #: call (`vera.resolver.own_module_path`, over the modules this analysis
    #: resolved), so a workflow that follows calls reads `ma::f(...)` inside
    #: `module ma;` as the call to `f` it is.  ``None`` for a document with
    #: no path of its own, or one that did not parse.
    own_path: tuple[str, ...] | None = None
    #: The modules this analysis resolved, direct and transitive: where a
    #: diagnostic located in one of them is published (#1788).
    modules: list[ResolvedModule] = field(default_factory=list)
    #: Each import whose file the resolver found and could not read, by
    #: the importing file and the module path, with the file (its E024
    #: names it): the binding an unread module has, from the resolver's
    #: own record (#1788).
    unread: dict[tuple[str, tuple[str, ...]], str] = field(
        default_factory=dict)


def analyze(
    session: VerificationSession, uri: str, text: str,
) -> Analysis:
    """Run the full pipeline for one document on the warm session.

    Parse/transform failures stop the pipeline and surface as the
    single diagnostic those exceptions carry — matching the CLI, where
    a parse error precludes everything downstream.

    The compiler is handed *text* as the file reader reads one
    (:func:`vera.parser.source_text`: a leading byte-order mark dropped,
    every line end a ``\\n``), so it numbers the lines the protocol does, a
    lone ``\\r`` included, and reads the program the CLI reads from the
    same bytes (#1788).  ``Analysis.text`` stays the
    client's text: the currency check compares it with the buffer, and the
    edit methods splice it, keeping the client's own line ends.
    """
    from vera.checker.core import typecheck_with_artifacts
    from vera.parser import parse
    from vera.transform import transform

    index = LineIndex(text)
    source = source_text(text)
    # The pipeline is driven with the PATH, never the URI (#1246): the
    # module resolver reads imports from `Path(file).parent`, and a
    # `file://` URI makes that the directory `file:`, so a document with
    # imports resolved none of them and was silently left unverified.
    path = uri_to_path(uri)
    analysis = Analysis(uri=uri, text=text, index=index, path=path)
    try:
        program = transform(parse(source, file=path))
    except (ParseError, TransformError) as exc:
        analysis.diagnostics = [exc.diagnostic]
        return analysis

    analysis.program = program
    # Module-AWARE, by the same rooting rule `verify_source` uses (#1513).
    # A module-blind check reports every imported name as unresolved, which
    # was only survivable while E200/E230 were warnings; as errors they
    # would stop every document that imports anything short of verification
    # and publish a false error on each imported call.
    resolved, resolver_errors, unread = resolve_document_imports(
        program, path)
    analysis.modules = list(resolved)
    analysis.unread = {
        (str(importer), mod_path): str(found)
        for (importer, mod_path), found in unread.items()
    }
    analysis.own_path = own_module_path(program, None, resolved)
    check_diags, artifacts = typecheck_with_artifacts(
        program, source, file=path, resolved_modules=resolved,
    )
    analysis.artifacts = artifacts
    analysis.alias_env = artifacts.alias_env
    analysis.diagnostics = resolver_errors + list(check_diags)

    if not any(d.severity == "error" for d in analysis.diagnostics):
        result = session.verify_source(source, file=path)
        # `verify_source` re-checks, and hands its check diagnostics back as
        # `check_diagnostics` — which were once discarded, so
        # `glib::takes_int("nope")` published a warning, produced no
        # obligations, and said nothing about the E202 that had stopped
        # verification (PR #1282 review).  Appended here, minus anything
        # the check above already reported: the second pass re-derives
        # those, and a straight append shows each twice.
        seen = {_diag_key(d) for d in analysis.diagnostics}
        analysis.diagnostics += [
            d for d in result.check_diagnostics if _diag_key(d) not in seen
        ]
        analysis.diagnostics += result.verify_diagnostics
        analysis.obligations = result.obligations
    return analysis


def _diag_key(d: Diagnostic) -> tuple[object, ...]:
    """Identity of a diagnostic for de-duplication across two passes:
    the whole location, its file with its line and column, so the same
    message at one position of two files is two diagnostics (#1788)."""
    return (
        d.error_code, d.severity, d.description,
        d.location.file, d.location.line, d.location.column,
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
    doc: Document | None, analysis: Analysis | None,
) -> Analysis | None:
    """*analysis* if it is an analysis of the open document *doc*'s
    text, else ``None``.

    The currency check behind the one reader of the per-URI analysis
    table, ``VeraLanguageServer.current_analysis`` (#1444).  Hover,
    definition, completion, the proof delta and the edit workflows all
    read through it, so none of them answers from an analysis of a text
    the buffer has left.  ``analyze_and_publish`` keeps the table that
    way -- an analysis that raises removes the entry instead of leaving
    the previous text's -- and this checks it again at the read.
    """
    if analysis is None or doc is None or analysis.text != doc.text:
        return None
    return analysis


@dataclass
class _Placement:
    """Where one analysis's diagnostics are published: the document, by
    its line index and the path the pipeline was given, and each module
    it resolved, by the import that brings it in (#1788)."""

    index: LineIndex
    path: str
    #: A module's file → the text the client's buffer of it holds as the
    #: resolver read it: its source, with the byte-order mark the file
    #: begins with put back, so its line 0 is counted as the buffer is.
    sources: dict[str, str] = field(default_factory=dict)
    #: Each import of the document, then each import of a resolved module
    #: in the order the walk reaches it: the importing file, the module
    #: path, and the range of the document's import it is reached under.
    routes: list[tuple[str, tuple[str, ...], lsp.Range]] = field(
        default_factory=list)
    #: A module path → the file the resolver bound it to: the resolved
    #: modules' own ``file_path``, the file their diagnostics name.  The
    #: resolver binds a path once, whichever import reaches it first, so
    #: this is the binding every import of that path has.
    bound: dict[tuple[str, ...], str] = field(default_factory=dict)
    #: An import the resolver could not read, by importing file and module
    #: path → the file it found (``Analysis.unread``).
    unread: dict[tuple[str, tuple[str, ...]], str] = field(
        default_factory=dict)
    #: Whether the client takes ``relatedInformation``.
    related: bool = False

    def head_for(self, file: str) -> lsp.Range:
        """The range a diagnostic located in *file*, a module, is
        published at: the first import, the document's own before any a
        module makes, that the resolver bound to *file*: by the path's
        binding, or for an import it could not read, by its record of that
        import; else the document's first token, for a file no import of
        the document reaches (none is known)."""
        for importer, mod_path, head in self.routes:
            if (self.bound.get(mod_path) == file
                    or self.unread.get((importer, mod_path)) == file):
                return head
        return location_to_range(SourceLocation(line=1, column=1), self.index)


def _placement(analysis: Analysis, related: bool) -> _Placement:
    """The :class:`_Placement` of *analysis*.

    A module is published at the first import of the document that names
    it; one the document reaches only through another module, at the
    first import whose module reaches it.  A diagnostic is named by
    ``str(file_path)``, the file the checker stamps on a module's
    diagnostics.
    """
    place = _Placement(index=analysis.index, path=analysis.path,
                       related=related)
    if analysis.program is None:
        return place
    by_path = {m.path: m for m in analysis.modules}
    heads = [
        (imp.path, span_to_range(imp.span, analysis.index))
        for imp in analysis.program.imports if imp.span is not None
    ]
    # The document's own imports first: a module the document names is
    # published on that import, wherever else the walk meets it.
    document = str(Path(analysis.path))  # as the resolver was handed it
    place.routes.extend((document, mod_path, head) for mod_path, head in heads)
    for mod_path, head in heads:
        queue, seen = [mod_path], set()
        while queue:
            current = queue.pop(0)
            mod = by_path.get(current)
            if current in seen or mod is None:
                continue
            seen.add(current)
            for imp in mod.program.imports:
                place.routes.append((str(mod.file_path), imp.path, head))
                queue.append(imp.path)
    place.bound = {m.path: str(m.file_path) for m in analysis.modules}
    place.unread = dict(analysis.unread)
    place.sources = {
        str(m.file_path): _with_mark(m.file_path, m.source)
        for m in analysis.modules
    }
    return place


def _with_mark(path: Path, source: str) -> str:
    """*source*, a module's text as the resolver read it, with the
    byte-order mark put back if its file begins with one: the resolver's
    reader drops it, and the buffer a client opens the file in holds it,
    so a related location on the module's first line counts it, as the
    document's own ranges do (:class:`~vera.lsp.convert.LineIndex`)."""
    try:
        with path.open("rb") as handle:
            marked = handle.read(3) == b"\xef\xbb\xbf"
    except OSError:
        marked = False
    return "\ufeff" + source if marked else source


def _file_uri(path: str) -> str | None:
    """The ``file:`` URI of the absolute *path*, or ``None`` for a path
    no URI names without guessing a directory (a relative one)."""
    try:
        return Path(path).as_uri()
    except ValueError:
        return None


def _to_lsp(d: Diagnostic, place: _Placement) -> lsp.Diagnostic:
    """One Vera diagnostic in LSP shape, on the document it is published on.

    The editor surface honours the same diagnostics-as-instructions
    contract as --json: description, then the rationale paragraph, then
    the Fix: paragraph (#728).

    A diagnostic whose file is the document's, or that names no file (a
    transform error), is placed at its own line and column.  One located
    in a module the document imports is not this document's line to mark
    (#1788): it is published on the import that brings the module in,
    with its description prefixed by the module's location as ``vera
    check`` prints it, and, for a client that takes it, a
    ``relatedInformation`` entry at that location in the module.
    """
    loc = d.location
    foreign = loc.file is not None and loc.file != place.path
    message = d.description
    related: list[lsp.DiagnosticRelatedInformation] | None = None
    if foreign:
        message = f"In imported module {loc}: {message}"
        doc_range = place.head_for(loc.file or "")
        module_text = place.sources.get(loc.file or "")
        module_uri = _file_uri(loc.file or "")
        if place.related and module_text is not None and module_uri:
            related = [lsp.DiagnosticRelatedInformation(
                location=lsp.Location(
                    uri=module_uri,
                    range=location_to_range(loc, LineIndex(module_text)),
                ),
                message=d.description,
            )]
    else:
        doc_range = location_to_range(loc, place.index)
    if d.rationale:
        message += f"\n\n{d.rationale}"
    if d.fix:
        message += f"\n\nFix: {d.fix}"
    return lsp.Diagnostic(
        range=doc_range,
        message=message,
        severity=_SEVERITY.get(d.severity, lsp.DiagnosticSeverity.Error),
        source="vera",
        code=d.error_code or None,
        related_information=related,
        data={"tier": d.tier} if d.tier is not None else None,
    )


def to_lsp_diagnostics(
    analysis: Analysis, related_information: bool = False,
) -> list[lsp.Diagnostic]:
    """Map Vera diagnostics (+ synthesised tier hints) to LSP shape, in
    the compiler's order.  *related_information* is the client's
    ``textDocument.publishDiagnostics.relatedInformation`` capability."""
    place = _placement(analysis, related_information)
    out = [_to_lsp(d, place) for d in analysis.diagnostics]
    out.extend(_tier_hints(analysis))
    return out


def analysis_failure(
    uri: str, text: str, exc: BaseException,
) -> list[lsp.Diagnostic]:
    """What is published for *uri* when analysing *text* raised: the
    diagnostics the failing pass had already recorded, then one
    ``E699`` naming the failure and what it stops.

    The same report the CLI's backstop makes for an exception that
    escapes a command (#1429 there: what the pass recorded comes first,
    because it is what the user can act on), so the client learns there
    was a compiler bug rather than seeing the previous text's
    diagnostics stay up, or none.
    """
    path = uri_to_path(uri)
    place = _Placement(index=LineIndex(text), path=path)
    recorded = [_to_lsp(d, place) for d in partial_diagnostics(exc)]
    return recorded + [_to_lsp(Diagnostic(
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
    ), place)]


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
