"""Codegen-internal control-flow exceptions for converting silent
skips into structured diagnostics (#626 Layer 3).

Two-tier design:

* :class:`CodegenSkip` — raised by a translator when an AST node shape
  is recognised but not yet implemented in the WASM backend.  The catch
  handler in ``_compile_fn`` / ``_compile_lifted_closure`` converts it
  to a source-located ``[E602]`` (body unsupported) diagnostic.  These
  are user-actionable: "this Vera construct doesn't compile yet".

* :class:`CodegenInvariantError` — raised when codegen encounters a
  state that should be impossible if type-check passed (e.g. a node
  the checker promised to reject).  These are *compiler bugs*, not
  user errors, and should never appear in production output.  The
  catch handler converts them to an ``[E699]`` "internal compiler
  error" diagnostic with a "please file a bug" rationale.

Why these aren't in :mod:`vera.errors`:

Every :class:`vera.errors.VeraError` subclass carries a fully-formed
:class:`vera.errors.Diagnostic` at construction time.  The codegen
skip path needs to *defer* diagnostic construction: the translator
that detects the unsupported shape doesn't know the enclosing
function name or its declaration span (needed for an accurate
"Function 'foo' body contains unsupported expressions" message).
The catch handler at the ``_compile_fn`` boundary has that context,
so these exceptions carry the raw ``(node, reason)`` and let the
catch handler build the structured ``Diagnostic``.

Migration plan (#626 Layer 3, Phase 2):

Before this refactor, every codegen translator that hit an
unsupported shape returned ``None`` and relied on the caller chain
propagating the ``None`` upward.  An audit identified 372 ``return
None`` sites across ``vera/codegen/`` and ``vera/wasm/``, classified
as:

* SILENT_SKIP (105) — caller propagates None without emitting a
  diagnostic.  This is the silent translator-skip class of bug
  #626.  104 were converted to ``raise CodegenSkip`` in PR #658
  (one borderline site reclassified to PROPAGATE on inspection).
* PROPAGATE (154) — pure None-forwarding after a sub-translation
  call.  Reachable only on PROPAGATE-of-PROPAGATE chains; many
  are now unreachable.  Track 1 cleanup tracked in #657.
* OPTIONAL_RETURN (74) — legitimate ``Optional[X]`` design (lookup
  helpers, inference helpers).  Left alone.
* INVARIANT_DEFENSIVE (39) — guards on type-check-impossible states.
  Candidates for conversion to ``CodegenInvariantError``.  Track 2
  tracked in #657.

See #657 for the full per-site audit table and the cleanup tracks.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from vera import ast


class CodegenSkip(Exception):
    """Raised by a translator when an AST node shape isn't supported.

    Caught at the ``_compile_fn`` / ``_compile_lifted_closure``
    boundary and converted to a structured ``[E602]`` diagnostic
    with the enclosing function's name and the unsupported node's
    span.  The translator just has to identify *what* it couldn't
    translate and *why* — the diagnostic-construction context lives
    at the catch site.

    Parameters
    ----------
    node:
        The AST node whose shape isn't yet supported by codegen.
        Used to attach a source span to the resulting diagnostic.
    reason:
        Short human-readable description of *why* this shape isn't
        supported.  Appears in the ``[E602]`` message after the
        node-type label.
    """

    def __init__(self, node: "ast.Node", reason: str) -> None:
        self.node = node
        self.reason = reason
        super().__init__(
            f"codegen skip on {type(node).__name__}: {reason}"
        )


class CodegenInvariantError(Exception):
    """Raised when codegen sees a state that type-check should have rejected.

    This is a *compiler bug* signal, not a user-facing limitation.
    If you find yourself catching this, the catch handler should
    surface it as an ``[E699]`` internal-compiler-error diagnostic
    asking the user to file a bug report.  The expected path is
    "never caught, always crash" during development, and "caught at
    the top-level so we don't drop a stack trace into the user's
    terminal" in production.

    Parameters
    ----------
    msg:
        Description of the invariant that was violated.  Should be
        specific enough that a compiler maintainer can grep the
        codebase and find the raise site.
    node:
        Optional AST node whose presence triggered the invariant
        check.  When present, attached to the diagnostic for
        source-location purposes.
    """

    def __init__(
        self, msg: str, node: "ast.Node | None" = None
    ) -> None:
        self.msg = msg
        self.node = node
        super().__init__(msg)
