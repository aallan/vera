"""Per-module disclosed-function manifests (#1399).

#1363 stops a caller claiming a Tier-1 proof that rests on a fact the run
DISCLOSED — reported as neither proved nor guarded — by withholding that fact
from the first proof attempt and demoting whatever needed it to Tier 3.  The
set of functions in that state is derived by
:func:`vera.verifier.disclosed_fn_names` from the run's own obligation stream.

An IMPORTED callee's obligations never enter the importing run's stream: the
importer verifies its own declarations, harvests the imported *contracts*, and
never discharges the library's obligations.  So the derivation could not see a
disclosure made on the other side of an import, and the very same program
split across two files proved at Tier 1 what one file reported as Tier 3.

This module closes that with a MANIFEST: each module's own verification emits
its disclosed-function set, keyed by the module's owner path, and the importer
consults it through the same resolved-module list that resolves the imported
declarations.  Three properties matter and are load-bearing:

* **Derived, never hand-maintained.**  A manifest is produced by running the
  module's own verification and asking the shared
  :func:`~vera.verifier.disclosed_fn_names` for its answer.  There is no
  second derivation to drift from the in-module one, and no annotation a
  library author could forget or get wrong.
* **The names only.**  The importer takes the disclosed *set*, not the
  module's obligations and not its diagnostics.  An imported module's stream
  stays out of the importer's — the accounting identity
  ``len(obligations) == total + violated + tier3_unguarded`` is a statement
  about the obligations THIS run discharged, and folding another module's in
  would make the importer's summary describe work it did not do.
* **Once per module, content-addressed.**  A module's disclosed set is a pure
  function of its own source, its transitive closure's sources, and the solver
  budget, so the cache below is keyed by exactly those.  A diamond (two
  importers of one module) computes it once, the warm
  :class:`~vera.obligations.session.VerificationSession` reuses it across
  re-verifies of an unchanged import, and an edit to any module in the closure
  is a different key — which is what makes invalidation automatic rather than
  something a caller has to remember to do.

Transitivity falls out of the recursion: computing module A's manifest runs
A's own verification, which builds its own index over A's closure and asks it
about B.  A three-hop chain therefore taints hop by hop with no special case,
and terminates because the resolver rejects circular imports before any of
this runs (:class:`~vera.resolver.ModuleResolver` reports E011 and the
pipeline stops at the type-check gate).
"""

from __future__ import annotations

import hashlib

from dataclasses import replace

from vera.resolver import ResolvedModule

#: A module's disclosed-function set, keyed by the module's owner path.
DisclosedManifest = dict[tuple[str, ...], frozenset[str]]

#: Bounded, content-addressed, process-wide.  Bounded because a long-lived
#: language-server session verifies many document states and each edit to any
#: module in a closure is a new key; content-addressed because that is what
#: makes "invalidate when the module's source changes" automatic — a changed
#: source simply does not hash to the entry that described the old one.
_MAX_ENTRIES = 512
_CACHE: dict[str, frozenset[str]] = {}


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def clear_cache() -> None:
    """Drop every cached manifest.

    For tests that need to observe the computation itself (a hit-count cell,
    a fixture reusing one path with different content in one process).
    Correctness never needs it: the keys are content-addressed.
    """
    _CACHE.clear()


class ModuleDisclosureIndex:
    """Answers "which functions did module *p* disclose?" for one verify run.

    Built from the resolved-module closure the importer already holds, so the
    lookup travels the same path as every other imported artefact.  Each
    module is computed at most once per index (and, via the content-addressed
    cache, at most once per distinct content per process), and only when
    something actually asks — a program that imports a module but never
    matches on one of its calls pays nothing.
    """

    def __init__(
        self,
        resolved_modules: list[ResolvedModule],
        timeout_ms: int,
    ) -> None:
        self._closure = list(resolved_modules)
        self._by_path = {m.path: m for m in self._closure}
        self._timeout_ms = timeout_ms
        self._memo: DisclosedManifest = {}

    def disclosed_in(self, path: tuple[str, ...]) -> frozenset[str]:
        """The disclosed-function set of the module at *path*.

        Empty for a path this run never resolved: there is no module to have
        disclosed anything, and the name it would have supplied does not
        resolve either, so the honest answer is "nothing" rather than a guess.
        """
        cached = self._memo.get(path)
        if cached is not None:
            return cached
        mod = self._by_path.get(path)
        result = frozenset() if mod is None else self._compute(mod)
        self._memo[path] = result
        return result

    # -- internals ------------------------------------------------------

    def _sub_closure(self, mod: ResolvedModule) -> list[ResolvedModule]:
        """*mod*'s OWN transitive import closure, `direct` re-derived.

        Exactly what ``vera verify <mod>`` resolves for itself, so the
        manifest is the answer that command would give.  Two halves, and both
        are load-bearing:

        * ``direct`` is re-derived from *mod*'s own ``import`` declarations.
          The flags on ``self._closure`` describe what the ENTRY program
          imports directly, and name injection and qualified-call resolution
          are gated on that flag — a module verified under the entry's flags
          verifies under a namespace it does not have.
        * The set is *mod*'s reachable set, NOT "the closure minus *mod*".
          Handing a module its own importers is not inert: an importer whose
          own import was excluded (it is the module being verified) no longer
          resolves the qualified calls in its bodies, and #1244 checks every
          resolved module's bodies — so the sub-check fails with errors that
          belong to a module nobody asked about, and the manifest falls back
          to its fail-closed answer.  In a diamond that cascades: the shared
          base is declared wholly disclosed, both arms inherit it, and the
          entry is demoted on the strength of a type error in a file that
          type-checks perfectly well on its own.
        """
        own = {tuple(imp.path) for imp in mod.program.imports}
        reachable: list[ResolvedModule] = []
        seen = {mod.path}
        stack = [p for p in own if p != mod.path]
        while stack:
            path = stack.pop()
            if path in seen:
                continue
            seen.add(path)
            dep = self._by_path.get(path)
            if dep is None:
                continue
            reachable.append(replace(dep, direct=(path in own)))
            stack.extend(tuple(imp.path) for imp in dep.program.imports)
        # Source order for the direct imports, matching what the resolver
        # hands a standalone run (it emits direct imports first, in the order
        # the file names them, then the transitive-only modules).
        order = {tuple(imp.path): i for i, imp in enumerate(mod.program.imports)}
        return sorted(
            reachable,
            key=lambda m: (0, order[m.path]) if m.direct else (1, 0),
        )

    def _cache_key(
        self, mod: ResolvedModule, sub: list[ResolvedModule],
    ) -> str:
        """Everything the module's disclosed set is a function of.

        Its own source; the sources of the closure it is verified against
        (a disclosure in a module it imports can flip one of its own
        obligations, which is the three-hop case); and the solver budget,
        because a longer budget can turn a Tier-3 non-verdict into a proof.
        The module's own path goes in too, so two byte-identical files at
        different paths stay distinct entries.
        """
        parts = [".".join(mod.path), _sha(mod.source), str(self._timeout_ms)]
        parts.extend(
            ".".join(other.path) + "\x1f" + _sha(other.source)
            for other in sorted(sub, key=lambda m: m.path)
        )
        return _sha("\x1e".join(parts))

    def _compute(self, mod: ResolvedModule) -> frozenset[str]:
        """Verify *mod* on its own and take the disclosed names off the run.

        Terminates without a re-entrancy guard, and structurally rather than
        by convention: :meth:`_sub_closure` always drops *mod* itself, and the
        nested verification is given exactly that list, so each level down the
        recursion runs over a STRICTLY smaller closure.  Depth is therefore
        bounded by the closure's size even for a hand-built cyclic
        ``resolved_modules`` — which the resolver in any case refuses to
        produce.
        """
        sub = self._sub_closure(mod)
        key = self._cache_key(mod, sub)
        cached = _CACHE.get(key)
        if cached is not None:
            return cached
        result = _verify_for_disclosure(mod, sub, self._timeout_ms)
        if key not in _CACHE and len(_CACHE) >= _MAX_ENTRIES:
            del _CACHE[next(iter(_CACHE))]
        _CACHE[key] = result
        return result


def _all_fn_names(mod: ResolvedModule) -> frozenset[str]:
    """Every function *mod* declares — the fail-closed answer."""
    from vera import ast

    return frozenset(
        tld.decl.name for tld in mod.program.declarations
        if isinstance(tld.decl, ast.FnDecl)
    )


def _verify_for_disclosure(
    mod: ResolvedModule,
    sub: list[ResolvedModule],
    timeout_ms: int,
) -> frozenset[str]:
    """Run *mod*'s own verification and return what it disclosed.

    Deliberately the WHOLE cold pipeline for that module — the same
    ``typecheck_with_artifacts`` + ``verify`` pair ``cmd_verify`` runs — so
    the manifest says exactly what ``vera verify <module>`` says.  Reaching
    for a cheaper approximation is how the two derivations would come to
    disagree, and a manifest that is more generous than the module's own run
    reinstates the false Tier-1 this exists to stop.

    A module that does not type-check answers fail-closed.  The importer's own
    check registers every resolved module's bodies (#1244), so an unclean
    module fails the importer's check first and verification never runs — but
    "unreachable" is not "safe to guess in the generous direction", and
    returning nothing here would say "this module disclosed nothing" about a
    module nobody managed to verify.
    """
    from vera.checker import typecheck_with_artifacts
    from vera.verifier import disclosed_fn_names, verify

    file = str(mod.file_path)
    check_diags, artifacts = typecheck_with_artifacts(
        mod.program, mod.source, file=file, resolved_modules=sub,
    )
    if any(d.severity == "error" for d in check_diags):
        return _all_fn_names(mod)
    result = verify(
        mod.program, mod.source, file=file,
        timeout_ms=timeout_ms,
        resolved_modules=sub,
        expr_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
    )
    return disclosed_fn_names(result.obligations)
