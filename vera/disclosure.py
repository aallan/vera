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

from dataclasses import dataclass, replace

from vera.resolver import ResolvedModule


@dataclass(frozen=True)
class DisclosureSite:
    """Where, and by what, one function's fact was disclosed (#1399).

    A membership answer alone made the importer's diagnostic untrue of the
    importing run: its rationale said "the run reported it as neither proved
    nor guarded" when this run reported no such thing, and the ``E504`` that
    identifies the culprit belongs to the library's run, whose diagnostics the
    importer discards by design.  In one file that ``E504`` sits beside the
    ``E534``; across an import the reader got one warning naming only their
    own postcondition, and nothing to go and look at.  Carrying the site with
    the name is what lets the importer cite it.
    """

    module: tuple[str, ...]
    fn_name: str
    file: str | None
    line: int
    column: int
    error_code: str

    def cite(self) -> str:
        """One clause naming the callee, its file position, and its code."""
        where = f"{self.file}:{self.line}" if self.file else "its own module"
        code = f" ({self.error_code})" if self.error_code else ""
        return (
            f"'{'.'.join(self.module)}::{self.fn_name}', disclosed at "
            f"{where}{code}"
        )


#: One module's disclosed functions, each with the site that disclosed it.
#: Membership (`name in manifest`) is the question most callers ask; the
#: value is what the importer's diagnostic cites.
ModuleManifest = dict[str, DisclosureSite]

#: Every module's manifest, keyed by the module's owner path.
DisclosedManifest = dict[tuple[str, ...], ModuleManifest]

#: Bounded, content-addressed, process-wide.  Bounded because a long-lived
#: language-server session verifies many document states and each edit to any
#: module in a closure is a new key; content-addressed because that is what
#: makes "invalidate when the module's source changes" automatic — a changed
#: source simply does not hash to the entry that described the old one.
_MAX_ENTRIES = 512
_CACHE: dict[str, ModuleManifest] = {}


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
    lookup travels the same path as every other imported artefact.  Two cost
    properties are structural rather than incidental, and both were bought
    with a defect (adversarial review of PR #1402):

    * **Each module is verified at most once.**  The first ask walks the
      import DAG BOTTOM-UP and computes every manifest the target depends on
      in dependency order, so by the time a module's own verification runs,
      each of its imports already has an answer in the content-addressed
      cache.  Computing lazily and letting the answer recurse looks
      equivalent and is not: it nests one whole verify pipeline per import
      hop, which is quadratic in the chain and — the part that turns a valid
      program into an internal compiler error — bounded by the interpreter's
      stack rather than by the closure.  A 70-module chain reached ``E699``
      where the same program verified clean without the manifest at all.
    * **This module adds no recursion of its own.**  Both DAG walks are
      iterative, so the only recursion in the path is the resolver's, which
      ran before verification even started.

    Laziness is unchanged and is the other half: a program that imports a
    module but never matches on one of its calls asks nothing and pays
    nothing.
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
        # Per-index memos for the two derived values every consult needs.
        # Keyed by (path, SOURCE), never by path alone: within one index a
        # path names one module, but a caller may hand two indexes different
        # content at the same path, and a path-keyed memo would then answer
        # for the wrong one — the very confusion between an identity and its
        # content that the content-addressed cache key exists to avoid.
        self._sub_memo: dict[
            tuple[tuple[str, ...], str], list[ResolvedModule]
        ] = {}
        self._key_memo: dict[tuple[tuple[str, ...], str], str] = {}
        # Shared across every sub-check this index runs, so a module's bodies
        # are checked once for the whole closure rather than once per module
        # verified.  See `typecheck_with_artifacts(body_check_memo=...)`.
        self._body_check_memo: set[tuple[str, ...]] = set()

    def disclosed_in(self, path: tuple[str, ...]) -> ModuleManifest:
        """The disclosed-function set of the module at *path*.

        Empty for a path this run never resolved: there is no module to have
        disclosed anything, and the name it would have supplied does not
        resolve either, so the honest answer is "nothing" rather than a guess.

        Everything *path* depends on is computed first, in dependency order —
        see the class docstring for why that is a correctness property and
        not only a speed one.
        """
        cached = self._memo.get(path)
        if cached is not None:
            return cached
        mod = self._by_path.get(path)
        if mod is None:
            self._memo[path] = {}
            return {}
        for dep_path in self._dependency_order(mod):
            if dep_path in self._memo:
                continue
            dep = self._by_path.get(dep_path)
            if dep is not None:
                self._memo[dep_path] = self._compute(dep)
        return self._memo[path]

    # -- internals ------------------------------------------------------

    def _sub_closure(self, mod: ResolvedModule) -> list[ResolvedModule]:
        """*mod*'s OWN closure, exactly as ``ModuleResolver`` would build it.

        The manifest's premise is that it says what ``vera verify <mod>``
        says, and that only holds if *mod* is verified against the closure
        that command resolves for itself — same members, same ``direct``
        flags, IN THE SAME ORDER.  Three parts, all load-bearing:

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
        * The ORDER mirrors ``ModuleResolver.resolve_imports``: direct
          imports first in source order, then everything else in the order
          ``_resolve_single`` inserts it into the cache, which recurses into
          a module's own imports BEFORE inserting it — a depth-first
          POST-order, each module's imports taken in source order.  Order is
          not cosmetic here: several harvests over ``_resolved_modules`` are
          first-wins ``setdefault``s — imported return types feeding
          monomorphization discovery among them — so two orders can select
          different declarations for one name.  A LIFO stack walk over a set
          gave `otop` the transitive-only order ``od, oc, oe`` where the
          resolver gives ``oc, od, oe`` (CodeRabbit, PR #1402), and iterating
          a set of paths made even that much depend on hash order.  The
          differential in ``tests/test_verifier_cross_module_disclosure.py``
          compares against ``ModuleResolver`` itself rather than against a
          restatement of this paragraph.
        """
        # Source order, de-duplicated — what `resolve_imports` iterates.
        memo_key = (mod.path, mod.source)
        memoized = self._sub_memo.get(memo_key)
        if memoized is not None:
            return memoized
        own = list(dict.fromkeys(
            tuple(imp.path) for imp in mod.program.imports
        ))
        own_set = set(own)

        # `ModuleResolver._resolve_single`'s cache-insertion order: recurse
        # first, insert after.  *mod* itself is excluded, which both keeps a
        # hand-built self-import from looping and matches the resolver, whose
        # entry program is never one of its own imports.
        cache_order = self._post_order(own, skip={mod.path})

        # `resolve_imports`' emission: the direct imports in source order,
        # then the remaining cache in insertion order, de-duplicated.
        emitted: set[tuple[str, ...]] = set()
        out: list[ResolvedModule] = []
        for path in [*own, *cache_order]:
            if path in emitted:
                continue
            dep = self._by_path.get(path)
            if dep is None:
                continue
            emitted.add(path)
            out.append(replace(dep, direct=(path in own_set)))
        self._sub_memo[memo_key] = out
        return out

    def _post_order(
        self,
        roots: list[tuple[str, ...]],
        skip: set[tuple[str, ...]],
    ) -> list[tuple[str, ...]]:
        """Depth-first POST-order over the import DAG, children in source order.

        The order ``ModuleResolver._resolve_single`` inserts modules into its
        cache: it recurses into a module's own imports before inserting the
        module. Two callers want exactly this — :meth:`_sub_closure`, which
        must reproduce the resolver's emission, and
        :meth:`_dependency_order`, which needs every dependency before its
        dependent.

        ITERATIVE, with an explicit stack. The recursive spelling reads
        better and costs a Python frame per import hop, on top of the frame
        per hop the verification itself was taking; between them a 70-module
        chain exhausted the interpreter stack and reported ``E699`` on a
        program that verifies clean (adversarial review of PR #1402). This
        walk now contributes no frames at all.
        """
        order: list[tuple[str, ...]] = []
        seen = set(skip)
        # Reversed so the first root pops first; likewise for each module's
        # own imports below, which must be visited in source order.
        stack: list[tuple[tuple[str, ...], bool]] = [
            (p, False) for p in reversed(roots)
        ]
        while stack:
            path, expanded = stack.pop()
            if expanded:
                order.append(path)
                continue
            if path in seen:
                continue
            seen.add(path)
            dep = self._by_path.get(path)
            if dep is None:
                continue  # unresolvable here, as it would be for the resolver
            stack.append((path, True))
            for sub in reversed(dep.program.imports):
                stack.append((tuple(sub.path), False))
        return order

    def _dependency_order(
        self, mod: ResolvedModule,
    ) -> list[tuple[str, ...]]:
        """*mod* and everything it reaches, dependencies before dependents.

        The order the bottom-up computation walks: when a module's turn
        comes, every import it could consult already has a manifest, so its
        verification finds cached answers instead of starting another one.
        """
        return self._post_order([mod.path], skip=set())

    def _cache_key(self, mod: ResolvedModule) -> str:
        """Everything the module's disclosed set is a function of.

        Takes *mod* alone and derives the closure itself, rather than
        accepting one: a key must cover every input it depends on, and a
        second parameter is a second thing a memo or a caller can get wrong
        while the key stays silent about it.

        Its own source; the sources of the closure it is verified against
        (a disclosure in a module it imports can flip one of its own
        obligations, which is the three-hop case); and the solver budget,
        because a longer budget can turn a Tier-3 non-verdict into a proof.
        The module's own path goes in too, so two byte-identical files at
        different paths stay distinct entries.
        """
        memo_key = (mod.path, mod.source)
        memoized = self._key_memo.get(memo_key)
        if memoized is not None:
            return memoized
        parts = [".".join(mod.path), _sha(mod.source), str(self._timeout_ms)]
        parts.extend(
            ".".join(other.path) + "\x1f" + _sha(other.source)
            for other in sorted(self._sub_closure(mod), key=lambda m: m.path)
        )
        key = _sha("\x1e".join(parts))
        self._key_memo[memo_key] = key
        return key

    def _compute(self, mod: ResolvedModule) -> ModuleManifest:
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
        key = self._cache_key(mod)
        cached = _CACHE.get(key)
        if cached is not None:
            return cached
        result = _verify_for_disclosure(
            mod, sub, self._timeout_ms, self._body_check_memo,
        )
        if key not in _CACHE and len(_CACHE) >= _MAX_ENTRIES:
            del _CACHE[next(iter(_CACHE))]
        _CACHE[key] = result
        return result


def _all_fn_names(mod: ResolvedModule) -> ModuleManifest:
    """Every function *mod* declares — the fail-closed answer.

    Each carries a site naming the module and its file, with no line to point
    at: nothing in it was verified, so there is no culprit obligation to cite,
    and saying so is more honest than borrowing a position.
    """
    from vera import ast

    return {
        tld.decl.name: DisclosureSite(
            module=mod.path, fn_name=tld.decl.name,
            file=str(mod.file_path), line=0, column=0, error_code="",
        )
        for tld in mod.program.declarations
        if isinstance(tld.decl, ast.FnDecl)
    }


def _verify_for_disclosure(
    mod: ResolvedModule,
    sub: list[ResolvedModule],
    timeout_ms: int,
    body_check_memo: set[tuple[str, ...]] | None = None,
) -> ModuleManifest:
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
    from vera.verifier import disclosed_fn_names, is_disclosing, verify

    file = str(mod.file_path)
    check_diags, artifacts = typecheck_with_artifacts(
        mod.program, mod.source, file=file, resolved_modules=sub,
        body_check_memo=body_check_memo,
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
    # WHICH functions is the shared derivation's answer; the walk below only
    # decorates it with the obligation that earned each one, selected by the
    # same predicate so the two cannot disagree about what disclosed what.
    #
    # This loop decorates the OBLIGATION-derived half; the loop after it adds
    # the RESULT-derived half (G1).  A function is disclosed when its result
    # is a disclosed value.  Since #1412 that has ONE kind of evidence: an
    # obligation of its own that was neither proved nor guarded.  A forwarder
    # used to make no claim and so record nothing, which made it invisible
    # here while the same declarations in one file demoted correctly — so
    # this emitted the union of the obligation-derived set with the
    # result-derived one.  #1412 then obligated a refined return at every
    # position that publishes it, which closes that gap where it opens: a
    # forwarder handing on a refined value carries its own unguarded
    # obligation, and one that does NOT publish the refinement hands on no
    # fact for a consumer to lean on.
    #
    # THE CLAIM IS BOUNDED BY WHAT WAS MEASURED, not by that argument.  With
    # the union reverted, no verdict moved across a forwarder dropping the
    # refinement, one through a `where` helper, one returning a tuple
    # carrying the payload, one two import hops away, and one in an
    # `Exn`-declared function; and removing it changed no cell in the suite.
    #
    # #1412 does NOT guard every narrowing.  `_NAT_CONSTRUCTION_GUARDED_SITES`
    # is `{"tuple component"}`, so an ARRAY ELEMENT and a `Map` VALUE still
    # disclose, by design (#1418 review J1).  Neither reaches a consumer as a
    # declared-type fact in any shape measured: an array's elements are
    # modelled opaquely, so a consumer indexing one, passing it to a nested
    # refinement, or re-narrowing it with a `let` is REFUTED (E500) rather
    # than falsely proved, and a `Map` insert emits no narrowing obligation
    # at all.  If a shape is found where such a producer's disclosure DOES
    # reach an importer through a forwarder, this is where the union goes
    # back — for that case, with the reason on the DisclosureSite.
    names = disclosed_fn_names(result.obligations)
    manifest: ModuleManifest = {}
    for o in result.obligations:
        if o.fn_name in names and o.fn_name not in manifest and is_disclosing(o):
            manifest[o.fn_name] = DisclosureSite(
                module=mod.path, fn_name=o.fn_name,
                file=o.file or file, line=o.line, column=o.column,
                error_code=o.error_code or "",
            )
    # A forwarder that narrows nothing has no obligation to decorate, so the
    # loop above skipped it (#1418 review J1).  Cite the import behind it when
    # there is one, and otherwise the forwarder's own declaration — the
    # position a reader of the importing diagnostic should open, from which
    # the local disclosure it hands on is one call away and carries its own
    # E504/E506 in that module's run.
    for name, sites in result.result_disclosed.items():
        if name in manifest:
            continue
        if sites:
            manifest[name] = sites[0]
            continue
        manifest[name] = DisclosureSite(
            module=mod.path, fn_name=name, file=file,
            line=_decl_line(mod, name), column=0, error_code="",
        )
    return manifest


def _decl_line(mod: ResolvedModule, name: str) -> int:
    """The line *name* is declared on in *mod*, or 0 when it cannot be found.

    Walks the declarations rather than trusting a registry, because a
    forwarder may be a ``where`` helper, which the flat last-wins registries
    cannot name (#1418 review G1).
    """
    from vera import ast

    stack = [
        tld.decl for tld in mod.program.declarations
        if isinstance(tld.decl, ast.FnDecl)
    ]
    while stack:
        decl = stack.pop()
        if decl.name == name and decl.span is not None:
            return int(decl.span.line)
        stack.extend(decl.where_fns or ())
    return 0
