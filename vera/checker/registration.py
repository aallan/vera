"""Pass 1 registration mixin — forward-declares all top-level names."""

from __future__ import annotations

import dataclasses
import functools
import re
from collections.abc import Iterator

from vera import ast
from vera.environment import (
    AbilityInfo,
    AdtInfo,
    ConstructorInfo,
    EffectInfo,
    OpInfo,
    TypeAliasInfo,
)
from vera.types import TypeVar

# #1191: the prelude's generated-declaration namespace — "Vera" + an
# uppercase letter or digit ("VeraOptionMapFn", "VeraA").  Anchored, so
# ordinary words like "Veranda" never match.
_RESERVED_TYPE_PREFIX_RE = re.compile(r"\AVera[A-Z0-9]")


@functools.lru_cache(maxsize=1)
def _builtin_reject_names() -> frozenset[str]:
    """Built-in function names a user/module ``fn`` must not redefine (E151).

    The full built-in registry minus the prelude-injected combinators, which
    the prelude lets the user override soundly (see
    :func:`vera.prelude.overridable_builtin_names`).  Cached: the built-in
    set is static.  Drives the #815 "one canonical form" check — redefining
    an opaque, verifier-modelled built-in (``abs`` / ``min`` / ``max`` / …)
    is the silent verifier↔runtime unsoundness that motivates the error.
    """
    from vera.environment import TypeEnv
    from vera.prelude import overridable_builtin_names

    # #854: apply_fn is a checker special form (variadic and
    # effect-polymorphic — see CallsMixin._check_apply_fn), not a
    # registry row, so it is absent from TypeEnv().functions; add it
    # explicitly.  Codegen unconditionally translates the name to
    # call_indirect (vera/wasm/calls.py), so a user redefinition is the
    # same checker↔codegen desync #815 guards against.
    return (frozenset(TypeEnv().functions)
            | {"apply_fn"}) - overridable_builtin_names()


@functools.lru_cache(maxsize=1)
def builtin_effect_names() -> frozenset[str]:
    """Built-in effect names a user ``effect`` block must not redeclare (E152).

    Read from the live effect registry (:func:`vera.introspect.
    builtin_effect_names`), never a hand-list, so a future built-in effect is
    gated the moment it is registered.  Cached: the registry is static.

    Drives the #1149 "one canonical form" check for effects — the sibling of
    E151 for built-in *functions*.  A built-in host effect is lowered by
    codegen to a fixed host import keyed on the QUALIFIER name, ignoring any
    user declaration, so a redeclaration whose operation signature diverges
    from the built-in (``op print(String, String -> Unit)``) passed both
    ``vera check`` and ``vera compile`` and then trapped at ``vera run`` on
    structurally invalid WASM.
    """
    from vera.introspect import builtin_effect_names as _registry_names

    return _registry_names()


# Identifiers the grammar reserves in *expression* position, so a call to a
# same-named function can never parse (E153).  A function under one of them is
# a declarable trap: it declares cleanly and no bare call site can reach it.
# The reservation refuses the mistake at its source rather than letting it
# surface later as a call-site error, the same one-canonical-form rule as E151
# (built-in functions) and E152 (built-in effects).
#
# The set is assembled from three named pieces so a future addition joins the
# right one deliberately.

# 1. The two contract state forms (#1181).  ``old_expr`` and ``new_expr`` in
# ``vera/grammar.lark`` claim ``"old" "("`` and ``"new" "("``, and each demands
# an *effect reference* as its argument: ``old(5)`` is diagnosed as a malformed
# state reference (``[E030]``/``[E031]``, #1173), never resolved as a call.
_STATE_FORM_FN_NAMES = frozenset({"old", "new"})

# 2. The keywords Lark's *contextual* lexer re-lexes as ``LOWER_IDENT`` in
# declaration position (#1187).  Each declares fine and none can be written in
# expression position: a bare ``match(3)`` does not parse at all (``[E005]``),
# and ``assert(3)`` / ``assume(3)`` are read as the statement forms and collide
# (``[E121]`` + ``[E172]``/``[E173]``).  Keywords the lexer does *not* admit as
# a function name (``resume``, ``with``, ``effect``, ``data``, …) need no entry
# here — the parser already refuses those declarations.
_KEYWORD_FN_NAMES = frozenset({
    "assert", "assume", "forall", "exists", "match",
    "if", "let", "fn", "true", "false", "handle",
})

# 3. The carve-out: names a *host* invokes rather than Vera source, so being
# uncallable from expression position does not make them dead code.
# ``public fn handle(@Request -> @Response)`` is the ``vera serve`` /
# ``wasi:http`` entry point (spec §9.5.6, ``examples/http_server.vera``).  A
# future host-invoked entry point joins this set — deliberately, with the same
# justification — rather than being dropped from the keyword list above.
_HOST_INVOKED_FN_NAMES = frozenset({"handle"})

# One route did reach a reserved name before it was reserved: a module-qualified
# ``mod::old(...)`` / ``mod::match(...)`` parses through the module-call rule
# rather than any reserved rule, so a module export under one of these names was
# callable cross-module (and only cross-module).  The reservation closes that
# route deliberately — a name that is a trap in every unqualified position is
# reserved outright rather than left half-usable.
_RESERVED_FN_NAMES = (
    (_STATE_FORM_FN_NAMES | _KEYWORD_FN_NAMES) - _HOST_INVOKED_FN_NAMES
)


def _strip_rejected_where_fns(decl: ast.FnDecl) -> ast.FnDecl:
    """Return ``decl`` with any where-helper named after a built-in removed,
    recursively (#815).

    A rejected helper must not overwrite the canonical built-in entry in
    ``env.functions`` (the shared ``register_fn`` registers every where-fn by
    name).  Its E151 is emitted separately in
    :meth:`RegistrationMixin._check_builtin_redefinition`; this only prevents
    its registration so a sibling call still resolves to the built-in.
    """
    if not decl.where_fns:
        return decl
    reject = _builtin_reject_names()
    kept = tuple(
        _strip_rejected_where_fns(wfn)
        for wfn in decl.where_fns
        if wfn.name not in reject
    )
    return dataclasses.replace(decl, where_fns=kept or None)


class RegistrationMixin:
    """Methods that register top-level declarations into the type environment."""

    def _register_all(self, program: ast.Program) -> None:
        """Register all top-level declarations (forward reference support)."""
        for tld in program.declarations:
            # C7c: require explicit visibility on fn/data declarations
            if (tld.visibility is None
                    and isinstance(tld.decl, (ast.FnDecl, ast.DataDecl))):
                name = tld.decl.name
                kind = "fn" if isinstance(tld.decl, ast.FnDecl) else "data"
                self._error(
                    tld.decl,
                    f"Missing visibility on '{name}'. "
                    f"Add 'public' or 'private' before '{kind}'.",
                    rationale=(
                        "Every top-level function and data type must have "
                        "an explicit visibility annotation."
                    ),
                    fix=f"private {kind} {name}(...) or public {kind} {name}(...)",
                    spec_ref='Chapter 8, Section 8.4 "Visibility"',
                )
            # #1181/#1187: a fn named after a contract state form (`old` /
            # `new`) or a grammar keyword (`match`, `let`, …) could never be
            # called, because the grammar claims those spellings in expression
            # position.  Checked before the E151 gate and without affecting its
            # control flow, so the two rules stay independent.
            if isinstance(tld.decl, ast.FnDecl):
                self._check_reserved_fn_name(tld.decl)
            # #815: redefining a built-in is a one-canonical-form violation
            # (and a silent verifier↔runtime unsoundness for the
            # verifier-modelled built-ins).  Covers top-level and module
            # functions and their where-helpers; prelude combinators exempt.
            if (isinstance(tld.decl, ast.FnDecl)
                    and self._check_builtin_redefinition(tld.decl)):
                # Rejected built-in redefinition — do not register it over the
                # canonical entry in ``env.functions`` (#815); leave the
                # built-in in scope so later references resolve to it, not the
                # invalid user definition.
                continue
            # #1149: the same one-canonical-form rule for effects.  Rejected
            # blocks are likewise not registered, so the built-in stays in
            # scope and the call sites resolve against it rather than
            # cascading arity errors from the invalid declaration.
            if (isinstance(tld.decl, ast.EffectDecl)
                    and self._check_builtin_effect_redeclaration(tld.decl)):
                continue
            self._register_decl(tld.decl, visibility=tld.visibility)

        # Post-registration cycle detection on type aliases (#648).
        # `_register_alias` resolves each alias's target one at a time;
        # when `type A = B` is processed before `B` is registered, the
        # forward-ref fallback in `_resolve_type` returns a placeholder
        # rather than chasing the chain, so `A = B; B = A` reaches the
        # post-loop state with no observable cycle in the resolved
        # types.  Codegen later stores the raw AST `type_expr` and
        # `_type_expr_to_wasm_type` chases the chain through the AST,
        # producing a `RecursionError` instead of a clean diagnostic.
        # Fix: walk the alias chain in the AST after all aliases have
        # registered, emit `[E132]` for any cycle we find.
        self._check_alias_cycles(program)

    def _check_builtin_redefinition(self, decl: ast.FnDecl) -> bool:
        """Emit E151 if ``decl`` (or a nested where-helper) redefines a
        built-in (#815).

        Returns ``True`` if ``decl`` itself redefines a built-in, so the
        caller can skip registering it over the canonical entry.  Recurses
        into ``where_fns`` so a helper named after a built-in is caught too —
        otherwise the verifier models the call with the built-in's idealized
        model while codegen runs the where-body, the exact
        verify-proves / run-violates desync one scope deeper.  The
        prelude-injected combinators are exempt (see
        :func:`_builtin_reject_names`).
        """
        rejected = decl.name in _builtin_reject_names()
        if rejected:
            self._rejected_builtin_redefs.add(id(decl))
            bn = decl.name
            self._error(
                decl,
                f"Function '{bn}' redefines a built-in.",
                rationale=(
                    f"'{bn}' is a built-in function (spec §9.6) — it is "
                    f"always in scope as the single canonical '{bn}'. "
                    f"Vera provides exactly one way to express each "
                    f"operation, so re-declaring a built-in is not "
                    f"allowed: there is nothing to gain by rolling your "
                    f"own, and a second definition is a second way to say "
                    f"the same thing. For the verifier-modelled built-ins "
                    f"it is also silently unsound — the verifier reasons "
                    f"about every call using the built-in's model while "
                    f"codegen runs your body, so a postcondition can be "
                    f"proved against the built-in yet violated at runtime "
                    f"by your version."
                ),
                fix=(
                    f"Delete this definition and call the built-in '{bn}' "
                    f"directly — it needs no import. If you intend "
                    f"genuinely different behaviour, give the function a "
                    f"distinct name (e.g. '{bn}_custom')."
                ),
                spec_ref='Chapter 9, Section 9.6 "Built-in Functions"',
                error_code="E151",
            )
        nested_rejected = False
        for wfn in decl.where_fns or ():
            if self._check_builtin_redefinition(wfn):
                nested_rejected = True
        # #815: a rejected nested helper is stripped from registration, so if
        # the parent body calls it the call resolves against the canonical
        # built-in and cascades bogus arity/type errors. Mark the parent so its
        # body is skipped in the check phase too. The return value still
        # reflects only whether ``decl``'s own name shadows a built-in, so the
        # parent itself is still registered under its (legitimate) name.
        if nested_rejected:
            self._rejected_builtin_redefs.add(id(decl))
        return rejected

    def _check_reserved_type_name(
        self, decl: ast.TypeAliasDecl | ast.DataDecl,
    ) -> None:
        """Emit E154 for a user type/alias name in the prelude's namespace.

        The prelude's combinators resolve their parameter types through
        generated declarations spelled ``Vera`` + an uppercase letter
        (``VeraOptionMapFn``; type parameters ``VeraA``/``VeraB``, #869).
        ``inject_prelude`` skips any of its declarations whose name a user
        program already spells, so a user ``type VeraOptionMapFn = Int;``
        silently re-types the prelude's own signatures — the program stays
        check-green and then fails WebAssembly validation at run, the
        wrong-layer failure PR #1191 eliminates for the unprefixed names.
        Reserving the prefix outright closes the class (spec §8.4.1); the
        checker never sees the injected twins (injection is a codegen-side
        transform, Pass 1.2), so every declaration reaching this gate is
        user-authored.  Names merely *containing* ``Vera`` (``Veranda``,
        ``MyVeraThing``) stay ordinary: the reservation is anchored at the
        start and requires an uppercase or digit follower.
        """
        if not _RESERVED_TYPE_PREFIX_RE.match(decl.name):
            return
        kind = "alias" if isinstance(decl, ast.TypeAliasDecl) else "data type"
        suggestion = decl.name.removeprefix("Vera")
        if not suggestion[:1].isupper():
            # A digit follower strips to an unparseable name (`Vera0Fn`
            # -> `0Fn`); UPPER_IDENT needs a leading uppercase letter.
            suggestion = f"My{decl.name}"
        self._error(
            decl,
            f"{kind.capitalize()} name '{decl.name}' is reserved for the prelude.",
            rationale=(
                "Names beginning with 'Vera' followed by an uppercase "
                "letter or digit are the prelude's internal namespace — "
                "its combinators resolve through generated declarations "
                "such as 'VeraOptionMapFn' and the type parameters "
                "'VeraA'/'VeraB'. A user declaration under such a name "
                "re-types those internals: the program still type-checks, "
                "then fails WebAssembly validation when it runs. Vera "
                "reserves the namespace outright so the mistake is "
                "refused where it is written."
            ),
            fix=(
                f"Rename the {kind} — any name not starting with 'Vera' "
                f"plus an uppercase letter or digit works (for example "
                f"'{suggestion}')."
            ),
            spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
            error_code="E154",
        )

    def _check_reserved_fn_name(self, decl: ast.FnDecl) -> None:
        """Emit E153 if ``decl`` — or a nested where-helper — is named after a
        contract state form (#1181) or a grammar keyword (#1187).

        Recurses into ``where_fns``: a helper is called in expression position
        exactly like a top-level function, so a helper named ``old`` or
        ``match`` is unreachable for the same reason, one scope deeper.

        The rationale branches on which piece of :data:`_RESERVED_FN_NAMES`
        the name came from — the two are reserved for different reasons, and
        telling a reader that ``match`` is a "contract state form" would be
        false.  The fix is the same on both branches: rename.

        The rejected declaration is still registered, unlike E151's.  There is
        no canonical built-in for the name to shadow here — nothing can resolve
        to ``old`` at all — so leaving the entry in place costs nothing and
        keeps this gate free of E151's skip bookkeeping.
        """
        if decl.name in _RESERVED_FN_NAMES:
            n = decl.name
            if n in _STATE_FORM_FN_NAMES:
                rationale = (
                    f"'{n}' is a contract state form, not an ordinary "
                    f"identifier: the grammar reads '{n}(' in expression "
                    f"position as a reference to an effect's "
                    f"{'pre' if n == 'old' else 'post'}-state, whose only "
                    f"valid argument is an effect reference such as "
                    f"'{n}(State<Int>)'. A call '{n}(...)' therefore never "
                    f"resolves to a function, so this declaration could not "
                    f"be reached from anywhere in the program — it is dead "
                    f"code the compiler would otherwise accept in silence."
                )
                fix = (
                    f"Rename the function to an identifier that is not a "
                    f"contract state form (e.g. '{n}_value' or "
                    f"'{'previous' if n == 'old' else 'updated'}') and "
                    f"update its call sites. Only the exact spellings 'old' "
                    f"and 'new' are reserved — 'older' and 'renew' are "
                    f"ordinary function names."
                )
            else:
                rationale = (
                    f"'{n}' is a keyword the grammar reserves in expression "
                    f"position, not an ordinary identifier. The declaration "
                    f"parses only because the lexer reads '{n}' as a name "
                    f"after 'fn'; in a body '{n}' is always lexed as the "
                    f"keyword, so '{n}(...)' does not parse as a call and "
                    f"never resolves to a function. This declaration could "
                    f"not be reached from anywhere in the program — it is "
                    f"dead code the compiler would otherwise accept in "
                    f"silence. Vera provides exactly one way to express each "
                    f"construct, so a keyword names that construct and "
                    f"nothing else."
                )
                fix = (
                    f"Rename the function to an identifier that is not a "
                    f"keyword — '{n}_fn', or better a name describing what "
                    f"it computes — and update its call sites. The "
                    f"reservation is on the whole identifier, so a longer "
                    f"name that merely begins with '{n}' (such as "
                    f"'{n}_value') is an ordinary function name. 'handle' is "
                    f"the one keyword still available, because 'vera serve' "
                    f"invokes 'handle(@Request -> @Response)' from the host "
                    f"rather than from Vera source."
                )
            self._error(
                decl,
                f"Function name '{n}' is reserved.",
                rationale=rationale,
                fix=fix,
                spec_ref='Chapter 5, Section 5.2 "Function Declaration Syntax"',
                error_code="E153",
            )
        for wfn in decl.where_fns or ():
            self._check_reserved_fn_name(wfn)

    def _check_builtin_effect_redeclaration(
        self, decl: ast.EffectDecl,
    ) -> bool:
        """Emit E152 if ``decl`` redeclares a built-in effect (#1149).

        Returns ``True`` when rejected, so the caller can skip registering it
        over the canonical entry in ``env.effects``.

        The rule is name-keyed and unconditional — it does not compare the
        declared operations against the built-in's.  Codegen routes a
        qualified ``Effect.op(...)`` to the host import by QUALIFIER name and
        never consults the declaration, so a divergent block miscompiles; and
        a *faithful* block is still a second textual spelling of the same
        program, which spec §0.2 design goal 3 (one canonical form) forbids.
        """
        if decl.name not in builtin_effect_names():
            return False
        en = decl.name
        self._error(
            decl,
            f"Effect '{en}' redeclares a built-in effect.",
            rationale=(
                f"'{en}' is a built-in effect (spec §9.5) — its operations "
                f"are always in scope for a function that declares "
                f"'effects(<{en}>)', so this block is a second way to write "
                f"a program the built-in already expresses, which Vera does "
                f"not allow. It is also silently unsound: codegen lowers "
                f"every qualified '{en}.op(...)' call to the fixed host "
                f"import selected by the qualifier and never reads this "
                f"declaration, so an operation signature that diverges from "
                f"the built-in passes 'check' and 'compile' and then traps "
                f"at 'run' on structurally invalid WASM."
            ),
            fix=(
                f"Delete this 'effect {en}' block — the built-in operations "
                f"are available automatically once a function declares "
                f"'effects(<{en}>)'. If you intend a genuinely different "
                f"effect, give it a distinct name (e.g. '{en}Custom')."
            ),
            spec_ref='Chapter 9, Section 9.5 "Built-in Effects"',
            error_code="E152",
        )
        return True

    def _check_alias_cycles(self, program: ast.Program) -> None:
        """Detect cyclic type aliases and emit `[E132]`.

        Spec §2.6.3 requires the alias reference graph to be acyclic.
        This walks the directed graph whose nodes are the program's
        aliases and whose edges run from an alias to every other alias
        its target *structurally* references — the target's own
        `NamedType` head, every `type_arg` at any nesting depth, and
        the base of any `RefinementType` wrapper.

        The rule is structural: not every cyclic spelling would fail
        later on its own.  `type F = Future<F>` crashes codegen with a
        `RecursionError` (#1059 — `_type_expr_to_wasm_type` recurses
        through `Future`'s type argument); `type L = Array<L>` compiles
        to a degenerate type whose only inhabitant is `[]`; a
        self-reference inside a type argument the generic alias
        discards (`type W<T> = Int; type C = W<C>`) even resolves to
        the generic's concrete body.  All are rejected by the one
        acyclicity rule rather than by enumerating which spellings
        happen to crash — no usage analysis of generic parameters.

        Descending into `type_args` is the #1059 extension.  The original
        #648 pass mirrored codegen's alias walker exactly — bare
        `type A = B` references and `RefinementType` bases only — and so
        followed no `type_arg` edge, silently admitting every
        through-`type_arg` cycle.

        A generic alias's own type *parameters* are excluded from the
        reference set: in `type Box<T> = Array<T>` the `T` is bound
        locally and never counts as a reference to a same-named alias,
        so a parameterised abbreviation is not mistaken for a self-cycle.
        """
        alias_decls: dict[str, ast.TypeAliasDecl] = {}
        for tld in program.declarations:
            if isinstance(tld.decl, ast.TypeAliasDecl):
                alias_decls.setdefault(tld.decl.name, tld.decl)

        # Standard three-colour DFS: `on_stack` (grey) holds the current
        # path so a back-edge into it is a cycle; `safe` (black) holds
        # aliases fully explored with no cycle reachable; `reported`
        # suppresses a second diagnostic for aliases already named in an
        # emitted cycle (one E132 per cycle is enough to act on).
        # Iterative with an explicit frame stack: a *legal* alias chain
        # declared deepest-first would recurse once per hop and overflow
        # Python's call stack around a thousand aliases — a checker
        # crash on valid input, the acyclic sibling of the #1059
        # RecursionError (PR #1066 review).
        safe: set[str] = set()
        reported: set[str] = set()

        def refs_of(name: str) -> list[str]:
            decl = alias_decls[name]
            return self._referenced_aliases(
                decl.type_expr, alias_decls, set(decl.type_params or ())
            )

        def visit(root: str) -> None:
            path = [root]
            on_stack = {root}
            # Each frame pairs an alias with an iterator over its
            # outgoing references; exhausting the iterator pops the
            # frame (the alias is fully explored).
            frames: list[tuple[str, Iterator[str]]] = [
                (root, iter(refs_of(root)))
            ]
            while frames:
                name, refs_iter = frames[-1]
                ref = next(refs_iter, None)
                if ref is None:
                    frames.pop()
                    safe.add(name)
                    on_stack.discard(name)
                    path.pop()
                    continue
                if ref in on_stack:
                    cycle = path[path.index(ref):] + [ref]
                    if not any(n in reported for n in cycle):
                        self._error(
                            alias_decls[cycle[0]],
                            f"Cyclic type alias `{cycle[0]}`: "
                            f"{' -> '.join(cycle)}.",
                            rationale=(
                                "Type aliases must form an acyclic "
                                "reference graph: expanding an alias must "
                                "reach a concrete type in finitely many "
                                "steps.  Cycles threaded through `Future` "
                                "type arguments crash codegen with "
                                "unbounded recursion; every other cyclic "
                                "spelling is rejected by the same "
                                "structural rule rather than special-cased "
                                "by whether it happens to compile."
                            ),
                            fix=(
                                "Replace one alias in the cycle with a "
                                "concrete type, or with an `ADT` declared "
                                "via `data` (which can be self-referential "
                                "because the indirection is a heap "
                                "pointer)."
                            ),
                            spec_ref='Chapter 2, Section 2.6.3 "Type Aliases with Refinements"',
                            error_code="E132",
                        )
                        reported.update(cycle)
                    continue
                if ref in safe or ref in reported:
                    continue
                path.append(ref)
                on_stack.add(ref)
                frames.append((ref, iter(refs_of(ref))))

        for name in alias_decls:
            if name in safe or name in reported:
                continue
            visit(name)

    @staticmethod
    def _referenced_aliases(
        te: ast.TypeExpr,
        aliases: dict[str, ast.TypeAliasDecl],
        exclude: set[str],
    ) -> list[str]:
        """Alias names `te` structurally references, outer-to-inner and
        left-to-right so the reported cycle path is deterministic.

        Descends into `NamedType.type_args` (so a self-reference buried
        in `Future<F>` / `Array<L>` is seen — the #1059 extension) and
        `RefinementType.base_type` (so a cycle hidden behind a refinement
        wrapper is seen — #648).  `FnType` parameter/return positions are
        deliberately NOT descended: a function value is a table-index
        (pointer) indirection, so an alias reference there never
        recursively expands the alias's representation — the same
        exemption spec 2.6.3 grants `data` ADTs.  `type FA = fn(FA ->
        Int) effects(pure);` therefore registers cleanly (and
        self-application is separately bounded by finite alias
        unfolding at the use site).
        `exclude` holds the enclosing alias's own type parameters, which
        are locally bound and never count as a reference to a like-named
        alias.

        Iterative (explicit stack) so a deeply nested spelling cannot
        overflow the Python call stack; pushes type_args reversed to
        keep the traversal depth-first left-to-right.
        """
        out: list[str] = []
        stack: list[ast.TypeExpr] = [te]
        while stack:
            t = stack.pop()
            if isinstance(t, ast.NamedType):
                if t.name in aliases and t.name not in exclude:
                    out.append(t.name)
                stack.extend(reversed(t.type_args or ()))
            elif isinstance(t, ast.RefinementType):
                stack.append(t.base_type)
        return out

    def _register_decl(
        self, decl: ast.Decl, visibility: str | None = None,
    ) -> None:
        """Register a single declaration's signature."""
        if isinstance(decl, ast.DataDecl):
            self._register_data(decl, visibility=visibility)
        elif isinstance(decl, ast.TypeAliasDecl):
            self._register_alias(decl)
        elif isinstance(decl, ast.EffectDecl):
            self._register_effect(decl)
        elif isinstance(decl, ast.FnDecl):
            self._register_fn(decl, visibility=visibility)
        elif isinstance(decl, ast.AbilityDecl):
            self._register_ability(decl)

    def _register_data(
        self, decl: ast.DataDecl, visibility: str | None = None,
    ) -> None:
        """Register an ADT and its constructors."""
        self._check_reserved_type_name(decl)
        # Set up type params for resolving constructor field types
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ctors: dict[str, ConstructorInfo] = {}
        for ctor in decl.constructors:
            field_types = None
            if ctor.fields is not None:
                field_types = tuple(
                    self._resolve_type(f) for f in ctor.fields)
            ci = ConstructorInfo(
                name=ctor.name,
                parent_type=decl.name,
                parent_type_params=decl.type_params,
                field_types=field_types,
            )
            ctors[ctor.name] = ci
            self.env.constructors[ctor.name] = ci

        self.env.data_types[decl.name] = AdtInfo(
            name=decl.name,
            type_params=decl.type_params,
            constructors=ctors,
            visibility=visibility,
        )

        self.env.type_params = saved_params

    def _register_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Register a type alias."""
        self._check_reserved_type_name(decl)
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        resolved = self._resolve_type(decl.type_expr)
        self.env.type_aliases[decl.name] = TypeAliasInfo(
            name=decl.name,
            type_params=decl.type_params,
            resolved_type=resolved,
        )

        self.env.type_params = saved_params

    def _register_effect(self, decl: ast.EffectDecl) -> None:
        """Register an effect and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,
            )

        self.env.effects[decl.name] = EffectInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_ability(self, decl: ast.AbilityDecl) -> None:
        """Register an ability and its operations."""
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ops: dict[str, OpInfo] = {}
        for op in decl.operations:
            param_types = tuple(
                self._resolve_type(p) for p in op.param_types)
            ret_type = self._resolve_type(op.return_type)
            ops[op.name] = OpInfo(
                name=op.name,
                param_types=param_types,
                return_type=ret_type,
                parent_effect=decl.name,  # stores ability name
            )

        self.env.abilities[decl.name] = AbilityInfo(
            name=decl.name,
            type_params=decl.type_params,
            operations=ops,
        )

        self.env.type_params = saved_params

    def _register_fn(
        self, decl: ast.FnDecl, visibility: str | None = None,
    ) -> None:
        """Register a function signature."""
        from vera.registration import register_fn
        # #815: drop where-helpers named after a built-in before registering,
        # so a rejected helper can't overwrite the canonical entry (its E151 is
        # emitted in _check_builtin_redefinition).
        register_fn(
            self.env, _strip_rejected_where_fns(decl),
            self._resolve_type, self._resolve_effect_row,
            visibility=visibility,
        )
