"""Pass 1 registration mixin — forward-declares all top-level names."""

from __future__ import annotations

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


# Identifiers unavailable as function names (E153).  For pieces 1 and 2 the
# grammar claims the spelling in *expression* position, so a function under one
# of those names is a declarable trap: it declares cleanly and no bare call site
# can reach it.  The reservation refuses the mistake at its source rather than
# letting it surface later as a call-site error, the same one-canonical-form
# rule as E151 (built-in functions) and E152 (built-in effects).
#
# The set is assembled from five named pieces so a future addition joins the
# right one deliberately, and each piece carries its own rationale because they
# are reserved for genuinely different reasons.  Pieces 3 and 5 are the
# exceptions to the paragraph above — both ARE reachable from expression
# position.  Piece 3 is reserved because that reachability collides with a
# binding the checker injects; piece 5 because spec §1.4 reserves the
# identifier and a keyword must not acquire a second meaning by position.
# Only pieces 1 and 2 may claim unreachability in a diagnostic.

# 1. The two contract state forms (#1181).  ``old_expr`` and ``new_expr`` in
# ``vera/grammar.lark`` claim ``"old" "("`` and ``"new" "("``, and each demands
# an *effect reference* as its argument: ``old(5)`` is diagnosed as a malformed
# state reference (``[E030]``/``[E031]``, #1173), never resolved as a call.
_STATE_FORM_FN_NAMES = frozenset({"old", "new"})

# 2. The keywords Lark's *contextual* lexer re-lexes as ``LOWER_IDENT`` in
# declaration position (#1187).  Each declares fine and none can be written in
# expression position: a bare ``match(3)`` does not parse at all (``[E005]``),
# and ``assert(3)`` / ``assume(3)`` are read as the statement forms and collide
# (``[E121]`` + ``[E172]``/``[E173]``).  Membership is decided by what the
# *lexer* does with the name — these are the keywords a call site genuinely
# cannot reach, which is what their rationale below claims.  ``resume`` is a
# keyword token nowhere and is reserved by piece 3; every OTHER spec §1.4
# keyword is reachable and is reserved by piece 5.
#
# This set was once described as covering the whole keyword list, on the
# premise that ``with`` / ``effect`` / ``data`` / ``type`` and their kind were
# "refused at parse: the contextual lexer does not admit them as a function
# name".  The tree refuted that premise (#1296): all 21 such names declared,
# type checked, verified, compiled and RAN.  They are now reserved by piece 5,
# which argues from the specification rather than from reachability.
_KEYWORD_FN_NAMES = frozenset({
    "assert", "assume", "forall", "exists", "match",
    "if", "let", "fn", "true", "false", "handle",
})

# 3. The handler-clause operator.  ``resume`` is reserved by spec §1.4, and it
# is the one name here that is not a declarable trap: it is never a keyword
# token, so ``fn resume(...)`` parses, and outside a handler clause a bare
# ``resume(7)`` resolves to the declaration and runs.  What it collides with is
# the binding ``check_handle_expr`` injects into ``env.functions`` for the
# duration of each clause body (``vera/checker/control.py``), typed from the
# handled operation's return type.  One spelling would mean the user's function
# in one position and the resumption operator in another — and measured against
# the pre-reservation tree it was worse than ambiguous: with a top-level
# ``private fn resume(@Int -> @Int)`` in the file, an otherwise valid
# ``handle[State<Int>]`` was rejected, its ``put`` clause's ``resume(())``
# failing ``[E202]`` against the *user's* Int parameter.  Removing the
# declaration made the identical handler check clean.  So the declaration is
# refused here, at the checker: the parser has no keyword to refuse it with.
# That shadowing is also cut off at its source, in
# :meth:`TypeChecker._lookup_function_scoped`, which resolves these names
# against the flat registry alone — otherwise the rejected declaration would
# still draw a second, misleading error out of the correct clause bodies.
_HANDLER_OPERATOR_FN_NAMES = frozenset({"resume"})

# 4. The carve-out: names a *host* invokes rather than Vera source, so being
# uncallable from expression position does not make them dead code.
# ``public fn handle(@Request -> @Response)`` is the ``vera serve`` /
# ``wasi:http`` entry point (spec §9.5.6, ``examples/http_server.vera``).  A
# future host-invoked entry point joins this set — deliberately, with the same
# justification — rather than being dropped from the keyword list above.
_HOST_INVOKED_FN_NAMES = frozenset({"handle"})


@functools.lru_cache(maxsize=1)
def grammar_keyword_names() -> frozenset[str]:
    """Every keyword ``vera/grammar.lark`` claims as a bare string literal.

    Read from the grammar file itself (:data:`vera.parser._GRAMMAR_PATH`, the
    same one the parser is built from), never a hand-list, so a keyword added
    to the grammar is reserved the moment it is added.  This is the shape
    :func:`builtin_effect_names` already uses for E152, adopted here for the
    same reason: the hand-list this replaces had silently fallen 21 names
    behind the grammar (#1296), and no gate could see the drift.

    Filtered to identifiers the lexer could actually produce — ``LOWER_IDENT``
    is ``/[a-z][A-Za-z0-9_]*/``, so the wildcard pattern ``"_"`` is excluded
    as it can never be a function name.  Line comments are stripped first so a
    keyword mentioned only in prose is not picked up.
    """
    from vera.parser import _GRAMMAR_PATH

    src = re.sub(r"//[^\n]*", "", _GRAMMAR_PATH.read_text(encoding="utf-8"))
    return frozenset(
        lit for lit in re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', src)
        if re.fullmatch(r"[a-z][A-Za-z0-9_]*", lit)
    )


# 5. The *contextual* keywords: every remaining name the grammar claims (#1296).
# Unlike pieces 1-3 these are not traps.  Lark's contextual lexer admits each
# as a name wherever a name is expected and reads it as the keyword only while
# the keyword's own construct is being parsed, so `private fn with(@Int ->
# @Int)` declares, type checks, verifies, compiles, runs, and answers a bare
# `with(1)` — and stays working inside a contract clause, inside an
# `if`/`then`/`else`, in a function carrying a `where { }` block, and after a
# `let`.  Nothing about the program breaks.
#
# What breaks is the specification.  Spec §1.4 says these identifiers MUST NOT
# be used as function names and nothing held the MUST, so the spec and the
# implementation disagreed about which programs are legal — a model trusting
# §1.4 and a model trusting the compiler derive different programs from the
# same source of truth, and no tool contradicted either.  DESIGN principle 1
# ("checkability over correctness") makes that a defect whatever the program
# does at runtime; principle 6 ("fewer valid programs") chooses enforcement
# over narrowing §1.4; principle 3 supplies the precedent, E152 rejecting even
# a FAITHFUL re-declaration of a built-in effect because a second textual
# spelling is itself the problem.
#
# Derived rather than listed, so the drift cannot recur.  Four of the names
# this reserves — `ability`, `effects`, `op`, `result` — are grammar keywords
# spec §1.4 never listed, found by the derivation rather than by the issue.
# A future grammar keyword lands here by default, which is the safe branch: its
# rationale argues from the reservation, which is true of every reserved
# keyword, rather than from unreachability, which is what proved false.
_CONTEXTUAL_KEYWORD_FN_NAMES = (
    grammar_keyword_names()
    - _STATE_FORM_FN_NAMES
    - _KEYWORD_FN_NAMES
    - _HANDLER_OPERATOR_FN_NAMES
    - _HOST_INVOKED_FN_NAMES
)

# A concrete rename for each, because the generic `<name>_fn` template produces
# `in_fn` / `type_fn` / `pure_fn` — advice no author would take, where DESIGN
# principle 1 asks for "an instruction, not a status report".  A name absent
# here falls back to the template, so a future grammar keyword still gets a
# usable fix; none of these collides with a built-in (E151) or another
# reserved name, which `test_fix_suggests_a_usable_replacement` pins.
_CONTEXTUAL_RENAME_HINTS = {
    "then": "then_branch", "else": "else_branch", "data": "payload",
    "type": "type_of", "module": "module_name", "import": "import_path",
    "public": "is_public", "private": "is_private",
    "requires": "precondition", "ensures": "postcondition",
    "invariant": "invariant_of", "decreases": "measure",
    "effect": "effect_of", "with": "combined_with", "in": "contains",
    "where": "matching", "pure": "is_pure", "ability": "ability_of",
    "effects": "effect_row", "op": "operation", "result": "result_of",
}

# One route did reach a reserved name before it was reserved: a module-qualified
# ``mod::old(...)`` / ``mod::match(...)`` parses through the module-call rule
# rather than any reserved rule, so a module export under one of these names was
# callable cross-module (and only cross-module).  The reservation closes that
# route deliberately — a name that is a trap in every unqualified position is
# reserved outright rather than left half-usable.
_RESERVED_FN_NAMES = (
    (_STATE_FORM_FN_NAMES | _KEYWORD_FN_NAMES | _HANDLER_OPERATOR_FN_NAMES
     | _CONTEXTUAL_KEYWORD_FN_NAMES)
    - _HOST_INVOKED_FN_NAMES
)


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
                # #1221 review: and its `forall` binders, which bind into
                # the same type namespace the two other E154 rails guard.
                self._check_reserved_type_params(tld.decl)
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
        kind = "alias" if isinstance(decl, ast.TypeAliasDecl) else "data type"
        self._check_reserved_decl_name(
            decl, decl.name, kind, prelude_occupies=True,
        )

    def _check_reserved_decl_name(
        self, node: ast.Node, name: str, kind: str, *,
        prelude_occupies: bool,
    ) -> None:
        """Emit E154 for any DECLARED name in the prelude's namespace.

        The reservation is one rule, not one rule per namespace (#1260):
        a type, an alias, an effect, an ability and a constructor all
        name something the program declares, and all five run through
        this single :data:`_RESERVED_TYPE_PREFIX_RE` call so the rails
        cannot drift.  What differs per rail is what the diagnostic can
        truthfully SAY, and both variable parts are load-bearing:

        ``kind`` is the noun, and it also settles the fix.  Renaming is
        the only escape any of these namespaces has; the alias escape the
        reference gate offers (``_resolve_named_type``, "write the type
        out or declare your own alias") is a type-position answer and
        would be wrong advice for an effect, an ability or a constructor,
        none of which can be aliased.

        ``prelude_occupies`` settles the RATIONALE, because the prelude
        does not populate all four namespaces.  It declares exactly six
        reserved type ALIASES and five reserved type PARAMETERS
        (``VeraOptionMapFn``, ``VeraA``/``VeraB``/…) and no effect,
        ability or constructor at all.  So the type/alias rail can state
        the concrete consequence — ``inject_prelude`` skips a declaration
        whose name the program already spells, the user's declaration
        re-types the prelude's own signatures, and the program checks
        green then fails WebAssembly validation at run.  The other three
        rails cannot: there is nothing there to re-type, and a
        reserved-name constructor compiled and RAN correctly before this
        gate existed.  Their reason is the forward one #1260 was decided
        on (DESIGN.md principle 6): the namespace is reserved ahead of
        use so the prelude can grow internals into it without breaking
        programs, and so one rule means one thing everywhere rather than
        being discoverable only by tripping over it in one namespace and
        not the next.  Claiming the type rail's consequence here would be
        a false statement in a diagnostic, which no automated gate can
        catch — ``check_diagnostic_fields`` checks that a rationale is
        PRESENT, not that it is true.
        """
        if not _RESERVED_TYPE_PREFIX_RE.match(name):
            return
        suggestion = name.removeprefix("Vera")
        if not suggestion[:1].isupper():
            # A digit follower strips to an unparseable name (`Vera0Fn`
            # -> `0Fn`); UPPER_IDENT needs a leading uppercase letter.
            suggestion = f"My{name}"
        shared = (
            "Names beginning with 'Vera' followed by an uppercase "
            "letter or digit are the prelude's internal namespace — "
            "its combinators resolve through generated declarations "
            "such as 'VeraOptionMapFn' and the type parameters "
            "'VeraA'/'VeraB'. "
        )
        if prelude_occupies:
            because = (
                "A user declaration under such a name re-types those "
                "internals: the program still type-checks, then fails "
                "WebAssembly validation when it runs. Vera reserves the "
                "namespace outright so the mistake is refused where it "
                "is written."
            )
        else:
            because = (
                f"The prelude declares no {kind} there today, so this "
                f"one collides with nothing yet — the namespace is "
                f"reserved ahead of use, in every declaration namespace, "
                f"so the prelude can grow internals into it without "
                f"breaking programs and so the rule means the same thing "
                f"wherever a name is declared."
            )
        self._error(
            node,
            f"{kind.capitalize()} name '{name}' is reserved for the prelude.",
            rationale=shared + because,
            fix=(
                f"Rename the {kind} — any name not starting with 'Vera' "
                f"plus an uppercase letter or digit works (for example "
                f"'{suggestion}')."
            ),
            spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
            error_code="E154",
        )

    def _check_reserved_type_params(
        self,
        decl: (ast.FnDecl | ast.DataDecl | ast.TypeAliasDecl
               | ast.EffectDecl | ast.AbilityDecl),
    ) -> None:
        """Emit E154 for a type-PARAMETER binder in the prelude's namespace.

        The declaration gate above covers the names a program *declares* as
        types, and the reference gate in ``_resolve_named_type`` covers the
        names it *mentions* — but a ``forall`` variable is neither: it BINDS
        a type name for the body of one declaration.  ``_resolve_named_type``
        consults ``env.type_params`` first, precisely so a binder shadows an
        outer alias, so ``forall<VeraOptionMapFn>`` made every mention of the
        reserved name resolve to the type variable and the reservation held
        at neither end (#1221 review).  Gated where the name is BOUND, which
        is the one place both other gates can then rely on.

        Every surface that binds a type name is covered, because they all
        feed the same ``env.type_params`` scope: a function's ``forall``
        variables (and a ``where`` helper's own, one scope deeper — the
        recursion mirrors :meth:`_check_reserved_fn_name`'s), and the type
        parameters of ``data``, ``type``, ``effect`` and ``ability``
        declarations.  This gate covers BINDERS; the names those same
        declarations introduce — type, alias, effect, ability and
        constructor alike — go through :meth:`_check_reserved_decl_name`
        (#1260), on the same regex.
        """
        if isinstance(decl, ast.FnDecl):
            binders = decl.forall_vars or ()
        else:
            binders = decl.type_params or ()
        for name in binders:
            if not _RESERVED_TYPE_PREFIX_RE.match(name):
                continue
            self._error(
                decl,
                f"Type parameter '{name}' is reserved for the prelude.",
                rationale=(
                    "Names beginning with 'Vera' followed by an uppercase "
                    "letter or digit are the prelude's internal namespace — "
                    "the declarations and type parameters its combinators "
                    "resolve through, injected at code generation and never "
                    "visible to the type checker. A binder in that namespace "
                    "makes every mention of the name inside this declaration "
                    "resolve to the type variable, so neither the "
                    "declaration nor the reference rail can see it, and code "
                    "generation resolves the same spelling to the prelude's "
                    "own declaration."
                ),
                fix=(
                    "Rename the type parameter to anything outside the "
                    "reserved namespace — any name that does not start with "
                    "'Vera' followed by an uppercase letter or digit."
                ),
                spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
                error_code="E154",
            )
        if isinstance(decl, ast.FnDecl):
            for wfn in decl.where_fns or ():
                self._check_reserved_type_params(wfn)

    def _check_reserved_fn_name(self, decl: ast.FnDecl) -> None:
        """Emit E153 if ``decl`` — or a nested where-helper — is named after a
        contract state form (#1181), an unreachable grammar keyword (#1187),
        the handler-clause resumption operator, or a contextual grammar
        keyword (#1296).

        Recurses into ``where_fns``: a helper is called in expression position
        exactly like a top-level function, so a helper named ``old`` or
        ``match`` is unreachable for the same reason, one scope deeper, a
        helper named ``resume`` collides with the same injected binding, and a
        helper named ``with`` is the same second spelling one scope in.

        The rationale branches on which piece of :data:`_RESERVED_FN_NAMES`
        the name came from — the four are reserved for different reasons, and
        telling a reader that ``match`` is a "contract state form", that
        ``resume`` is a keyword no call site can reach, or that ``with`` is
        unreachable when their own program just called it, would each be
        false.  The fix is the same on every branch: rename.

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
                    f"'{n}(State<Int>)'. A bare call '{n}(...)' therefore never "
                    f"resolves to a function, so no unqualified call site "
                    f"can reach this declaration. The one route that "
                    f"previously could — a module-qualified 'mod::{n}(...)' "
                    f"on an exported function — is deliberately closed by "
                    f"this reservation rather than left half-usable."
                )
                fix = (
                    f"Rename the function to an identifier that is not a "
                    f"contract state form (e.g. '{n}_value' or "
                    f"'{'previous' if n == 'old' else 'updated'}') and "
                    f"update its call sites. Only the exact spellings 'old' "
                    f"and 'new' are reserved — 'older' and 'renew' are "
                    f"ordinary function names."
                )
            elif n in _HANDLER_OPERATOR_FN_NAMES:
                rationale = (
                    f"'{n}' names the operator that resumes a suspended "
                    f"effect operation, which the checker binds inside every "
                    f"handler clause body. Unlike the other reserved names "
                    f"this one is not a keyword and does parse as an ordinary "
                    f"call, so the declaration would give '{n}(...)' two "
                    f"meanings that depend on where it is written: this "
                    f"function outside a handler clause, the resumption "
                    f"operator inside one. Vera provides exactly one way to "
                    f"express each construct, so the name means the operator "
                    f"and nothing else."
                )
                fix = (
                    f"Rename the function to an identifier that is not "
                    f"reserved — one describing what it computes, such as "
                    f"'{n}_with' or 'continue_from' — and update its call "
                    f"sites. The reservation is on the whole identifier, so "
                    f"'{n}d' or '{n}_at' are ordinary function names. "
                    f"Resuming inside a handler clause is unaffected: that "
                    f"'{n}' is bound by the handler, not declared."
                )
            elif n in _CONTEXTUAL_KEYWORD_FN_NAMES:
                hint = _CONTEXTUAL_RENAME_HINTS.get(n, f"{n}_fn")
                rationale = (
                    f"'{n}' is a keyword of the language: the grammar claims "
                    f"the spelling for its own construct, and Chapter 1, "
                    f"Section 1.4 reserves the identifier. Unlike the other "
                    f"reserved names this one is reachable — the contextual "
                    f"lexer admits '{n}' as a name where a name is expected, "
                    f"so the declaration parses and a call resolves to it. "
                    f"That is what makes it worth refusing rather than "
                    f"tolerating: the same spelling would name a language "
                    f"construct in one place and this function in another, "
                    f"and a reader would have to decide which by position. "
                    f"Vera provides exactly one way to express each "
                    f"construct, so a keyword names that construct and "
                    f"nothing else."
                )
                fix = (
                    f"Rename the function to an identifier that is not a "
                    f"keyword — '{hint}', or better a name describing what "
                    f"it computes — and update its call sites. The "
                    f"reservation is on the whole identifier, so a longer "
                    f"name that merely contains '{n}' (such as "
                    f"'{n}_value') is an ordinary function name. 'handle' is "
                    f"the one keyword still available, because 'vera serve' "
                    f"invokes it from the host rather than from Vera source."
                )
            else:
                rationale = (
                    f"'{n}' is a keyword the grammar reserves in expression "
                    f"position, not an ordinary identifier. The declaration "
                    f"parses only because the lexer reads '{n}' as a name "
                    f"after 'fn'; in a body '{n}' is always lexed as the "
                    f"keyword, so '{n}(...)' does not parse as a call and "
                    f"no unqualified call site can reach this declaration. "
                    f"The one route that previously could — a "
                    f"module-qualified 'mod::{n}(...)' on an exported "
                    f"function — is deliberately closed by this reservation "
                    f"rather than left half-usable. Vera provides exactly "
                    f"one way to express each construct, so a keyword names "
                    f"that construct and nothing else."
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

    #: The built-in ADT names whose SEMANTICS the compiler special-cases, so
    #: a user declaration of the name cannot be told apart from the built-in
    #: (#1397).  ``Future`` is the transparent wrapper: several derivations
    #: peel a ``Future<…>`` spelling before asking what the name means, so a
    #: declared ``data Future`` compiled to a module that fails to load.
    #:
    #: ``Tuple`` is NOT here, though it has the same disease — ``show`` under
    #: a user ``data Tuple`` drops the constructor name and prints ``(7)``,
    #: and equality is refused (E243) against the BUILT-IN's non-Eq fields.
    #: Reserving it is a language change this tree already decided against:
    #: ``vera/wasm/data.py``'s FIX-3 discriminates the built-in variadic
    #: carrier from a user ``data Tuple<A, B>`` on purpose, and
    #: ``TestFix3UserTupleGate`` plus two verifier cells pin that a user
    #: ``Tuple`` constructs, verifies and runs.  Refusing it would retract
    #:support those tests assert.  Left open on #1397 for a ruling.
    #:
    #: NOT the other built-in ADTs either.  §8.4.1 makes the prelude's data
    #: types ordinary declarations a program may shadow, ``examples/vera/
    #: collections.vera`` ships a ``public data Option<T>``, and #1312's E623
    #: rail is built on entry-file shadowing being legal.  NOT the containers
    #: (``Array``, ``Map``, ``Set``, ``Decimal``): the resolution spine tells
    #: those apart from a declaration correctly, which is #1321/#1331.
    _SPECIAL_CASED_BUILTIN_ADTS = ("Future",)

    def _check_special_cased_builtin_adt(self, decl: ast.DataDecl) -> None:
        """Refuse a `data` whose name the compiler special-cases (#1397).

        The same rule E151 applies to built-in FUNCTIONS and E152 to built-in
        EFFECTS: a name whose meaning the compiler hard-codes cannot also be
        a user declaration, because nothing downstream can tell the two
        apart.  Accepting it was silent for ``Tuple`` — ``show`` dropped the
        constructor name — which is the outcome DESIGN §0.2 excludes.
        """
        if decl.name not in self._SPECIAL_CASED_BUILTIN_ADTS:
            return
        self._error(
            decl,
            f"'{decl.name}' is a built-in type whose meaning the compiler "
            f"special-cases, so it cannot be redeclared as a data type.",
            rationale=(
                f"Unlike the prelude's data types, which a program may "
                f"shadow, '{decl.name}' is recognised by name throughout "
                f"code generation — how it is rendered, compared and laid "
                f"out. A declaration of that name cannot be told apart from "
                f"the built-in, so the program would compile against a "
                f"mixture of the two."
            ),
            fix=(
                f"Rename the declaration. If you meant the built-in "
                f"'{decl.name}', use it directly instead of declaring it."
            ),
            spec_ref='Chapter 8, Section 8.4.1 "Visibility Rules"',
            error_code="E158",
        )

    def _register_data(
        self, decl: ast.DataDecl, visibility: str | None = None,
    ) -> None:
        """Register an ADT and its constructors."""
        self._check_special_cased_builtin_adt(decl)
        self._check_reserved_type_name(decl)
        self._check_reserved_type_params(decl)
        # #1208: allocate the declaration index BEFORE resolving anything, so
        # data and alias registrations interleave in source order.
        decl_index = self.env.next_decl_index()
        # Set up type params for resolving constructor field types
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        ctors: dict[str, ConstructorInfo] = {}
        for ctor in decl.constructors:
            self._check_reserved_decl_name(
                ctor, ctor.name, "constructor", prelude_occupies=False,
            )
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
            decl_index=decl_index,
        )

        self.env.type_params = saved_params

    def _register_alias(self, decl: ast.TypeAliasDecl) -> None:
        """Register a type alias."""
        self._check_reserved_type_name(decl)
        self._check_reserved_type_params(decl)
        decl_index = self.env.next_decl_index()
        saved_params = dict(self.env.type_params)
        if decl.type_params:
            for tv in decl.type_params:
                self.env.type_params[tv] = TypeVar(tv)

        resolved = self._resolve_type(decl.type_expr)
        self.env.type_aliases[decl.name] = TypeAliasInfo(
            name=decl.name,
            type_params=decl.type_params,
            resolved_type=resolved,
            body=decl.type_expr,
            decl_index=decl_index,
        )

        self.env.type_params = saved_params

    def _register_effect(self, decl: ast.EffectDecl) -> None:
        """Register an effect and its operations."""
        self._check_reserved_decl_name(
            decl, decl.name, "effect", prelude_occupies=False,
        )
        self._check_reserved_type_params(decl)
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
        self._check_reserved_decl_name(
            decl, decl.name, "ability", prelude_occupies=False,
        )
        self._check_reserved_type_params(decl)
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
        """Register a function signature.

        Only the declaration itself: ``register_fn`` does not descend into
        ``where`` helpers (#1307), so a helper named after a built-in can no
        longer overwrite the canonical entry and needs no pre-registration
        strip.  Its E151 is emitted in
        :meth:`_check_builtin_redefinition`, and the checker's scoped lookup
        skips a rejected helper by id, so the built-in stays canonical for
        the parent's own calls too.
        """
        from vera.registration import register_fn
        register_fn(
            self.env, decl,
            self._resolve_type, self._resolve_effect_row,
            visibility=visibility,
        )
