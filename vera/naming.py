"""The ONE renderer for slot names, slot-reference keys, and cell families.

Six subsystems used to answer the question "what is the name of this type
expression?" independently, and disagreed about aliases; the disagreements
are the #1208 / #1209 bug class, where a name minted one way and looked up
another silently misses and the miss reads as "not statically known".

Every slot name and every slot-reference key now comes from here, on the
BIND side and the REFERENCE side together: the checker's two naming entry
points, the monomorphizer's De Bruijn recount, codegen (parameters, ``let``
and match binders, closure captures, handler clause scopes, refinement
guards, slot references), the verifier, the SMT layer, the tester, and
``vera check --explain-slots``.  They move together by construction, because
there is one function of one environment.

The State/Exn cell FAMILY renders here too (:func:`family_name`, #1209):
one cell per checker is one cell per codegen, so a composite alias joins
the family its resolution names instead of minting a second one.  That one
renderer is the only clause of THE RULE below that does NOT go through
``pretty_type``: a family names a CELL rather than a spelling, so it
renders through :func:`~vera.types.structural_type_key` — the same key the
checker orders effect rows by — because ``pretty_type``'s two elisions
(a refinement's predicate, a type variable's built-in marker) would merge
cells the checker keeps apart (#1219).

TWO derivations deliberately stay behind in :mod:`vera.slots`, and both are
about a type's REPRESENTATION rather than about naming anything:
:func:`~vera.slots.type_expr_slot_name` answers the alias-opaque syntactic
spelling for the WASM width / erasure walks and the structural-``Eq``
derivability oracle, and :func:`~vera.slots.family_fallback_name` supplies
the name a family falls back on when its type expression has no nameable
family at all.  Nothing else derives a name of its own: codegen's refinement
boundary guard consumed the last copy — :func:`refinement_binder_parts` — in
#1208 review, and layers only its erasure and E618 decisions on top.

THE RULE, and this module implements exactly it, is **the checker's current
rendering** — because the checker's rendering is what the binding table is
keyed by, so everything downstream must match it or it matches nothing:

* the top-level HEAD is syntactic (alias-opaque): a parameter declared
  ``@MyAlias`` renders ``MyAlias``, never ``Int``;
* type ARGUMENTS are fully resolved: ``@Option<MyAlias>`` where
  ``type MyAlias = Int`` renders ``Option<Int>``;
* a refinement at top level renders its base; in argument position it
  renders the predicate-elided ``{@Int | ...}`` form;
* a function type renders ``Fn`` at top level, and its full
  ``fn(...) effects(...)`` spelling (effect row SORTED) in argument
  position;
* every renderer is TOTAL — an unresolvable type renders ``?``, matching
  the checker's ``UnknownType``, and none of them raise, at any input the
  parser accepts.  Totality is a property to defend, not to assume: alias
  resolution is ITERATIVE, ONE dependency at a time (see
  :func:`_resolve_alias`), precisely because a recursive descent raised
  ``RecursionError`` on a legal 340-hop alias chain — and because resolving
  a whole pending list at once merely moved the recursion onto a
  sibling-shaped alias graph, which raised it again.  The alias branch also
  checks ``env.aliases`` membership so an environment carrying an index
  without a body falls through rather than raising.

Argument resolution is done by rebuilding the checker's own semantic
:class:`~vera.types.Type` and handing it to the checker's own
:func:`~vera.types.pretty_type`, rather than by re-implementing the
rendering; :func:`slot_name` reaches it through :func:`type_arg_name` so
there is one per-argument answer rather than two compositions of the same
steps.  Only the ``Head<a, b>`` JOIN is restated here, and the differential
in ``tests/test_slot_naming_differential.py`` compares against
``canonical_type_name`` directly, so a drift in the separator or the
bracketing goes red across the whole corpus.  Byte-identity with the checker
is therefore structural, not a coincidence to be maintained.

One renderer is only half the contract; the other half is the ENVIRONMENT it
is handed, and getting that wrong fails exactly as silently.  Two rules:

An :class:`AliasEnv` is MODULE-scoped (spec §8.4.1), so every consumer must
render a type expression against the env of the module that DECLARED the
enclosing function — codegen's ``_module_alias_scope``-current env, the
clone's ORIGIN module env in the monomorphizer, the verifier's own
per-module registration (``ContractVerifier._module_alias_envs``, which is
also what an IMPORTED callee's contract renders against).  Rendering against
a neighbouring module's namespace is the same failure as rendering with a
different renderer.

And a ``forall`` variable SHADOWS a same-named module alias for the whole
signature and body it is declared over — the checker binds it before it
binds any slot — so a function-scoped type expression renders against the
module env NARROWED by :func:`~vera.slots.fn_slot_scope`, accumulating a
``where`` helper's ancestors' variables as well as its own.  Un-narrowed,
``forall<T> fn f(@Option<T>, @Option<Int>)`` under ``type T = Int`` collapses
two parameter stacks the checker keeps apart, and every reference into them
resolves onto the wrong parameter.

Alias visibility follows the checker's REGISTRATION ORDER: an alias body is
resolved against only the aliases declared before it, exactly as
``_register_alias`` resolves each alias against the table as it stood at
that point.  A forward reference (``type A = B;`` before ``type B = Int;``)
therefore stays opaque as ``B``, and a cycle (``type A = B; type B = A;``)
terminates with the same placeholder the checker produces rather than
looping — the ordering restriction is well-founded by construction, and it
is what makes the iterative resolution's dependency graph a DAG.
"""

from __future__ import annotations

import enum
import sys
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field

from vera import ast
from vera.types import (
    PRIMITIVES,
    REMOVED_ALIASES,
    AdtType,
    ConcreteEffectRow,
    EffectInstance,
    EffectRowType,
    FunctionType,
    PureEffectRow,
    RefinedType,
    Type,
    TypeVar,
    UnknownType,
    base_type,
    pretty_type,
    structural_type_key,
    substitute,
)

__all__ = [
    "EMPTY_ALIAS_ENV",
    "UNBOUNDED",
    "AliasEnv",
    "NameSort",
    "RefinementBinder",
    "alias_body",
    "alias_env_from_environment",
    "classify_named",
    "family_base_name",
    "family_name",
    "predicate_binder_key",
    "refinement_binder_parts",
    "resolve_type_expr",
    "slot_name",
    "slot_name_or_none",
    "slot_ref_key",
    "type_arg_name",
    "with_type_params",
]


# =====================================================================
# The naming environment
# =====================================================================

@dataclass(frozen=True)
class AliasEnv:
    """The module-scoped naming context: aliases plus type params in scope.

    Vera's alias namespace is MODULE-scoped (spec §8.4.1), so one of these
    describes one module's view.  *aliases* maps an alias name to its
    SYNTACTIC body (``TypeAliasInfo.body``, #1208) in DECLARATION ORDER —
    the order is load-bearing, see the module docstring.  *alias_params* is
    the same key set mapped to each alias's declared type parameters
    (``None`` for a non-parameterised alias).  *type_params* is the set of
    type-variable names in scope at the point being rendered; a type
    parameter SHADOWS a same-named alias, which is why it is tested first.
    *data_types* maps each declared ADT name to its DECLARATION INDEX, in the
    same shared index space as ``_order`` (#1208).  An ADT matters to naming
    only because a user ADT may take a name the resolver otherwise treats
    specially — and whether it does so depends on where it was declared
    relative to the alias body asking, hence the index rather than a flat
    set; see :func:`_resolve_named`.  A built-in ADT carries ``-1``: it
    precedes every user declaration and is therefore always visible.
    """

    aliases: Mapping[str, ast.TypeExpr]
    alias_params: Mapping[str, tuple[str, ...] | None]
    type_params: frozenset[str] = frozenset()
    data_types: Mapping[str, int] = field(default_factory=dict)
    # Alias name -> declaration index, so an alias body can be resolved
    # against only the declarations that precede it.  Shares ONE index space
    # with ``data_types``, which is what lets the bound order the two
    # registries against each other.  Also the per-env memo of
    # already-resolved alias bodies (an alias's restricted resolution is
    # fixed, so it is computed at most once).
    _order: Mapping[str, int] = field(
        default_factory=dict, repr=False, compare=False)
    _memo: dict[str, Type] = field(
        default_factory=dict, repr=False, compare=False)

    def __post_init__(self) -> None:
        if not self._order:
            object.__setattr__(
                self, "_order",
                {name: i for i, name in enumerate(self.aliases)},
            )


EMPTY_ALIAS_ENV = AliasEnv(aliases={}, alias_params={})
"""The alias-free environment.

Legitimate ONLY where the caller can show no alias can be in scope — a
rendering of built-in / synthesized type expressions that never came from
user source.  Every use must be able to state that argument: reaching for
this constant because an environment is inconvenient to thread is exactly
the "renders one way, is looked up another" failure #1208 exists to close,
and it fails SILENTLY (an alias renders opaquely, the key misses).
"""


def alias_env_from_environment(env: object) -> AliasEnv:
    """Build the naming env from a live checker/verifier ``Environment``.

    Reads the syntactic bodies recorded by ``_register_alias``
    (``TypeAliasInfo.body``, #1208).  An entry whose body is ``None`` — a
    ``TypeAliasInfo`` built by some future path that has no TypeExpr in hand
    — is OMITTED rather than guessed at, so it renders opaquely (the
    conservative direction: an opaque head is what the checker produces for
    an unknown name anyway).  ``env.type_params`` supplies the shadowing set
    and ``env.data_types`` the declared-ADT set, so the result reflects the
    checker's state at the moment it is called, mid-check type parameters
    included.
    """
    aliases: dict[str, ast.TypeExpr] = {}
    alias_params: dict[str, tuple[str, ...] | None] = {}
    order: dict[str, int] = {}
    type_aliases = getattr(env, "type_aliases", {})
    for name, info in type_aliases.items():
        body = getattr(info, "body", None)
        if body is None:
            continue
        aliases[name] = body
        alias_params[name] = getattr(info, "type_params", None)
        order[name] = getattr(info, "decl_index", -1)
    data_types = {
        name: getattr(info, "decl_index", -1)
        for name, info in getattr(env, "data_types", {}).items()
    }
    return AliasEnv(
        aliases=aliases,
        alias_params=alias_params,
        type_params=frozenset(getattr(env, "type_params", {})),
        data_types=data_types,
        _order=order,
    )


def with_type_params(env: AliasEnv, params: Iterable[str]) -> AliasEnv:
    """*env* with *params* added to the shadowing set.

    A type parameter shadows a same-named alias for the whole scope it is
    declared over (a ``forall<T>`` signature, an alias's own parameters), so
    entering such a scope means extending the env, never mutating it.
    """
    return AliasEnv(
        aliases=env.aliases,
        alias_params=env.alias_params,
        type_params=env.type_params | frozenset(params),
        data_types=env.data_types,
        _order=env._order,
        # Sharing the memo across the narrowing is sound because what it
        # caches is keyed by each ALIAS's own parameters, not by
        # ``env.type_params``: an alias body resolves under the parameters
        # its own declaration binds, and the shadowing set only decides
        # whether a name is looked up as an alias at all — a decision taken
        # before the memo is consulted.  Revisit this if a memo entry ever
        # becomes sensitive to the enclosing shadowing set; then the memo has
        # to be keyed by it, or dropped here.
        _memo=env._memo,
    )


# =====================================================================
# Resolution — the checker's `_resolve_type`, as a pure function
# =====================================================================

_UNBOUNDED = sys.maxsize
"""The visibility bound for a rendering that is NOT inside an alias body.

The checker resolves a parameter's type expression after registration has
finished, so every declaration is in scope; only an alias BODY is bounded,
and only by its own declaration index.  A sentinel rather than
``len(env.aliases)``, because the index space is shared with the ADTs and so
runs past the alias count.
"""

UNBOUNDED = _UNBOUNDED
"""Public spelling of the unbounded visibility limit, for callers of
:func:`classify_named` outside an alias body — which is every consumer that
is not this module's own alias resolution."""


class NameSort(enum.Enum):
    """Which branch of the ONE resolution spine a type NAME takes.

    The spine is :func:`classify_named`, and this is its answer.  Every
    derivation that needs to know what a name MEANS — the checker's
    ``_resolve_named``, codegen's WAT-width derivation, the WASM layer's
    canonicalisation — asks for this rather than re-implementing the branch
    order, because a derivation that orders the branches differently
    disagrees with the type the program was checked and verified against
    (#1309, #1316, #1321, #1331).
    """

    TYPE_PARAM = "type_param"
    """A ``forall`` variable or an alias's own parameter.  Shadows everything."""

    PRIMITIVE = "primitive"
    """A member of :data:`vera.types.PRIMITIVES`, written without arguments."""

    ALIAS = "alias"
    """A ``type`` alias visible here, applied at its declared arity.
    :func:`alias_body` gives the body with the supplied arguments substituted."""

    ALIAS_ARITY_MISMATCH = "alias_arity_mismatch"
    """A visible alias applied at the WRONG arity — the checker reports E133
    and produces an unknown type.  A separate sort because the name IS the
    alias's; it is only unusable at this application."""

    DECLARED_ADT = "declared_adt"
    """A ``data`` declaration this namespace can see, at or before this
    point in the shared declaration-index space.  Ahead of every built-in
    interpretation of the name: §8.4.1 lets a declaration take a name the
    prelude or a built-in container already uses, and the declaration wins."""

    BUILTIN = "builtin"
    """Nothing this namespace declares — so whatever the name means globally:
    a built-in container (``Array`` / ``Map`` / ``Set`` / ``Tuple``), the
    opaque ``Decimal``, a removed alias, or an unknown name that resolves to
    an opaque ADT.  Which of those it is a REPRESENTATION question, and the
    caller answers it; the spine's job ends at "not declared here"."""


def classify_named(
    te: ast.NamedType,
    env: AliasEnv,
    *,
    type_params: frozenset[str] | None = None,
    limit: int = _UNBOUNDED,
) -> NameSort:
    """THE resolution spine: which branch does ``te.name`` take in *env*?

    Type parameter (SHADOWS everything) -> primitive -> alias (arity-checked)
    -> DECLARED ADT -> everything built-in.  This is the order
    :func:`_resolve_named` documents and the order the checker resolves in;
    it lives here, once, so no consumer can hold a different one.

    *type_params* defaults to ``env.type_params``; *limit* bounds visibility
    to declarations with index ``< limit`` and is only ever narrowed inside an
    alias BODY (see :func:`_resolve_alias`).  Every other caller leaves it
    :data:`UNBOUNDED`.

    Pure and total: no diagnostics, no exceptions, no state.
    """
    params = env.type_params if type_params is None else type_params
    name = te.name
    if name in params:
        return NameSort.TYPE_PARAM
    if name in PRIMITIVES and not te.type_args:
        return NameSort.PRIMITIVE
    idx = env._order.get(name)
    # ``name in env.aliases`` is what makes the branch TOTAL: the two maps
    # agree for every environment this module builds, but an env assembled
    # elsewhere with an ``_order`` entry and no body must fall through to the
    # ADT branch rather than raise.
    if idx is not None and idx < limit and name in env.aliases:
        declared = env.alias_params.get(name) or ()
        supplied = len(te.type_args) if te.type_args else 0
        if supplied != len(declared):
            return NameSort.ALIAS_ARITY_MISMATCH
        return NameSort.ALIAS
    adt_idx = env.data_types.get(name)
    if adt_idx is not None and adt_idx < limit:
        return NameSort.DECLARED_ADT
    return NameSort.BUILTIN


def alias_body(
    te: ast.NamedType,
    env: AliasEnv,
    *,
    type_params: frozenset[str] | None = None,
    limit: int = _UNBOUNDED,
) -> ast.TypeExpr:
    """The SYNTACTIC body an :attr:`NameSort.ALIAS` classification names,
    with ``te``'s arguments substituted for the alias's own parameters.

    The syntactic counterpart of the semantic substitution
    :func:`_resolve_named` performs — for the consumers that must keep
    walking type EXPRESSIONS (codegen's width derivation, the WASM layer's
    canonicalisation) rather than land on a :class:`~vera.types.Type`.  Both
    halves therefore take one branch decision from :func:`classify_named` and
    substitute the same arguments into the same body.

    Only meaningful when :func:`classify_named` returned
    :attr:`NameSort.ALIAS`; calling it otherwise raises ``KeyError``.
    """
    # Imported inside the call because :mod:`vera.monomorphize` imports THIS
    # module.  ``substitute_type_vars`` is a pure ``TypeExpr -> TypeExpr``
    # walker with no monomorphization state, and it is the substitution every
    # existing consumer of an alias body already performs — sharing it is what
    # keeps the syntactic half of the spine identical to the semantic half.
    from vera.monomorphize import substitute_type_vars

    body = env.aliases[te.name]
    declared = env.alias_params.get(te.name) or ()
    if te.type_args and declared and len(declared) == len(te.type_args):
        return substitute_type_vars(body, dict(zip(declared, te.type_args)))
    return body


def resolve_type_expr(te: ast.TypeExpr, env: AliasEnv) -> Type:
    """Resolve *te* to the semantic :class:`~vera.types.Type` the checker's
    ``_resolve_type`` would produce for it.

    Clause of THE RULE: this is the ARGUMENT-position resolution — full
    alias resolution, refinements preserved as :class:`RefinedType`, an
    unresolvable type expression as :class:`UnknownType` (renders ``?``).
    Total: it reports no diagnostics and raises nothing, where the checker
    would additionally emit E133 / E134 / E135 and return the same type.
    """
    return _resolve(te, env, env.type_params, _UNBOUNDED)


def _resolve(
    te: ast.TypeExpr,
    env: AliasEnv,
    type_params: frozenset[str],
    limit: int,
) -> Type:
    """``_resolve_type`` with the alias-visibility bound *limit* (only
    aliases whose declaration index is ``< limit`` are in scope) and an
    explicit *type_params* set (an alias body sees its OWN parameters, not
    the caller's — matching the ``saved_params`` swap in
    ``_register_alias``)."""
    if isinstance(te, ast.NamedType):
        return _resolve_named(te, env, type_params, limit)
    if isinstance(te, ast.FnType):
        params = tuple(_resolve(p, env, type_params, limit) for p in te.params)
        ret = _resolve(te.return_type, env, type_params, limit)
        eff = _resolve_effect_row(te.effect, env, type_params, limit)
        return FunctionType(params, ret, eff)
    if isinstance(te, ast.RefinementType):
        return RefinedType(
            _resolve(te.base_type, env, type_params, limit), te.predicate)
    return UnknownType()


def _resolve_named(
    te: ast.NamedType,
    env: AliasEnv,
    type_params: frozenset[str],
    limit: int,
) -> Type:
    """``_resolve_named_type``'s branch order, exactly.

    The order itself lives in :func:`classify_named` — the ONE spine every
    derivation asks — and this function is its semantic arm: given the
    branch, produce the :class:`~vera.types.Type` the checker would.

    Type parameter (SHADOWS everything) -> primitive -> alias (arity-checked,
    substituted) -> DECLARED ADT -> ``Decimal`` (opaque, arguments dropped)
    -> removed alias (``?``) -> opaque ADT.  The checker's built-in-container
    branch (``Array``/``Tuple``/``Map``/``Set``) is absorbed by the last one:
    it builds ``AdtType(name, args)`` from the same resolved arguments, and
    its extra work is E135 diagnostics, which naming does not emit.

    The declared-ADT branch, by contrast, is NOT absorbable, and it must sit
    exactly where the checker puts it — ahead of the ``Decimal`` and removed
    -alias branches.  A user may declare ``data Float`` or ``data Decimal``
    (both check clean), and for those the checker takes the ADT branch first:
    ``@Option<Float>`` renders ``Option<Float>``, not ``Option<?>``, and a
    user ``Decimal`` keeps its type arguments (``Option<Decimal<Int>>``)
    instead of having them dropped by the built-in ``Decimal`` branch.

    ADT visibility is bounded by declaration index exactly as alias
    visibility is, because the two registries share ONE index space (#1208).
    ``type M = Decimal;`` declared ABOVE ``data Decimal`` resolved, at
    registration time, against a table that did not yet hold the ADT — so the
    built-in ``Decimal`` branch is what the checker took, and what is taken
    here.  Declared below it, the ADT branch wins on both sides.  The bound
    only ever matters for an ADT named after a removed alias or a built-in in
    the first place; every other ADT reaches the same opaque ``AdtType``
    whichever branch it takes.
    """
    name = te.name
    sort = classify_named(te, env, type_params=type_params, limit=limit)
    if sort is NameSort.TYPE_PARAM:
        # `env.type_params` maps every name to `TypeVar(name)`.
        return TypeVar(name)
    if sort is NameSort.PRIMITIVE:
        return PRIMITIVES[name]
    if sort is NameSort.ALIAS_ARITY_MISMATCH:
        return UnknownType()  # checker: E133, then UnknownType
    if sort is NameSort.ALIAS:
        params = env.alias_params.get(name) or ()
        body = _resolve_alias(name, env)
        if te.type_args and params:
            args = tuple(
                _resolve(a, env, type_params, limit) for a in te.type_args)
            return substitute(body, dict(zip(params, args)))
        return body
    if sort is NameSort.BUILTIN:
        if name == "Decimal":
            return AdtType("Decimal", ())  # checker: E134 when args supplied
        if name in REMOVED_ALIASES:
            return UnknownType()
    return AdtType(name, tuple(
        _resolve(a, env, type_params, limit) for a in te.type_args
    ) if te.type_args else ())


def _mentioned_names(te: ast.TypeExpr, out: list[str]) -> None:
    """Every type NAME written anywhere in *te*, deliberately over-approximated.

    Used only to order alias resolution (see :func:`_resolve_alias`), never to
    decide a rendering — so it collects names a resolution would skip (a
    shadowing type parameter, an arity mismatch, a primitive) rather than
    re-deciding :func:`_resolve_named`'s branch order.  Over-approximating is
    what keeps it from drifting: resolving one extra alias early is inert,
    since an alias's own resolution does not depend on who asked for it.
    """
    if isinstance(te, ast.NamedType):
        out.append(te.name)
        for arg in te.type_args or ():
            _mentioned_names(arg, out)
    elif isinstance(te, ast.FnType):
        for param in te.params:
            _mentioned_names(param, out)
        _mentioned_names(te.return_type, out)
        if isinstance(te.effect, ast.EffectSet):
            for ref in te.effect.effects:
                for arg in getattr(ref, "type_args", None) or ():
                    _mentioned_names(arg, out)
    elif isinstance(te, ast.RefinementType):
        _mentioned_names(te.base_type, out)


def _resolve_alias(name: str, env: AliasEnv) -> Type:
    """The alias's registration-time ``resolved_type``, recomputed.

    Resolved against only the aliases DECLARED BEFORE it and with only its
    own type parameters in scope — the state ``_register_alias`` had when it
    resolved that body.  The strictly-decreasing visibility bound makes the
    resolution well-founded, so a cyclic or forward-referencing alias
    terminates on the opaque placeholder the checker also produces.

    ITERATIVE, dependency-first, because the chain length is the user's to
    choose and the checker's is O(1) per hop (it stores each alias's
    ``resolved_type`` at registration).  A recursive descent spent Python
    frames per hop and died on a legal program — ``type A1 = A0; type A2 =
    A1; …`` at ~340 hops raised an uncaught ``RecursionError`` from inside a
    renderer this module's docstring calls TOTAL (#1208 review, probe
    ``d01_deep_chain``).  Every alias a body mentions has a strictly smaller
    declaration index, so the mention graph is a DAG.

    ONE dependency is pushed per iteration, and that is the load-bearing
    detail rather than a stylistic one.  Pushing a body's whole pending list
    at once puts SIBLINGS in progress together, and the ``in_progress`` guard
    below then FILTERS a sibling that is also a real dependency — so the body
    is resolved with that sibling still unmemoized and ``_resolve`` reaches it
    through a nested ``_resolve_alias``, one Python frame per level.  ``type
    Bk = D(k-1); type Ck = Drop<Bk>; type Dk = Drop2<Bk, Ck>;`` is that shape,
    and it raised ``RecursionError`` from the same renderer at a few hundred
    levels (#1208 round-2 review, probe ``sib_300``).  Pushing one at a time
    leaves only this walk's ANCESTORS in progress, and an ancestor can never
    be a pending dependency (its index is strictly larger), so nothing is ever
    filtered: by the time a body is resolved every alias it mentions is in the
    memo, and the ``_resolve_alias`` calls underneath it return from the memo
    without recursing.  The Python nesting is therefore ONE frame below this
    one, whatever the chain length — the depth of the ``_resolve`` walk itself
    stays bounded by the alias body's own syntactic nesting.

    Equivalence with the checker is preserved exactly — this is an evaluation
    ORDER, not a depth bound, so a long chain still renders its real
    resolution rather than a truncated ``?``.
    """
    memo = env._memo
    cached = memo.get(name)
    if cached is not None:
        return cached
    stack: list[str] = [name]
    # Exactly this walk's ancestors — see the docstring.  Defence in depth,
    # and provably inert on any environment this module builds: the visibility
    # bound strictly decreases along a dependency edge, so an ancestor's index
    # is strictly larger than every pending dependency's and can never be one
    # of them.  Should that invariant ever be broken, skipping an in-progress
    # name terminates on the same opaque placeholder the checker produces
    # instead of spinning.
    in_progress: set[str] = {name}
    while stack:
        cur = stack[-1]
        if cur in memo:
            in_progress.discard(cur)
            stack.pop()
            continue
        limit = env._order[cur]
        mentioned: list[str] = []
        _mentioned_names(env.aliases[cur], mentioned)
        pending = next((
            ref for ref in mentioned
            if ref not in memo
            and ref not in in_progress
            and ref in env.aliases
            and env._order.get(ref, _UNBOUNDED) < limit
        ), None)
        if pending is not None:
            # ONE at a time, so only ancestors are ever in progress and no
            # real dependency is filtered.  Strictly smaller indices, so the
            # stack cannot cycle and each alias is resolved at most once
            # (a later push hits the memo).
            stack.append(pending)
            in_progress.add(pending)
            continue
        memo[cur] = _resolve(
            env.aliases[cur], env,
            frozenset(env.alias_params.get(cur) or ()), limit)
        in_progress.discard(cur)
        stack.pop()
    return memo[name]


def _resolve_effect_row(
    er: ast.EffectRow,
    env: AliasEnv,
    type_params: frozenset[str],
    limit: int,
) -> EffectRowType:
    """``_resolve_effect_row``, as a pure function.

    An effect name that is a type parameter in scope is the row VARIABLE
    (effect polymorphism), not an instance.  The rendering
    (:func:`~vera.types.pretty_effect`, reached through ``pretty_type`` on a
    ``FunctionType``) sorts the instances, so a row renders identically
    across hash seeds.
    """
    if isinstance(er, ast.EffectSet):
        instances: list[EffectInstance] = []
        row_var: str | None = None
        for ref in er.effects:
            if isinstance(ref, ast.EffectRef):
                if ref.name in type_params:
                    row_var = ref.name
                    continue
                instances.append(EffectInstance(ref.name, tuple(
                    _resolve(a, env, type_params, limit) for a in ref.type_args
                ) if ref.type_args else ()))
            elif isinstance(ref, ast.QualifiedEffectRef):
                instances.append(EffectInstance(
                    f"{ref.module}.{ref.name}", tuple(
                        _resolve(a, env, type_params, limit)
                        for a in ref.type_args
                    ) if ref.type_args else ()))
        return ConcreteEffectRow(frozenset(instances), row_var)
    return PureEffectRow()


# =====================================================================
# The renderers
# =====================================================================

def slot_name(te: ast.TypeExpr, env: AliasEnv) -> str:
    """THE renderer: the slot-matching name of a parameter type expression.

    Clause of THE RULE: SYNTACTIC head, RESOLVED arguments.  A named type
    with no arguments renders as itself (an alias stays opaque — ``@PosInt``
    counts ``PosInt`` bindings, not ``Int``); with arguments it renders
    ``Head<arg, arg>`` where each argument goes through
    :func:`type_arg_name`.  A refinement renders its base's name; a function
    type renders the synthetic ``Fn``; anything else renders ``?``.  Total.
    """
    if isinstance(te, ast.NamedType):
        if te.type_args:
            # Each argument through :func:`type_arg_name`, then the checker's
            # own join shape (``Head<a, b>``, ", "-separated).  Routed through
            # the argument renderer rather than handing resolved
            # :class:`~vera.types.Type` values straight to
            # ``canonical_type_name``, so the two ways of asking "what does
            # this type argument render as?" are ONE way — the docstring
            # below promised that composition and it has to be real.  The join
            # is the only thing restated here, and it cannot drift silently:
            # the corpus differential's reference side calls
            # ``canonical_type_name`` directly, so a divergence in either the
            # separator or the bracketing goes red across every parameterised
            # rendering in the corpus.
            return "{}<{}>".format(
                te.name,
                ", ".join(type_arg_name(a, env) for a in te.type_args),
            )
        return te.name
    if isinstance(te, ast.RefinementType):
        return slot_name(te.base_type, env)
    if isinstance(te, ast.FnType):
        return "Fn"
    return "?"


def slot_name_or_none(te: ast.TypeExpr, env: AliasEnv) -> str | None:
    """:func:`slot_name`, with the unnameable ``?`` reported as ``None``.

    The subsystems downstream of the checker carry a ``str | None`` naming
    contract and branch on ``None`` to skip (a ``CodegenSkip``, an untranslated
    SMT term).  ``?`` is the checker's ``UnknownType`` rendering — a type
    expression the checker could not resolve either — so it is the one
    rendering that should still take those branches.  Everything else now
    HAS a name, including the shapes the pre-#1208 syntactic builder gave up
    on (a function type nested in a type argument): the checker binds those,
    so binding them here is what makes the two sides agree.
    """
    name = slot_name(te, env)
    return None if name == "?" else name


def type_arg_name(te: ast.TypeExpr, env: AliasEnv) -> str:
    """The ARGUMENT-position rendering of a type expression.

    Clause of THE RULE: fully resolved, then rendered by the checker's own
    :func:`~vera.types.pretty_type` — so a refinement renders its
    predicate-elided ``{@Int | ...}`` form, a function type its full
    ``fn(...) effects(...)`` spelling with a SORTED effect row, and anything
    unresolvable renders ``?``.  This is exactly the per-argument rendering
    :func:`slot_name`'s join performs — literally, since #1208 review:
    ``slot_name`` calls this per argument rather than composing the same two
    steps itself, so the two answers are one answer by construction.
    """
    return pretty_type(resolve_type_expr(te, env))


def slot_ref_key(ref: ast.SlotRef, env: AliasEnv) -> str:
    """The binding-table key a ``@T.n`` reference looks itself up under.

    Clause of THE RULE: identical to :func:`slot_name` over the reference's
    head and arguments — the checker's ``_slot_ref_key`` routes through the
    same renderer as the binding side, and a reference that rendered
    differently from the binding would miss, silently.
    """
    return slot_name(
        ast.NamedType(name=ref.type_name, type_args=ref.type_args), env)


def predicate_binder_key(predicate: ast.Expr, env: AliasEnv) -> str | None:
    """The key a refinement predicate's BINDER must be pushed under (#1226).

    Clause of THE RULE, from the reference side: a predicate is closed over one
    binder, so the key the binder is bound under is by definition the key that
    binder's own reference resolves through — :func:`slot_ref_key` over the
    predicate's first ``@T.n``.  ``None`` when the predicate holds no
    reference, in which case there is no binder to bind.  "First" is
    :func:`~vera.ast.predicate_binder_ref`'s traversal order, whose one
    documented exception (a closure inside the predicate contributing its own
    binder) costs a Tier-3 demotion, never a wrong assumption.

    Derived here rather than from the refinement's TYPE EXPRESSION because the
    consumers hold different things: the runtime guard has the type expression
    (:func:`refinement_binder_parts`, which names its base through
    :func:`slot_name`) while the SMT layer holds only the resolved type and the
    predicate.  Both answers are one rendering of one name, so they agree —
    what they must not do is what the pre-#1226 SMT push did, take the head
    identifier alone: ``{ @Box<Cnt> | @Box<Cnt>.0 >= 18 }`` pushed ``Box``
    where the reference resolves ``Box<Nat>``, the predicate silently failed to
    translate, and the refined-return fact vanished from the caller's context —
    rejecting a valid program with a spurious E501.

    *env* is the environment the predicate is being TRANSLATED in, which for a
    callee's refined return is the callee's module (its type arguments resolve
    there, and ``Box<Cnt>`` names different types in two modules).
    """
    ref = ast.predicate_binder_ref(predicate)
    return None if ref is None else slot_ref_key(ref, env)


def family_name(
    te: ast.TypeExpr | None, env: AliasEnv, fallback: str,
) -> str:
    """The State/Exn cell FAMILY name for an effect type argument (#1209).

    Clause of THE RULE, and the one place it differs: a family names a CELL,
    not a source spelling, so the head resolves too — ``State<MyAlias>``
    where ``type MyAlias = Option<Int>`` is the ``Option<Int>`` family, the
    same cell ``State<Option<Int>>`` names.  (Scalar aliases already
    collapsed this way, #1205; composite ones splitting the family was
    #1209.)  This mirrors the checker, which resolves effect-instance type
    arguments in full (``_resolve_effect_ref``), so the family agrees with
    the cell type the checker typed.

    A refinement is part of that cell type, NOT stripped from it (#1218).
    The checker keeps ``State<Pos>``, ``State<Neg>`` and ``State<Int>``
    apart over one base — ``EffectInstance`` holds the ``RefinedType``, and
    E125 rejects passing one where another is required — so collapsing them
    to ``Int`` gave three checker cells one host cell, and a callee bound to
    the outer one wrote whichever was innermost.  This is the IDENTITY
    question; a cell's REPRESENTATION (i32 / i64 / f64 / pair, which #1203
    write guard applies) is the base's, and that is
    :func:`family_base_name`.

    The rendering is :func:`~vera.types.structural_type_key`, not
    ``pretty_type`` (#1219).  A family names a cell, and two cells are one
    exactly when the CHECKER holds their types equal — so the rendering has
    to discriminate everything the checker does, and ``pretty_type`` makes
    two deliberate elisions that it does not: a refinement's predicate
    becomes ``...`` and a type variable's built-in marker is stripped.
    ``State<Option<Pos>>`` and ``State<Option<Neg>>`` both render
    ``Option<{@Int | ...}>`` under ``pretty_type``, and merging those two
    families is a shared cell behind a check that typed them apart.  The
    structural key is the same one ``TypeEnv`` orders effect rows by, so
    family identity and checker identity are one derivation rather than two
    that agree by coincidence.

    *fallback* is returned when there is no type expression and when the
    resolution has no nameable family — a top-level function type, or an
    unresolvable type.  Both are refused DOWNSTREAM, though not at the same
    gate: the unresolvable one at ``_register_state_cell`` /
    ``_register_exn_tag`` (E607 / E612), which never reaches this renderer,
    while a bare function type maps to ``i32`` and so passes that gate,
    gets named here, and is refused when its enclosing function is dropped
    (E616 at the closure read, then E602 / E620).  Either way nothing that
    reaches a running program rests on the name, so the fallback's
    only remaining job is to keep two such spellings apart rather than
    merging them onto one ``fn(…)`` or ``?``; see
    :func:`~vera.slots.family_fallback_name`.

    Until #1219 a third gate stood here: the rendering also had to be
    *mangle-safe*, meaning inside the canonical ``Head<arg, arg>`` grammar,
    because ``mangle_type_name`` escaped only that grammar and anything else
    emitted an import name the WAT parser rejects.  A resolution outside it
    (``Option<{@Int | ...}>``, ``Option<fn(Int -> Int) effects(pure)>``)
    kept the alias-opaque spelling instead — conservative, but it left a
    family split the checker does not have, and it was the only thing
    keeping the ``pretty_type`` elisions above from merging two cells.  The
    mangler is now total over canonical renderings, so the gate is gone.
    """
    if te is None:
        return fallback
    ty = resolve_type_expr(te, env)
    if isinstance(base_type(ty), (FunctionType, UnknownType)):
        return fallback
    return structural_type_key(ty)


def family_base_name(
    te: ast.TypeExpr | None, env: AliasEnv, fallback: str,
) -> str:
    """A cell's REPRESENTATION name — :func:`family_name`'s base (#1218).

    The same resolution, with the refinement wrappers stripped and rendered
    by ``pretty_type``: ``State<Pos>`` under ``type Pos = {@Int | P}``
    answers ``Int``.  Two clauses of one rule, and the split is what #1218
    is: a cell's IDENTITY must discriminate the predicate (three refinements
    of one base are three cells), while its REPRESENTATION must not (all
    three are i64, all three take the same ``@Nat``-narrowing guard, a
    refined ``String`` payload is still a pointer/length pair).  Deriving
    both from the same type expression is what keeps them from disagreeing —
    the pre-#1218 code had ONE name doing both jobs, which is why making it
    discriminate would otherwise have silently switched off every
    representation decision keyed on ``"Nat"`` / ``"Int"`` / ``"Byte"`` /
    ``"Bool"`` / ``"String"``.

    Never a symbol, and never compared against another cell's: an import
    name, a tag, ``_pushed_cell_families`` and the addressability gate all
    take :func:`family_name`, because two cells sharing a base share
    everything this answers and nothing that one answers.

    Falls back exactly as :func:`family_name` does, so the two agree about
    which type expressions have no cell at all.
    """
    if te is None:
        return fallback
    ty = base_type(resolve_type_expr(te, env))
    if isinstance(ty, (FunctionType, UnknownType)):
        return fallback
    return pretty_type(ty)


# =====================================================================
# Refinement binders
# =====================================================================

@dataclass(frozen=True)
class RefinementBinder:
    """What a refinement's runtime guard binds its predicate over.

    *predicate* is the guard's predicate, closed over ``@<binder_name>.0``;
    *binder_name* is that binder's slot name; *base* is the alias-chased
    base type expression (the caller decides whether it has a WASM
    representation); *base_is_refinement* flags a refinement whose base
    resolves to another refinement — a shape whose guard would silently drop
    the inner membership predicate, so the caller rejects it (E618).
    """

    predicate: ast.Expr
    binder_name: str
    base: ast.TypeExpr
    base_is_refinement: bool


def refinement_binder_parts(
    te: ast.TypeExpr, env: AliasEnv,
) -> RefinementBinder | None:
    """The binder a refinement's runtime guard uses, or ``None``.

    Clause of THE RULE, and THE derivation both consumers use: chase the
    alias chain (bare-name follows only, cycle-guarded) to a
    ``RefinementType``, then name its base as the predicate's binder.  It was
    a second copy of codegen's ``_refinement_guard_parts`` walk until #1208
    converged them; codegen now calls this and layers its two WASM-specific
    decisions on top (reject a nested refinement base with E618, emit no
    guard for a base that erases), because a type's REPRESENTATION is not a
    naming question and this module must not import the backend.
    ``tests/test_refinement_binder_convergence_1208.py`` is the differential
    that keeps the two from drifting apart again.

    The binder itself is named by :func:`slot_name` (#1208), so the guard
    pushes the value under exactly the key a predicate's ``@Base.n``
    resolves to through :func:`slot_ref_key` — and under the key the checker
    bound the predicate's binder to.  :func:`predicate_binder_key` asks the
    same question from the REFERENCE side, for a consumer that holds the
    predicate but not the type expression; the two meet because both render
    through :func:`slot_name`, and they are separate functions only because a
    predicate may spell its binder differently from its base (``{ @Age |
    @Nat.0 >= 18 }``), where the answers are honestly different names for one
    value.  The pre-consolidation derivation named
    the base's type arguments SYNTACTICALLY (``Array<Txt>`` for
    ``type Txt = String``), which met its reference side only because that
    side was syntactic too; with both resolved they meet on
    ``Array<String>``.

    One deliberate difference from :func:`slot_name` remains, because the
    guard and the predicate must agree with each other: the alias chain is
    followed by NAME with no substitution, so a parameterised alias
    application is chased as its head.

    The ``@Nat``/``@Byte`` implicit range predicates are conjoined here, as
    codegen does, so a value satisfying the written predicate but outside
    the base's range cannot launder past the guard.  They are NOT conjoined
    when ``base_is_refinement`` — the caller rejects that shape before it
    would use the predicate.
    """
    node: ast.TypeExpr = te
    seen: set[str] = set()
    while (isinstance(node, ast.NamedType)
           and node.name in env.aliases
           and node.name not in seen):
        seen.add(node.name)
        node = env.aliases[node.name]
    if not isinstance(node, ast.RefinementType):
        return None
    base = node.base_type
    if not isinstance(base, ast.NamedType):
        return None
    name = slot_name(base, env)
    base_node: ast.TypeExpr = base
    bseen: set[str] = set()
    while (isinstance(base_node, ast.NamedType)
           and base_node.name in env.aliases
           and base_node.name not in bseen):
        bseen.add(base_node.name)
        base_node = env.aliases[base_node.name]
    if isinstance(base_node, ast.RefinementType):
        return RefinementBinder(node.predicate, name, base_node, True)
    predicate = node.predicate
    if isinstance(base_node, ast.NamedType) and base_node.name == "Nat":
        predicate = ast.BinaryExpr(
            op=ast.BinOp.AND,
            left=ast.BinaryExpr(
                op=ast.BinOp.GE,
                left=ast.SlotRef(type_name=name, type_args=None, index=0),
                right=ast.IntLit(value=0),
            ),
            right=predicate,
        )
    elif isinstance(base_node, ast.NamedType) and base_node.name == "Byte":
        slot = ast.SlotRef(type_name=name, type_args=None, index=0)
        predicate = ast.BinaryExpr(
            op=ast.BinOp.AND,
            left=ast.BinaryExpr(
                op=ast.BinOp.AND,
                left=ast.BinaryExpr(
                    op=ast.BinOp.GE, left=slot, right=ast.IntLit(value=0)),
                right=ast.BinaryExpr(
                    op=ast.BinOp.LE, left=slot, right=ast.IntLit(value=255)),
            ),
            right=predicate,
        )
    return RefinementBinder(predicate, name, base_node, False)
