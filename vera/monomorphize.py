"""Shared generic-function monomorphization: instantiation discovery + AST
substitution.

Extracted from ``vera/codegen/monomorphize.py`` so that BOTH codegen (Pass 1.5,
for WASM emission) and the verifier (#732, per-monomorphization static
verification) drive the SAME discovery + substitution logic.  Sharing one
implementation is a *soundness requirement*: the verifier must check exactly the
instantiation set codegen emits, or a missed instantiation becomes a false
Tier-1 — ``vera verify`` reports clean while a runtime obligation is left
unproven.

This module is deliberately codegen-free.  It imports :mod:`vera.ast`, the ONE
naming renderer (:mod:`vera.naming` / :mod:`vera.slots`, #1208), and the pure
:func:`substitute_type_vars` ``TypeExpr`` walk (relocated here from
``vera/wasm/inference.py`` so importing the monomorphizer doesn't pull in the
``vera.wasm`` backend).  WASM/layout-specific concerns — ability-constraint
checking (E613) and layout-derived ``Eq`` auto-derivation — stay in
``vera/codegen/monomorphize.py``.

Discovery + substitution are exposed as methods on :class:`Monomorphizer`, which
holds a :class:`MonoContext` of registration metadata.  Each consumer builds the
context from its own state (codegen from its layout/signature mixin, the
verifier from :class:`~vera.environment.TypeEnv`) and runs its own *orchestration*
(worklist) — codegen filters constraint-failing instances via ``_check_constraints``
while building WAT; the verifier discovers a constraint-agnostic superset.  The
leaf inference + substitution they call is identical, which is what keeps the two
instantiation sets in agreement.
"""

from __future__ import annotations

import re
from collections.abc import (
    Iterable,
    Mapping,
)
from dataclasses import dataclass, field, fields, replace
from typing import Any

from vera import ast, naming
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.slots import (
    fn_slot_scope,
)

# Identifier tokens inside a rendered type name (`Map<String, Int>` →
# `Map`, `String`, `Int`).  #1271 matches type-variable names against these
# rather than by substring, so `Unit` never reads as a mention of `U`.  A
# `$`-joined name is ONE token: an owner-qualified type (`libm$Shape`, #1317)
# names one type, and a `where` helper binder renamed apart
# (`Int$shadowed`, #1433) is one type variable.
_TYPE_NAME_TOKENS = re.compile(r"[A-Za-z_][A-Za-z_0-9$]*")


def substitute_type_vars(
    te: ast.TypeExpr,
    subst: dict[str, ast.TypeExpr],
) -> ast.TypeExpr:
    """Substitute type variables inside a TypeExpr.

    Module-level so it's accessible from `InferenceMixin`
    (`vera/wasm/inference.py` — the canonicaliser, called from
    interpolation/apply_fn inference), `CodeGenerator`
    (`vera/codegen/core.py` — the compilability check
    `_type_expr_to_wasm_type`), and :func:`resolve_fn_type_alias`
    below — the shared transitive walker behind
    `Monomorphizer._resolve_arg_fn_shape` /
    `CallsMixin._resolve_arg_fn_shape_wasm` (#604 / #659 CR-4 +
    CR-5, routed through the resolver by PR #880).  All sites need
    the same substitution semantics when
    following a parameterised alias (`type Box<T> = Array<T>`,
    `type Mapper<T> = fn(T -> T)`) so the alias's own type-param
    references in the body get bound to the concrete type arguments
    from the call site (#635 closes the compilability-side gap that
    PR #631's walker fix didn't reach).

    A "type variable reference" is a bare `NamedType(name=X,
    type_args=None|())` whose name is a key in `subst`; it gets
    replaced wholesale by `subst[X]`.  `NamedType` with non-bare
    type_args is recursed into (substituting in each arg).
    `RefinementType` substitutes its `base_type`; the `predicate`
    is left untouched (predicates are `Expr`, not `TypeExpr`, and
    canonicalisation is type-level only).  `FnType` substitutes
    through each param and the return type (added by #659 CR-4 +
    CR-5 for parameterised FnType aliases).  Other shapes pass
    through unchanged.
    """
    if isinstance(te, ast.NamedType):
        if not te.type_args and te.name in subst:
            return subst[te.name]
        if te.type_args:
            new_args = tuple(
                substitute_type_vars(a, subst) for a in te.type_args
            )
            return ast.NamedType(name=te.name, type_args=new_args)
        return te
    if isinstance(te, ast.RefinementType):
        new_base = substitute_type_vars(te.base_type, subst)
        return ast.RefinementType(
            base_type=new_base, predicate=te.predicate)
    if isinstance(te, ast.FnType):
        new_params = tuple(
            substitute_type_vars(p, subst) for p in te.params
        )
        new_return = substitute_type_vars(te.return_type, subst)
        # `effect` is passed through unchanged.  All current
        # parameterised FnType aliases use `effects(pure)` or
        # similarly-monomorphic effects.  If a future type
        # introduces `effects(<State<T>>)` or similar where `T`
        # is an alias parameter, the substitution would NOT
        # propagate into the effect row — this is a deliberate
        # gap noted in the #659 review (type-design analyzer
        # finding 3).  The corresponding regression test in
        # `tests/test_wasm.py::TestSubstituteTypeVarsFnType`
        # pins this contract so a future refactor doesn't
        # silently change behaviour.
        return ast.FnType(
            params=new_params,
            return_type=new_return,
            effect=te.effect,
        )
    return te


def resolve_type_alias(
    te: ast.TypeExpr,
    type_aliases: Mapping[str, ast.TypeExpr],
    type_alias_params: Mapping[str, tuple[str, ...] | None],
) -> ast.TypeExpr | None:
    """Resolve a ``TypeExpr`` through the alias chain to its terminal shape.

    The general transitive alias walker every representation-level
    classifier shares — :func:`resolve_fn_type_alias` below is the
    fn-type-specialised view over this walk, and the fused-await
    classifier (``vera/wasm/async_fusion.py``, #1109) uses it to
    resolve alias-typed slots and declared returns before its literal
    ``Future<Result<String, String>>`` check.  Aliases are transparent
    everywhere else in the language; a classifier that probes runtime
    representation must see through them too.

    Lives here — the deliberately codegen-free shared monomorphizer
    module (see the module docstring / #732) — so the WASM backend,
    the codegen-free fusion predicates, and the monomorphizer can all
    import it without an import cycle.

    Walks iteratively (until a terminal shape or a cycle):

    1. Unwraps ``RefinementType`` layers (any nesting depth) — callers
       classify by runtime representation, and a refinement's
       representation is its base type's.
    2. A bared ``FnType`` is terminal wherever it appears.
    3. For a ``NamedType`` found in ``type_aliases``, substitutes the
       current ``type_args`` into the alias's type params (for a generic
       alias like ``type Producer<T> = Future<T>``) and follows the
       chain one hop.
    4. A ``NamedType`` that is not an alias is terminal — returned
       as-is (a primitive, an ADT, the literal ``Future<...>``).

    Returns the terminal ``TypeExpr``, or ``None`` only on a cyclic
    alias chain (``type A = B; type B = A``).  The type checker rejects
    circular aliases upstream (``[E132]``, #648); the guard makes the
    resolver terminate with ``None`` (the caller then falls to its loud
    backstop) rather than spin forever — the same defence-in-depth
    ``InferenceMixin._resolve_base_type_name`` and
    ``_canonical_named_type`` carry.
    """
    seen: set[str] = set()
    while True:
        while isinstance(te, ast.RefinementType):
            te = te.base_type
        if isinstance(te, ast.FnType):
            return te
        if not isinstance(te, ast.NamedType):
            return te
        if te.name in seen:
            return None
        seen.add(te.name)
        alias = type_aliases.get(te.name)
        if alias is None:
            return te
        # Bind this hop's concrete type args to the alias's params so a
        # generic alias body's type-var references resolve to the bound
        # types (``type Producer<T> = Future<T>`` used as
        # ``Producer<Result<...>>`` → ``Future<Result<...>>``).
        params = type_alias_params.get(te.name)
        if params and te.type_args and len(params) == len(te.type_args):
            alias = substitute_type_vars(alias, dict(zip(params, te.type_args)))
        if isinstance(alias, (ast.FnType, ast.NamedType, ast.RefinementType)):
            te = alias
            continue
        return None


def resolve_fn_type_alias(
    te: ast.TypeExpr,
    type_aliases: Mapping[str, ast.TypeExpr],
    type_alias_params: Mapping[str, tuple[str, ...] | None],
) -> ast.FnType | None:
    """Resolve a ``TypeExpr`` to the ``FnType`` it aliases, transitively.

    The single transitive-alias-to-fn-type resolver behind every site
    that discovers a function type through an alias — the ``apply_fn``
    ``call_indirect`` signature builder (``_infer_apply_fn_return_type``),
    its Vera-type twin (``_infer_fncall_vera_type``), the fused-await
    classifier (``_apply_fn_closure_ret_type``,
    ``vera/wasm/async_fusion.py``), and the generic higher-order-fn
    consultors (``Monomorphizer._resolve_arg_fn_shape`` /
    ``_infer_fn_alias_type_args`` below, and their WASM call-rewrite
    twins in ``vera/wasm/calls.py``).  Routing every site through this
    one walker makes their depth-N behaviour structurally identical
    rather than replicated per-site: a single-level unwrap at any one
    site desynced it from the signal it must agree with (#867 — a
    two-hop ``type Fetcher = InnerFetcher;`` resolved one hop, saw a
    ``NamedType`` not a ``FnType``, bailed, and consultors diverged
    into a silent identity await / an ``i64``-defaulted
    ``call_indirect`` signature that trapped at WASM validation; the
    PR #880 review found the same single-hop miss in the generic-HOF
    consultors, where a closure-bound type param fell to the
    phantom-var default).

    Lives here — the deliberately codegen-free shared monomorphizer
    module (see the module docstring / #732) — so the WASM backend,
    the codegen-free fusion predicates, and the monomorphizer can all
    import it without an import cycle (``vera/wasm/async_fusion.py``
    imports this module, so it cannot host a helper this module needs).

    The walk itself lives in :func:`resolve_type_alias` above — this is
    the fn-type-specialised view over it: the terminal shape is returned
    iff it is an ``FnType``, else ``None`` (a bare ``NamedType`` that is
    not an alias, a primitive, a terminal ADT — no ``FnType``
    reachable).  Deriving the two from one walk keeps their depth-N
    behaviour structurally identical: refinement layers unwrap at any
    nesting depth (including an alias body that is a refinement
    DIRECTLY wrapping an inline fn type — ``type Foo = { @fn(...) | p
    };`` — PR #880 review, CodeRabbit Major), a bared ``FnType`` is
    terminal wherever it appears, generic alias params are substituted
    hop by hop (``type Producer<T> = fn(String -> T)`` used as
    ``Producer<Future<...>>`` → ``fn(String -> Future<...>)``), and the
    ``seen`` guard terminates a cyclic alias chain with ``None``
    (defence-in-depth; the checker rejects cycles upstream with
    ``[E132]``, #648).
    """
    resolved = resolve_type_alias(te, type_aliases, type_alias_params)
    return resolved if isinstance(resolved, ast.FnType) else None


def canonicalize_type_aliases(
    te: ast.TypeExpr,
    type_aliases: dict[str, ast.TypeExpr],
    type_alias_params: dict[str, tuple[str, ...]],
    _depth: int = 0,
) -> ast.TypeExpr:
    """Substitute every alias reference in *te* with its target, deeply (#1111).

    :func:`resolve_type_alias` above follows the alias chain at the ROOT
    of a type expression only — ``Array<F>`` is terminal there because
    ``Array`` is no alias, so the element alias ``F`` survives.  This
    walker rewrites nested positions too, producing an alias-free
    ("canonical") expression: alias names are resolved with their
    defining namespace's maps and the result carries no name that a
    later consumer could re-resolve against the WRONG namespace.

    That is exactly the module-harvest contract (#1111): spec §8.4.1 makes
    type aliases module-local, so a module's return-type expressions are
    canonicalized against the module's OWN alias maps at harvest time and
    the shared registry (``_fn_ret_type_exprs``) stays namespace-free by
    construction.

    Scope and deliberate limits:

    - ``NamedType``: an alias name is substituted (binding its type args
      to the alias's params, like :func:`resolve_type_alias`) and the
      substitution re-walked; a non-alias name keeps its identity and
      gets canonicalized type args.
    - ``FnType``: params and return type are canonicalized; the effect
      row is left verbatim.  The harvested-registry consumers (the
      fused-await classifier and index-element extraction) never consult
      effect-row type args, so a leftover alias name there is never
      cross-namespace-resolved.
    - ``RefinementType``: the base type is canonicalized, the predicate
      kept verbatim — refinement predicates are only evaluated while
      compiling the defining declaration, where the per-module alias
      scope (``_module_alias_scope``) is active.
    - Unknown / unhandled shapes return unchanged — conservative: the
      pre-#1111 behaviour, never a wrong substitution.

    The depth guard terminates a cyclic alias chain by returning the
    expression as-is (defence-in-depth; the checker rejects circular
    aliases upstream with ``[E132]``, #648 — same posture as
    :func:`resolve_type_alias`'s ``seen`` guard).
    """
    if _depth > 64:
        return te
    if isinstance(te, ast.NamedType):
        alias = type_aliases.get(te.name)
        if alias is not None:
            params = type_alias_params.get(te.name)
            if params and te.type_args and len(params) == len(te.type_args):
                alias = substitute_type_vars(
                    alias, dict(zip(params, te.type_args)),
                )
            return canonicalize_type_aliases(
                alias, type_aliases, type_alias_params, _depth + 1,
            )
        if te.type_args:
            new_args = tuple(
                canonicalize_type_aliases(
                    a, type_aliases, type_alias_params, _depth + 1,
                )
                for a in te.type_args
            )
            if new_args != te.type_args:
                return replace(te, type_args=new_args)
        return te
    if isinstance(te, ast.FnType):
        new_params = tuple(
            canonicalize_type_aliases(
                p, type_aliases, type_alias_params, _depth + 1,
            )
            for p in te.params
        )
        new_ret = canonicalize_type_aliases(
            te.return_type, type_aliases, type_alias_params, _depth + 1,
        )
        if new_params != te.params or new_ret is not te.return_type:
            return replace(te, params=new_params, return_type=new_ret)
        return te
    if isinstance(te, ast.RefinementType):
        new_base = canonicalize_type_aliases(
            te.base_type, type_aliases, type_alias_params, _depth + 1,
        )
        if new_base is not te.base_type:
            return replace(te, base_type=new_base)
        return te
    return te


def _unshadowed(
    mapping: dict[str, str], binders: tuple[str, ...] | None,
) -> dict[str, str]:
    """*mapping* without the type variables *binders* rebind (#1433).

    A ``where`` helper's own ``forall`` binders shadow its enclosing
    function's inside the helper (spec §5.6.2), so a substitution for the
    enclosing function stops at them.  Returns *mapping* itself when nothing
    is shadowed, so the common case allocates nothing.
    """
    if not binders or not any(b in mapping for b in binders):
        return mapping
    return {k: v for k, v in mapping.items() if k not in binders}


def _capturing_binders(
    mapping: dict[str, str], binders: tuple[str, ...] | None,
) -> dict[str, str]:
    """Fresh names for the *binders* a substitution by *mapping* would
    capture (#1433): each one a replacement type in *mapping* spells.

    A helper's ``forall<Int>`` binds ``Int`` inside the helper, so the
    ``Int`` a parent's ``U -> Int`` puts in place of the helper's ``@U``
    would name the helper's parameter instead of the type.  A fresh name
    ends in ``$shadowed``: ``$`` cannot appear in a source identifier, so it
    spells no declared type, and no replacement spells it either, because a
    renamed binder is a type variable and never an instantiation
    (``_binds_a_type_var``).  Over-reading a replacement only renames a
    binder that did not need it, which is harmless.
    """
    if not binders or not mapping:
        return {}
    spelled = {
        tok for value in mapping.values()
        for tok in _TYPE_NAME_TOKENS.findall(value)
    }
    return {b: f"{b}$shadowed" for b in binders if b in spelled}


def substitute_type_param_names(name: str, mapping: dict[str, str]) -> str:
    """Substitute type-parameter NAMES inside a type-name *string* (#773).

    ``substitute_type_param_names("List<T>", {"T": "Int"})`` → ``"List<Int>"``.
    A string-level wrapper over :func:`substitute_type_vars`: the name is
    parsed to a :class:`~vera.ast.NamedType`, each bare occurrence of a mapped
    parameter is replaced by the (parsed) concrete argument, and the result is
    re-formatted.  Used by structural-Eq derivation to resolve a declared
    constructor field type like ``List<T>`` or ``Box<T>`` against a concrete
    instantiation's type arguments — the *bare*-param field case (``T``) is
    handled positionally by ``_ctor_adt_tp_indices`` upstream; this covers
    parameters nested inside a parameterized field type (the recursive-ADT
    tail ``Cons(T, List<T>)`` being the canonical case).
    """
    if not mapping or "<" not in name:
        # A bare name is either unmapped or handled positionally upstream;
        # only parameterized field types need the deep walk.
        return mapping.get(name, name)
    parsed = Monomorphizer._parse_type_name(name)
    subst: dict[str, ast.TypeExpr] = {
        param: Monomorphizer._parse_type_name(concrete)
        for param, concrete in mapping.items()
    }
    substituted = substitute_type_vars(parsed, subst)
    if isinstance(substituted, ast.NamedType):
        return Monomorphizer._format_type_name(substituted)
    return name  # pragma: no cover — NamedType in, NamedType out


def declared_return_clone_key(te: ast.TypeExpr | None) -> str | None:
    """The clone-name KEY a user fn's declared return TypeExpr contributes when
    its call result is bound to a generic's type variable.

    THE single source of truth for this key — discovery
    (:func:`vera.codegen.monomorphize._simple_return_type_name`), the #732
    verifier (``ContractVerifier._simple_type_name``), and the WASM call-rewrite
    (``InferenceMixin._declared_return_clone_name``) ALL delegate here, so the
    three consultors cannot desync by construction (#878 / #899 whack-a-mole:
    each independently re-derived this key and they diverged on parameterized
    returns and scalar-resolving aliases, dropping ``main`` at run time on a
    check-green program).

    Convention — refinement-unwrap, then the **base name** with type args
    DROPPED:

      * ``@Decimal``                 → ``"Decimal"``
      * ``@Age`` (``type Age = Int``) → ``"Age"``  (RAW alias, not resolved)
      * ``@Option<Decimal>``          → ``"Option"`` (base name only)
      * ``@{ @Int | p }``             → ``"Int"``  (refinement-unwrapped)
      * a bare ``FnType`` / anything without a NamedType base → ``None``

    The base-name-only key is **sound** for the bare-``@T`` binding it feeds:
    a ``forall<T>`` body binding a whole ADT to ``@T`` (``pick(@T, @T -> @T)``)
    is representation-polymorphic — it can only move/copy the ``i32`` handle,
    never pattern-match or project ``T`` (the body doesn't know ``T``'s
    constructors), so ``Option<Decimal>`` and ``Option<Int>`` share one identity
    clone ``pick$Option`` with byte-identical WAT.  (A parameterized *parameter*
    like ``Option<T>`` — where the body CAN project the field — is a different
    path that recovers the full type argument via ``_get_arg_type_info*``; this
    key is only the bare-``@T`` case.)
    """
    while isinstance(te, ast.RefinementType):
        te = te.base_type
    if isinstance(te, ast.NamedType):
        return te.name
    return None


# Source character -> its two-character `_X` escape code.  These, plus the
# `", "` pair below, are the PRE-#1219 alphabet and their meanings are
# FROZEN: every family name, Z3 sort, `$eq_` helper and mono clone the
# compiler already emits is named through them, so changing one renames
# symbols across the corpus.  Anything else outside `[A-Za-z0-9_]` takes the
# `_U<hex>_` escape below.
_MANGLE_CODES = {
    "_": "__",
    "<": "_L",
    ">": "_R",
    " ": "_S",
}

# The canonical argument SEPARATOR, escaped as one unit (`Map<String, Int>`
# → `Map_LString_CInt_R`).  Matched before the per-character table, so a
# comma that is NOT part of the separator — only a string literal inside a
# refinement predicate can spell one — falls through to `_U2c_` instead of
# being collapsed onto this code, which is what keeps `'a,b'` and `'a, b'`
# distinct families (#1219).
_MANGLE_SEP = ", "
_MANGLE_SEP_CODE = "_C"

# The reserved letter for the variable-length escape (`_U` + lowercase hex +
# `_`).  It may never be given to a character in `_MANGLE_CODES`; nor may
# `J`, which `Monomorphizer._mangle_fn_name` uses as the JOIN separator
# between mangled components and which therefore must stay outside the
# mangler's range.
_MANGLE_HEX = "U"


def mangle_type_name(type_name: str) -> str:
    """Escape a canonical Vera type name for embedding in a WAT identifier.

    The ONE escape convention for type names in WAT symbols (#775): the
    structural-Eq helper namer (``$eq_<type>``, ``vera/wasm/operators.py``,
    #773), the mono-clone namer (:meth:`Monomorphizer._mangle_fn_name`), the
    Z3 sort namer (``vera/smt.py``) and the State/Exn cell-family symbols
    (``vera/codegen/assembly.py``) all delegate here, so the naming families
    cannot drift apart.

    Encoding, a left-to-right scan:

    ==============  ========  ====================================
    source          code      where it comes from
    ==============  ========  ====================================
    ``_``           ``__``    any identifier
    ``<``           ``_L``    ``Head<arg>``
    ``>``           ``_R``    ``Head<arg>``
    ``", "``        ``_C``    the canonical argument separator
    ``" "``         ``_S``    a space that is not that separator
    other non-      ``_U``    everything a canonical rendering can
    ``[A-Za-z0-9_]``  ``<hex>_``  carry outside the two grammars above
    ==============  ========  ====================================

    The first five are the pre-#1219 alphabet, unchanged, so no symbol the
    compiler already emits moves.  The sixth is what makes the mangler TOTAL
    (#1219): a cell family is no longer restricted to the ``Head<arg, arg>``
    grammar, so a family name can now carry a function type's parentheses
    and arrow, an effect row, a refinement's braces and ``|`` bar, the
    canonical source form a refinement predicate renders as (#1218), and
    any character a string literal inside such a predicate spells —
    non-ASCII included.  Output is ``[A-Za-z0-9_]`` only, which is
    inside the WAT ``idchar`` set, inside the SMT-LIB simple-symbol set, and
    unchanged by the browser runtime's ``/^state_get_(.+)$/`` split.

    Injectivity (now over EVERY canonical rendering, not just
    :meth:`Monomorphizer._format_type_name`'s): the output is a
    concatenation of code units, each either a single ``[A-Za-z0-9]``
    character mapping to itself, or a unit starting with ``_`` — the
    two-character codes above, or ``_U`` followed by hex digits and a
    closing ``_``.  Decoding scans left to right: at a ``_``, the next
    character selects the unit (and ``U`` makes it variable-length,
    terminated by the ``_`` that no hex digit can be), otherwise consume
    one.  :func:`unmangle_type_name` is that scan, and
    ``unmangle_type_name(mangle_type_name(t)) == t`` for every ``t`` — a
    left inverse, which is exactly injectivity.  This kills the
    ``g<Map<String, Int>>`` vs ``g<Map_String_Int>`` collision class from
    #775 (the former encodes its brackets, the latter doubles its
    underscores) and, since #1219, the ``'a,b'`` vs ``'a, b'`` class a
    refinement predicate's string literal introduced: a comma NOT followed
    by a space is no longer collapsed onto the ``", "`` separator's code.

    NOT idempotent, and cannot be: ``mangle_type_name("Option_LInt_R")`` is
    ``"Option__LInt__R"``, because ``Option_LInt_R`` is itself a legal flat
    ADT name and must not collide with ``Option<Int>``'s symbol.  The range
    and the domain overlap, so there is likewise no sound "already mangled?"
    guard to add.  The invariant is STRUCTURAL instead: canonical names are
    carried everywhere and mangled exactly once, at symbol construction, and
    any comparison of two families is made on the canonical side.
    ``tests/test_codegen_monomorphize.py::TestMangleInjectivity`` pins the
    decision, the alphabet, and the preserved pre-#1219 symbols.
    """
    out: list[str] = []
    i = 0
    n = len(type_name)
    while i < n:
        if type_name.startswith(_MANGLE_SEP, i):
            out.append(_MANGLE_SEP_CODE)
            i += len(_MANGLE_SEP)
            continue
        ch = type_name[i]
        code = _MANGLE_CODES.get(ch)
        if code is not None:
            out.append(code)
        elif ch.isascii() and ch.isalnum():
            out.append(ch)
        else:
            out.append(f"_{_MANGLE_HEX}{ord(ch):x}_")
        i += 1
    return "".join(out)


# Two-char escape code -> the canonical character(s) it decodes to.  `_U` is
# absent deliberately: it is the variable-length escape and is decoded by its
# own branch in :func:`unmangle_type_name`.
_UNMANGLE_CODES = {"_": "_", "L": "<", "R": ">", "C": ", ", "S": " "}


def collect_nested_generic_decls(
    decl: ast.FnDecl,
    out: dict[str, ast.FnDecl],
) -> None:
    """Collect ``forall<T>`` where-helpers under an all-NON-generic ancestor
    chain into *out* (#990).

    A generic helper nested in a non-generic function's ``where`` block is a
    monomorphization base exactly like a top-level generic: its concrete call
    sites need clones emitted (codegen Pass 1.5) and verified per
    instantiation (the #732 loop).  This is the SHARED collector both sides
    build their base set with, so they collect the identical set by
    construction — the verifier⊇codegen differential
    (``tests/test_monomorphize_differential.py``) pins the lockstep.

    Stops at the first generic node: a generic helper's own subtree is NOT
    descended (each clone carries it and codegen hoists it per-instantiation,
    #904 — collecting it here would double-emit the NON-generic descendants),
    and callers only pass non-generic roots.  Note the hoisting path only
    substitutes the generic ANCESTOR's type variables — a descendant with its
    own ``forall`` is hoisted as a still-generic template and never
    instantiated, so that shape still dangles at compile (#1002); this
    collector deliberately does not paper over it.

    Callers pass a program that has been through
    :func:`qualify_nested_generic_decls` (#1014), so every collected helper
    name is parent-qualified (``a$where$g``) and globally unique by
    construction — two same-named helpers under different parents collect as
    two distinct bases.  ``setdefault`` is retained as a no-op backstop.
    """
    for wfn in decl.where_fns or ():
        if wfn.forall_vars:
            out.setdefault(wfn.name, wfn)
        else:
            collect_nested_generic_decls(wfn, out)


def rewrite_fn_call_names(node: object, rename: dict[str, str]) -> object:
    """Return *node* with every ``FnCall`` whose name is in *rename* redirected
    to the mapped name, rebuilding only changed spines (spans preserved).

    The standalone twin of codegen's ``_rewrite_call_names`` — shared here so
    the #1014 qualification transform below can run identically on the codegen
    program and the verifier's discovery copy.
    """
    if isinstance(node, ast.Node):
        changes: dict[str, Any] = {}
        for f in fields(node):
            if f.name == "span":
                continue
            val = getattr(node, f.name)
            new_val = rewrite_fn_call_names(val, rename)
            if new_val is not val:
                changes[f.name] = new_val
        if isinstance(node, ast.FnCall) and node.name in rename:
            changes["name"] = rename[node.name]
        if changes:
            return replace(node, **changes)
        return node
    if isinstance(node, tuple):
        new_items = tuple(rewrite_fn_call_names(v, rename) for v in node)
        if any(n is not o for n, o in zip(new_items, node)):
            return new_items
        return node
    return node


@dataclass(frozen=True)
class NamespaceFnNames:
    """Which bare function names each namespace can NAME (#1299/#1281).

    ``by_namespace`` maps a module path — ``None`` for the entry program — to
    the bare SOURCE function names a body compiled in that namespace may
    resolve a bare call to: its own top-level declarations, whatever their
    visibility, plus the PUBLIC declarations its OWN import list admits.
    That is the checker's view of every module, and imports are read per
    namespace and never inherited, so a module reached only transitively
    from the entry program contributes nothing to the entry's set (spec
    §8.6.4) while still holding everything its own imports allow.

    ``ambiguous_sources`` maps each namespace to the bare names it could
    resolve to more than one dependency's declaration, with no declaration of
    its own to settle it, each paired with its supplying module paths in
    IMPORT order.  Spec §8.5 refuses that name in the namespace that holds
    the clash (#1304), so the checker reads its own namespace's entry to
    report at the offending import and to keep the name out of the type
    environment.

    One derivation because there are three consumers and they must not
    disagree: codegen narrows its per-declaration ownership table with it
    (``_scoped_fn_names``), the CHECKER refuses its own namespace's clashes
    (#1304), and the verifier narrows discovery with it.  Two walks over the
    same imports could differ about a filter or a visibility, and the two
    sides of the #732 differential would then discover different clones.
    """

    by_namespace: Mapping[tuple[str, ...] | None, frozenset[str]]
    ambiguous_sources: Mapping[
        tuple[str, ...] | None,
        Mapping[str, tuple[tuple[str, ...], ...]],
    ] = field(default_factory=dict)

    def visible(self, path: tuple[str, ...] | None) -> frozenset[str]:
        """The names *path*'s namespace can NAME; empty for an unknown path."""
        return self.by_namespace.get(path, frozenset())

    def ambiguous_in(
        self, path: tuple[str, ...] | None,
    ) -> Mapping[str, tuple[tuple[str, ...], ...]]:
        """*path*'s OWN clashing bare names, each to its suppliers (#1304).

        Import order, so a diagnostic can name the import that introduced the
        clash rather than whichever module a set happened to yield first —
        the same nondeterminism this refusal exists to remove.
        """
        return self.ambiguous_sources.get(path, {})


def namespace_fn_names(
    entry: ast.Program,
    modules: Iterable[tuple[tuple[str, ...], ast.Program]],
    prelude: Iterable[str] = (),
) -> NamespaceFnNames:
    """Build the per-namespace visibility tables (see :class:`NamespaceFnNames`).

    Reads each program's declarations as written.  The Pass-0 transforms (the
    #991 hoist, the #1014 qualification) only ADD ``$``-qualified top-level
    declarations, and ``$`` cannot occur in a Vera identifier
    (``LOWER_IDENT``), so no bare source name enters or leaves either set —
    which is what lets codegen call this on its post-transform programs and
    the verifier on its pre-transform ones and still get the same answer.

    *prelude* is the injected combinators' names.  They belong to EVERY
    namespace — a module's body may call ``option_map`` exactly as the entry
    program may — and they are supplied separately rather than read off the
    entry program because the two consumers inject them at different passes:
    the verifier's discovery copy is post-``inject_prelude`` while codegen's
    tables are built at Pass 0.5, before the prelude is registered.  Passing
    them makes the result independent of WHEN it is called, which is the
    property the two sides need and the one
    ``test_discovery_scopes_agree_between_the_two_sides`` checks.  They also
    join the "declared here" set for the ambiguity test: a name the prelude
    or the built-in registry already owns is never ambiguous however many
    dependencies export it, because the importer's injection is a
    ``setdefault`` and the incumbent wins.  No dependency may declare a
    prelude function's name in any case (E151, #1469), so the argument
    changes the ambiguity half only over a program the checker refuses.
    """
    public_fns: dict[tuple[str, ...], frozenset[str]] = {}
    module_list = list(modules)
    prelude_names = frozenset(prelude)
    for path, prog in module_list:
        public_fns[path] = frozenset(
            tld.decl.name for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
            and (tld.visibility or "private") == "public"
        )

    def visible(
        prog: ast.Program,
    ) -> tuple[frozenset[str], dict[str, tuple[tuple[str, ...], ...]]]:
        own = {
            tld.decl.name for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
        } | prelude_names
        names = set(own)
        # Which dependency each importable name came from, in IMPORT order.  A
        # name this namespace declares ITSELF is never ambiguous however many
        # dependencies also export it — the local declaration owns every bare
        # call here (spec §8.5.2).
        #
        # ``sorted`` over the exports, not because this loop's order changes
        # the ANSWER — each name's supplier list follows the enclosing import
        # loop either way — but because a set of strings iterates in an order
        # that varies with the interpreter's hash seed, and #1304 is a defect
        # that reached the user's diagnostics through exactly that.  Nothing
        # downstream of a namespace table should be able to notice a run.
        sources: dict[str, list[tuple[str, ...]]] = {}
        for imp in prog.imports:
            dep = tuple(imp.path)
            exported = public_fns.get(dep)
            if exported is None:
                continue
            for name in sorted(exported):
                if imp.names is None or name in imp.names:
                    names.add(name)
                    deps = sources.setdefault(name, [])
                    if dep not in deps:
                        deps.append(dep)
        clashes = {
            name: tuple(deps)
            for name, deps in sorted(sources.items())
            if len(deps) > 1 and name not in own
        }
        return frozenset(names), clashes

    by_namespace: dict[tuple[str, ...] | None, frozenset[str]] = {}
    ambiguous_sources: dict[
        tuple[str, ...] | None, Mapping[str, tuple[tuple[str, ...], ...]],
    ] = {}
    for key, prog in [(None, entry), *module_list]:
        by_namespace[key], ambiguous_sources[key] = visible(prog)
    return NamespaceFnNames(by_namespace, ambiguous_sources)


@dataclass(frozen=True)
class NamespaceAdtNames:
    """Which bare TYPE and CONSTRUCTOR names two imports both supply (#1304).

    The data-side twin of :class:`NamespaceFnNames`'s ambiguity half, and it
    has to be a second table rather than two more fields on that one because
    the three namespaces are filtered differently: a selective import names
    FUNCTIONS and TYPES directly, while a constructor is admitted by its
    PARENT type's name (spec §8.5.4), so ``import m(Shape)`` supplies ``Sq``
    without ever mentioning it.

    Both maps are per namespace — ``None`` for the entry program — from the
    clashing bare name to the module paths supplying it, in IMPORT order.
    The two are tracked independently because they come apart: two modules
    exporting differently-named ADTs that happen to share a constructor name
    clash on the constructor alone (E157 without E156).

    Only the CHECKER reads this.  Code generation asks no such question:
    every module type and constructor carries its link name in the linked
    program (#1694), so two declarations never contend there.
    """

    ambiguous_types: Mapping[
        tuple[str, ...] | None, Mapping[str, tuple[tuple[str, ...], ...]],
    ]
    ambiguous_ctors: Mapping[
        tuple[str, ...] | None, Mapping[str, tuple[tuple[str, ...], ...]],
    ]

    def types_in(
        self, path: tuple[str, ...] | None,
    ) -> Mapping[str, tuple[tuple[str, ...], ...]]:
        """*path*'s clashing bare TYPE names, each to its suppliers."""
        return self.ambiguous_types.get(path, {})

    def ctors_in(
        self, path: tuple[str, ...] | None,
    ) -> Mapping[str, tuple[tuple[str, ...], ...]]:
        """*path*'s clashing bare CONSTRUCTOR names, each to its suppliers."""
        return self.ambiguous_ctors.get(path, {})


def namespace_adt_names(
    entry: ast.Program,
    modules: Iterable[tuple[tuple[str, ...], ast.Program]],
    owned_types: Iterable[str] = (),
    owned_ctors: Iterable[str] = (),
) -> NamespaceAdtNames:
    """Build the per-namespace data-side clash tables (#1304).

    *owned_types* / *owned_ctors* are the names something OTHER than this
    program's declarations already owns in every namespace — the built-in and
    prelude ADTs (``Option``, ``Result``, ``Ordering``, ``UrlParts``) and
    their constructors.  They join the "declared here" set rather than the
    supplied one, so a namespace whose two imports both export a ``data
    Option`` is NOT reported here: the built-in registry occupies that bare
    name and the imports never win it, exactly as a local declaration would
    settle the clash (spec §8.5.2).  The checker passes its own built-in
    snapshot, so this table cannot disagree with the environment the
    injection loop actually builds — that loop is a ``setdefault`` over a
    ``TypeEnv`` the built-ins already populated.
    """
    public_adts: dict[tuple[str, ...], dict[str, frozenset[str]]] = {}
    module_list = list(modules)
    base_types = frozenset(owned_types)
    base_ctors = frozenset(owned_ctors)
    for path, prog in module_list:
        public_adts[path] = {
            tld.decl.name: frozenset(
                ctor.name for ctor in tld.decl.constructors
            )
            for tld in prog.declarations
            if isinstance(tld.decl, ast.DataDecl)
            and (tld.visibility or "private") == "public"
        }

    def clashes(
        prog: ast.Program,
    ) -> tuple[
        dict[str, tuple[tuple[str, ...], ...]],
        dict[str, tuple[tuple[str, ...], ...]],
    ]:
        own_types = {
            tld.decl.name for tld in prog.declarations
            if isinstance(tld.decl, ast.DataDecl)
        } | base_types
        own_ctors = {
            ctor.name for tld in prog.declarations
            if isinstance(tld.decl, ast.DataDecl)
            for ctor in tld.decl.constructors
        } | base_ctors
        type_sources: dict[str, list[tuple[str, ...]]] = {}
        ctor_sources: dict[str, list[tuple[str, ...]]] = {}
        for imp in prog.imports:
            dep = tuple(imp.path)
            exported = public_adts.get(dep)
            if exported is None:
                continue
            # ``sorted`` for the same reason as the function twin: a set of
            # strings iterates in hash-seed order, and #1304 is a defect that
            # reached the user's diagnostics through exactly that.
            for adt_name in sorted(exported):
                if imp.names is not None and adt_name not in imp.names:
                    continue
                for bucket, names in (
                    (type_sources, (adt_name,)),
                    (ctor_sources, sorted(exported[adt_name])),
                ):
                    for name in names:
                        deps = bucket.setdefault(name, [])
                        if dep not in deps:
                            deps.append(dep)
        return (
            {
                name: tuple(deps)
                for name, deps in sorted(type_sources.items())
                if len(deps) > 1 and name not in own_types
            },
            {
                name: tuple(deps)
                for name, deps in sorted(ctor_sources.items())
                if len(deps) > 1 and name not in own_ctors
            },
        )

    types: dict[
        tuple[str, ...] | None, Mapping[str, tuple[tuple[str, ...], ...]],
    ] = {}
    ctors: dict[
        tuple[str, ...] | None, Mapping[str, tuple[tuple[str, ...], ...]],
    ] = {}
    for key, prog in [(None, entry), *module_list]:
        types[key], ctors[key] = clashes(prog)
    return NamespaceAdtNames(types, ctors)


def where_helper_name(name: str) -> str:
    """A ``where`` helper's own name: *name*, or its last ``$where$``
    segment when the link step (:func:`vera.binding.link`) has already
    named it ``<parent>$where$<name>``.  A transform that names a helper
    under its parent's prefix builds ``<prefix>$where$`` + this, so on a
    linked program it reproduces the link name rather than nesting it."""
    return name.rpartition("$where$")[2]


def _qualify_generic_subtree_calls(
    fn: ast.FnDecl, rename: dict[str, str],
) -> ast.FnDecl:
    """Redirect calls to OUTER qualified generic helpers inside a retained
    generic subtree, honouring the subtree's own shadowing (#1014).

    A generic helper's subtree is per-clone territory (#904): nothing inside
    it is renamed here, and a name the subtree re-declares at any level drops
    the outer entry for that level and below (the per-clone hoist owns it) —
    the same rule as the non-generic hoist's
    ``_rewrite_generic_subtree_shadowed``.
    """
    level_names = {wfn.name for wfn in fn.where_fns or ()}
    visible = {k: v for k, v in rename.items() if k not in level_names}
    body_only = replace(fn, where_fns=None)
    rewritten = rewrite_fn_call_names(body_only, visible)
    assert isinstance(rewritten, ast.FnDecl)  # noqa: S101
    new_where = tuple(
        _qualify_generic_subtree_calls(wfn, visible)
        for wfn in fn.where_fns or ()
    )
    return replace(rewritten, where_fns=new_where or None)


def _qualify_nested_under(
    fn: ast.FnDecl, prefix: str, scope: dict[str, str],
) -> ast.FnDecl:
    """Qualify *fn*'s generic where-helpers under *prefix*, recursively.

    *scope* maps every lexically-enclosing generic helper's bare name to its
    qualified name; this level's declared names (generic or not) shadow outer
    entries, and this level's generic helpers add their own qualified names —
    so a bare call anywhere in the subtree resolves to the NEAREST same-named
    helper, exactly the lexical rule of spec §5 and the non-generic hoist.
    """
    where_fns = fn.where_fns or ()
    declared = {wfn.name for wfn in where_fns}
    generic_renames = {
        wfn.name: f"{prefix}$where${where_helper_name(wfn.name)}"
        for wfn in where_fns
        if wfn.forall_vars
    }
    combined = {k: v for k, v in scope.items() if k not in declared}
    combined.update(generic_renames)
    new_where: list[ast.FnDecl] = []
    for wfn in where_fns:
        if wfn.forall_vars:
            # Rename the base decl; its subtree is rewritten shadow-aware but
            # structurally untouched (per-clone hoisting owns it, #904).
            rewritten = _qualify_generic_subtree_calls(wfn, combined)
            new_where.append(
                replace(rewritten, name=generic_renames[wfn.name])
            )
        else:
            # Descend a non-generic helper, extending the qualification
            # chain — a generic grandchild under it becomes
            # ``a$where$leaf$where$g``, byte-identical to what the codegen
            # side produces after the #991 hoist made ``a$where$leaf`` a
            # top-level parent.
            new_where.append(
                _qualify_nested_under(
                    wfn, f"{prefix}$where${where_helper_name(wfn.name)}",
                    combined,
                )
            )
    body_only = replace(fn, where_fns=None)
    body_rewritten = rewrite_fn_call_names(body_only, combined)
    assert isinstance(body_rewritten, ast.FnDecl)  # noqa: S101
    return replace(body_rewritten, where_fns=tuple(new_where) or None)


def qualify_nested_generic_decls(
    program: ast.Program, name_prefix: str = "",
) -> ast.Program:
    """Give every ``forall`` where-helper under a NON-generic ancestor chain
    a parent-qualified name (``a$where$g``) and redirect each
    lexically-visible bare call to it (#1014).

    Pre-#1014 the nested-generic base set was keyed by BARE name, flat and
    first-seen-wins: two same-named ``forall`` helpers under different parents
    both resolved to the first parent's declaration, so the second parent's
    call silently ran the first parent's body (check-green, wrong value).
    Qualification makes every base name unique by construction — discovery,
    clone naming (``a$where$g$Int``), call rewriting, and the
    codegen<->verifier differential all operate on the qualified names with
    no special-casing.  ``$`` cannot appear in a source identifier and
    ``where`` is reserved, so qualified names collide with nothing
    user-writable; the scheme matches the #991 non-generic hoist and the #904
    per-clone hoist conventions exactly.

    *name_prefix* namespaces the chain root (``{name_prefix}{decl.name}``,
    #1029): the main program passes ``""`` (bare ``compute$where$gid``), while
    codegen's ``_register_modules`` and the verifier's ``_collect_instantiations``
    pass ``"mod$" + "$".join(mod.path) + "$"`` for an IMPORTED module — byte-for-
    byte the prefix of a module declaration's link name
    (:attr:`vera.binding.DeclId.link_name`).
    Without it, two imported modules' same-named nested generics
    (``ma::compute$where$gid`` and ``mb::compute$where$gid``) collapse to one
    key first-seen-wins, leaving a LYING namesake unverified (a false Tier-1).

    Applied by BOTH sides in lockstep: codegen transforms its program at Pass 0
    (BEFORE the #991 hoist — a non-generic helper that calls a generic sibling
    must be qualified while still lexically inside the shared ``where`` block,
    else the hoist lifts it out of parent scope and its bare call dangles; see
    the ordering comment in ``codegen/core.py``), and the verifier transforms its
    prelude-free discovery COPY (``_collect_instantiations``) while keeping the
    original AST for contract verification — its instance lookup joins the lexical
    ``enclosing`` chain to reconstruct the same key.  GENERIC top-level
    declarations are skipped whole: their subtrees are per-clone territory
    (#904/#1002).
    """
    import dataclasses

    new_tlds: list[ast.TopLevelDecl] = []
    for tld in program.declarations:
        decl = tld.decl
        if (isinstance(decl, ast.FnDecl)
                and decl.where_fns
                and not decl.forall_vars):
            new_tlds.append(
                dataclasses.replace(
                    tld,
                    decl=_qualify_nested_under(
                        decl, f"{name_prefix}{decl.name}", {},
                    ),
                )
            )
        else:
            new_tlds.append(tld)
    return dataclasses.replace(program, declarations=tuple(new_tlds))


def unmangle_type_name(mangled: str) -> str:
    """Inverse of :func:`mangle_type_name` over canonical type names.

    :func:`mangle_type_name` is a prefix code — the output is a concatenation
    of code units, each either a single ``[A-Za-z0-9]`` character (mapping to
    itself) or a unit starting with ``_``: one of the two-character codes
    (``__``/``_L``/``_R``/``_C``/``_S``), or the variable-length ``_U<hex>_``
    (#1219).  A left-to-right scan therefore decodes uniquely: at a ``_`` the
    next character selects the unit, and for ``_U`` the run of hex digits
    ends at the ``_`` that no hex digit can be.  Round-trips every canonical
    type name (``unmangle_type_name(mangle_type_name(t)) == t``) — the LEFT
    INVERSE that makes the mangler injective, and what lets the verifier's
    Array-element reverse lookup (``_get_element_sort_for_array`` in
    ``vera/smt.py``) recover the ``_z3_sorts`` key (``List<Int>``) from a
    mangled Array-element sort name (``List_LInt_R``) after #884 routed ADT
    sort names through the mangler.

    Raises ``ValueError`` on a string that is not valid mangler output (a
    trailing lone ``_``, an unknown ``_X`` code, or an unterminated / empty /
    non-hex ``_U…`` run) — such input is outside the mangler's range and has
    no preimage.
    """
    out: list[str] = []
    i = 0
    n = len(mangled)
    while i < n:
        ch = mangled[i]
        if ch != "_":
            out.append(ch)
            i += 1
            continue
        if i + 1 >= n:
            raise ValueError(f"trailing lone '_' in mangled name: {mangled!r}")
        code = mangled[i + 1]
        if code == _MANGLE_HEX:
            end = mangled.find("_", i + 2)
            digits = mangled[i + 2:end] if end >= 0 else ""
            if end < 0 or not digits or any(
                    d not in "0123456789abcdef" for d in digits):
                raise ValueError(
                    f"malformed '_{_MANGLE_HEX}<hex>_' escape in mangled "
                    f"name: {mangled!r}"
                )
            out.append(chr(int(digits, 16)))
            i = end + 1
            continue
        decoded = _UNMANGLE_CODES.get(code)
        if decoded is None:
            raise ValueError(
                f"unknown escape code '_{code}' in mangled name: {mangled!r}"
            )
        out.append(decoded)
        i += 2
    return "".join(out)


# Sentinel marking a genuinely-FREE (un-inferred) type-parameter slot in a
# partially-recovered sparse-multi-parameter ADT name (`Res<?, Int>`, #898).
# `?` cannot occur in a real Vera type name, so it never collides with a
# concrete type; such a name reaches only the ability gate (the instance is
# always rejected), never an emitted clone, and lets the gate tell an
# under-determined-but-would-derive type (E619, annotate the free param) from
# one whose known component is already non-Eq (E613, annotation cannot help).
_FREE_TYPE_PARAM = "?"


def checker_clone_type_name(
    table: Mapping[int, object] | None, expr: ast.Expr,
) -> str | None:
    """The clone-name the CHECKER's recorded type for *expr* denotes (#1327).

    The two type namers — discovery's ``_infer_vera_type_name`` and the WASM
    call-rewrite's ``_infer_vera_type`` — are hand-maintained walkers over the
    expression grammar, and every member of the #1327 family is one of them
    missing an arm the other has: discovery had none for ``IndexExpr``
    (#1327), none for ``ModuleCall`` (#1366), none for ``ResultRef`` (#1369).
    A missing arm answers ``None``, the type variable falls to the phantom
    default, and the two consultors name different clones on check-green
    source.

    The checker has already typed every expression it synthesised, so this is
    the answer neither walker has to re-derive.  Both consult it through THIS
    function, in the same position — after their own walk, never before it —
    so a shape one of them cannot name is named identically for both, and the
    class of bug that is "one walker is missing an arm" cannot recur.

    Why after rather than before: the walkers' answers are a deliberate
    clone-NAMING vocabulary, not a type judgement, and it differs from the
    checker's semantic type in ways that are load-bearing.  Measured over the
    corpus, 1,976 namer calls across 73 shapes would change their answer if
    the checker won: an integer literal names ``Int`` where the checker says
    ``Nat`` (the WAT-collapsed vocabulary the #732 differential is stated in),
    a ``ConstructorCall`` names the bare ``List`` where the checker says
    ``List<List<Nat>>`` (#772 — an unconstrained generic's clone is a uniform
    pointer, so one ``id$Box`` serves every instantiation), and a user
    function's declared ``-> @Age`` names ``Age`` where the checker resolves
    the alias to ``Int`` (#899 — the raw declared name is what discovery keys
    the clone on).  Reversing the precedence would re-granulate
    monomorphization across the whole corpus, which is a language decision and
    not this repair.  Consulted second, the checker changes no name that
    exists and supplies every name that does not.

    Returns ``None`` when there is no table, no entry for this node, or a type
    with no clone-name spelling (a still-generic ``TypeVar``, a function type,
    the checker's unknown) — in which case the caller is exactly as informed as
    it was before, and [E622] reports the hole rather than guessing at it.
    """
    if table is None:
        return None
    key = expr.node_id
    if key is None:
        return None
    ty = table.get(key)
    if ty is None:
        return None
    return _type_clone_name(ty)


def _type_clone_name(ty: object) -> str | None:
    """Render one checker ``Type`` into the clone-name vocabulary.

    Deliberately narrow: primitives and ADTs by name (with type arguments,
    which is how a slot reference's declared name already spells them), a
    refinement by its base (every namer arm unwraps refinements), and nothing
    at all for a type variable — a still-generic type must never name a
    concrete clone — or for a function type or the unknown.
    """
    from vera.types import AdtType, PrimitiveType, RefinedType

    if isinstance(ty, PrimitiveType):
        if ty.name == "Never":
            # A diverging expression has no value, so it can never be the
            # value a generic is instantiated at.  Answering `Never` here
            # would defeat the #1286 join, whose whole premise is that a
            # branch naming NOTHING must not decide the answer: the `then` of
            # `idg(if c then { throw(x) } else { 42 })` walks to `None` today
            # and the `else` supplies `Int`, and a checker answer of `Never`
            # at the recursive level would name `idg$Never` — a clone whose
            # parameter has no WASM representation, dropped at [E604], taking
            # `main` with it.  Measured: the whole #1286 battery and
            # `ch02_generic_arg_branch_join` fail exactly that way without
            # this line.
            return None
        return ty.name
    if isinstance(ty, AdtType):
        if not ty.type_args:
            return ty.name
        parts = [_type_clone_name(a) for a in ty.type_args]
        if any(p is None for p in parts):
            # A partially-generic instantiation has no honest concrete
            # spelling.  Drop EVERY argument rather than render the ones that
            # resolved: `Option<Option>` for `Option<Option<T>>` is a name no
            # clone emission produces, where the bare `Option` is exactly what
            # both walkers already answer for an unconstrained parameterised
            # argument (#772).
            return ty.name
        return f"{ty.name}<{', '.join(p for p in parts if p is not None)}>"
    if isinstance(ty, RefinedType):
        return _type_clone_name(ty.base)
    return None


def checker_arg_type_info(
    table: Mapping[int, object] | None, expr: ast.Expr,
) -> tuple[str, tuple[str | None, ...]] | None:
    """``(base name, per-type-argument names)`` from the CHECKER's type.

    The structural counterpart of :func:`checker_clone_type_name`, for the
    parameterised branch of unification: matching ``Array<T>`` against an
    argument needs the argument's own base and type arguments, and the
    walkers' ``_get_arg_type_info`` has the same missing arms their namers had
    — no arm for an indexed argument, none for a nested module call — so the
    variable stays unbound and the phantom default names the clone (#1395).

    Consulted ONLY for variables the walkers left unbound, and only after
    every parameter has bound what it can.  That ordering is the whole
    discipline: the checker's answer is a SEMANTIC type and the walkers' is a
    clone-NAMING vocabulary, and where they differ the walkers' is the one the
    emitted symbol must use.  `option_unwrap_or(nothing(()), 11)` measures
    `Option<Nat>` here where the walkers spell the same instantiation `Int`;
    consulted during the first pass that answer arrives from the FIRST
    parameter and displaces the correct binding the second parameter's literal
    supplies, moving six corpus programs' WAT.  Consulted last, into a hole,
    it can displace nothing.
    """
    if table is None:
        return None
    key = expr.node_id
    if key is None:
        return None
    ty = table.get(key)
    if ty is None:
        return None
    from vera.types import AdtType, RefinedType

    while isinstance(ty, RefinedType):
        ty = ty.base
    if not isinstance(ty, AdtType):
        return None
    return ty.name, tuple(_type_clone_name(a) for a in ty.type_args)


#: The simple names the rewrite chain has always used where they are not the
#: record's: `string_length` returns `Nat` and is named by the WAT-collapsed
#: `Int` here.  Clone-NAME agreement between the two consultors is the
#: invariant, not name precision, so changing a value is a clone-granularity
#: decision, not a completion (#769).
_HISTORICAL_RETURN_NAMES: dict[str, str] = {"string_length": "Int"}


def _builtin_return_tables() -> tuple[
    dict[str, str], dict[str, tuple[str, tuple[str, ...]]]
]:
    """The two tables, from the registry's records."""
    from vera.builtins import BUILTINS
    from vera.types import (
        AdtType, FunctionType, PrimitiveType, RefinedType, Type, TypeVar, pretty_type,
    )

    def concrete(ty: Type) -> bool:
        if isinstance(ty, TypeVar):
            return False
        if isinstance(ty, AdtType):
            return all(concrete(a) for a in ty.type_args)
        if isinstance(ty, RefinedType):
            return concrete(ty.base)
        if isinstance(ty, FunctionType):
            return all(concrete(p) for p in ty.params) and concrete(ty.return_type)
        return True

    simple: dict[str, str] = {}
    parameterized: dict[str, tuple[str, tuple[str, ...]]] = {}
    for name, spec in BUILTINS.items():
        ret = spec.signature.ret
        if isinstance(ret, (PrimitiveType, AdtType)):
            simple[name] = _HISTORICAL_RETURN_NAMES.get(name, ret.name)
        if isinstance(ret, AdtType) and ret.type_args and concrete(ret):
            parameterized[name] = (
                ret.name, tuple(pretty_type(a) for a in ret.type_args))
    return simple, parameterized


_BUILTIN_VERA_RETURN_TYPES, _BUILTIN_PARAMETERIZED_RETURNS = _builtin_return_tables()


class Monomorphizer:
    """The clone builder: a generic declaration's copy at one instantiation
    (:meth:`monomorphize_fn`), the type-name parse and render its
    substitution spells, and the injective clone mangler.

    The typed program (:mod:`vera.typed`) decides the instances, from the
    checker's instantiations, and builds each clone with this once.
    *alias_env* is the naming environment a clone's De Bruijn recount
    renders binder names in when the caller hands none (#1208).
    """

    def __init__(self, alias_env: AliasEnv = EMPTY_ALIAS_ENV) -> None:
        self.alias_env = alias_env

    @staticmethod
    def _unify_type_arg_pair(
        param_ta: ast.TypeExpr,
        arg_name: str,
        forall_vars: tuple[str, ...],
        mapping: dict[str, str],
    ) -> None:
        """Recursively unify ONE parameter type-argument against a concrete
        type-argument NAME, binding forall vars at any nesting depth (#769
        gap 2): ``Option<T>`` vs ``"Option<Int>"`` binds ``T = "Int"``, and so
        does ``Array<Option<T>>`` vs ``"Array<Option<Int>>"`` — the pre-#769
        zip bound only when the IMMEDIATE type argument was the variable
        itself, so any deeper var fell to the ``Bool`` phantom default.

        First binding wins (``mapping`` is never overwritten), matching
        ``_unify_param_arg``'s outer behavior.  Static and self-contained so
        the WASM call-rewrite twin (``_unify_param_arg_wasm``,
        vera/wasm/calls.py) calls THIS implementation — the two clone-name
        consultors bind identically by construction.
        """
        if isinstance(param_ta, ast.RefinementType):
            param_ta = param_ta.base_type
        if not isinstance(param_ta, ast.NamedType):
            return
        if param_ta.name in forall_vars:
            if param_ta.name not in mapping:
                mapping[param_ta.name] = arg_name
            return
        if not param_ta.type_args:
            return
        parsed = Monomorphizer._parse_type_name(arg_name)
        if parsed.name != param_ta.name or not parsed.type_args:
            return
        for p_sub, a_sub in zip(param_ta.type_args, parsed.type_args):
            if isinstance(a_sub, ast.NamedType):
                Monomorphizer._unify_type_arg_pair(
                    p_sub, Monomorphizer._format_type_name(a_sub),
                    forall_vars, mapping,
                )

    @staticmethod
    def _parse_type_name(name: str) -> ast.NamedType:
        """Parse a full type name string into a NamedType AST node.

        E.g. "Map<String, Int>" → NamedType("Map", (NamedType("String"),
        NamedType("Int"))).  Handles nested types like
        "Map<String, Array<Int>>".
        """
        # A refinement's predicate is one atom (#1674).
        masked = naming.mask_refinements(name)
        if "<" not in masked:
            return ast.NamedType(name=name, type_args=None)
        lt = masked.index("<")
        base = name[:lt]
        inner = name[lt + 1:-1]  # strip outer < >
        # Split at top-level commas (respecting nesting)
        args: list[str] = []
        depth = 0
        current: list[str] = []
        for ch, sh in zip(inner, masked[lt + 1:-1]):
            if sh == "<":
                depth += 1
                current.append(ch)
            elif sh == ">":
                depth -= 1
                current.append(ch)
            elif sh == "," and depth == 0:
                args.append("".join(current).strip())
                current = []
            else:
                current.append(ch)
        if current:
            args.append("".join(current).strip())
        type_args = tuple(
            Monomorphizer._parse_type_name(a) for a in args
        )
        return ast.NamedType(name=base, type_args=type_args)

    @staticmethod
    def _format_type_name(te: ast.NamedType) -> str:
        """Format a NamedType as a full type name including type args.

        E.g. NamedType("Map", (NamedType("String"), NamedType("Int")))
        becomes "Map<String, Int>".

        Note: duplicated in InferenceMixin._format_named_type (inference.py).
        Both must remain in sync — the mixin architecture prevents sharing.
        """
        if not te.type_args:
            return te.name
        arg_names = []
        for ta in te.type_args:
            if isinstance(ta, ast.NamedType):
                arg_names.append(Monomorphizer._format_type_name(ta))
            else:
                return te.name
        return f"{te.name}<{', '.join(arg_names)}>"

    @staticmethod
    def _mangle_fn_name(name: str, concrete_types: tuple[str, ...]) -> str:
        """Produce a mangled name for a monomorphized function.

        Example: identity + ("Int",) -> "identity$Int"
        Example: swap + ("Int", "Bool") -> "swap$Int_JBool"
        Example: option_unwrap_or + ("Map<String, Int>",)
                 -> "option_unwrap_or$Map_LString_CInt_R"

        INJECTIVE over (name, type-arg vector), #775.  Each component is
        escaped by :func:`mangle_type_name` (itself injective — see its
        docstring) and the vector is joined with ``_J``.

        The separator is safe because of a property of the escape, not
        because of a list of its codes: **no mangler unit begins with**
        ``J``.  A unit is either a single ``[A-Za-z0-9]`` character or a
        ``_``-led escape, and ``J`` is not one of the escape letters — so
        during the left-to-right decode, a ``_J`` at a unit boundary can
        only be the separator.  A literal ``_J`` inside a type name is not
        that: its ``_`` escapes to ``__``, whose two characters are
        consumed as one unit first, leaving the ``J`` as an ordinary
        character mid-unit-stream.  Splitting on boundary-``_J`` therefore
        recovers the exact component vector, and each component un-escapes
        uniquely — no two distinct instantiation vectors share a symbol.

        Stating it as the property rather than as an enumeration is what
        keeps it true as the escape grows: the #1219 widening added the
        variable-length ``_U<hex>_`` unit, whose TERMINATOR is a ``_`` that
        can sit immediately before a literal ``J``, and an argument phrased
        as "the codes are ``__``/``_L``/``_R``/``_C``/``_S``" would have
        silently stopped covering the alphabet it describes.  It is still
        sound: that ``_`` closes its unit, so the ``J`` after it begins a
        new one as an ordinary character, never a ``_J`` boundary.

        ``name`` never contains ``$`` (Vera identifiers can't lex it), so
        the prefix splits off unambiguously at the first ``$``.

        Collision classes this kills (both produced duplicate WAT ``func``
        identifiers pre-fix): parameterized built-in vs flat user ADT
        (``g<Map<String, Int>>`` / ``g<Map_String_Int>`` both mangled to
        ``g$Map_String_Int``) and multi-parameter joins across the ``_``
        boundary (``g<A_B, C>`` / ``g<A, B_C>`` both ``g$A_B_C``).

        Determinism: a pure string map of the (already canonical,
        deterministically ordered) instantiation vector — stable across
        runs and platforms.  DESIGN.md principle 1 (checkability: the
        injectivity argument is mechanical, with no reliance on
        bracket-balance properties of the inputs) and principle 3 (one
        canonical form: one shared escape for every type name embedded in
        a WAT symbol) drove the encoding choice.
        """
        suffix = "_J".join(mangle_type_name(ct) for ct in concrete_types)
        return f"{name}${suffix}"

    def monomorphize_fn(
        self,
        decl: ast.FnDecl,
        concrete_types: tuple[str, ...],
        alias_env: AliasEnv | None = None,
    ) -> ast.FnDecl:
        """Create a monomorphized copy of a generic function.

        Public: the shared substitution contract called by both codegen and the
        verifier (#732).  Needs no ``ctx`` beyond ``decl`` + ``concrete_types``,
        so a discovery-time ``Monomorphizer`` can be reused at verify time.

        Replaces type variables with concrete types throughout the AST
        and mangles the function name.

        When distinct type variables map to the same concrete type
        (e.g. A→Int, B→Int), De Bruijn indices in slot references
        must be adjusted because formerly separate namespaces merge.

        *alias_env* is the naming environment the reindex renders binder
        names against (#1208).  It must be the env of the module that
        DECLARED *decl*, not the driver's own: aliases are module-scoped
        (spec §8.4.1), so a clone of an IMPORTED generic whose parameters
        name a module-local alias merges differently in its own namespace
        than in the importer's — and the consumers rebuild the clone's scope
        under the defining module's scope, so a recount done against the
        importer's would be a recount against a scope nobody has.  Defaults
        to ``ctx.alias_env``, which is right whenever the caller has only
        one namespace in play.  ``_compute_scoped_reindex`` narrows it by the
        ``forall`` variables in scope on each side of the recount — all of
        them before substitution, the SURVIVING ones after — so a type
        parameter shadowing a same-named alias renders as the checker
        rendered it, and as the consumers re-render it on the clone.
        """
        assert decl.forall_vars is not None  # noqa: S101
        env = self.alias_env if alias_env is None else alias_env
        mapping = dict(zip(decl.forall_vars, concrete_types))
        mangled = self._mangle_fn_name(decl.name, concrete_types)

        # #1433: rename every `where` helper binder the substitution would
        # capture first, so the reindex walk and the substitution below both
        # read the renamed declaration and agree node for node.
        decl = self._rename_capturing_binders(decl, mapping)

        # Scope-aware De Bruijn reindexing (#769 gap 3): resolve every
        # SlotRef against the full binding scope at its reference site and
        # recompute its index in the collapsed (post-substitution) namespace.
        reindex = self._compute_scoped_reindex(decl, mapping, env)

        # Substitute type variables in the entire FnDecl
        substituted = self._substitute_in_ast(decl, mapping, reindex)
        assert isinstance(substituted, ast.FnDecl)  # noqa: S101

        # Override name and clear forall_vars/constraints
        return replace(
            substituted, name=mangled,
            forall_vars=None, forall_constraints=None,
        )

    def _rename_capturing_binders(
        self, fn: ast.FnDecl, mapping: dict[str, str],
    ) -> ast.FnDecl:
        """*fn* with each ``where`` helper binder that *mapping* would
        capture renamed, at every depth (#1433).

        *mapping* is the substitution in force inside *fn*.  Each helper
        sees it without the type variables the helper rebinds
        (:func:`_unshadowed`), and a binder the remaining replacements spell
        (:func:`_capturing_binders`) is renamed with every use of it — its
        type positions, slot and result references, and ability constraints
        — through the helper and into the nested helpers that do not rebind
        it.  Returns *fn* itself when nothing is renamed.
        """
        helpers = fn.where_fns or ()
        if not helpers or not mapping:
            return fn
        renamed: list[ast.FnDecl] = []
        for helper in helpers:
            active = _unshadowed(mapping, helper.forall_vars)
            fresh = _capturing_binders(active, helper.forall_vars)
            if fresh:
                helper = self._rename_binders(helper, fresh)
            renamed.append(self._rename_capturing_binders(helper, active))
        if all(new is old for new, old in zip(renamed, helpers)):
            return fn
        return replace(fn, where_fns=tuple(renamed))

    def _rename_binders(
        self, helper: ast.FnDecl, fresh: dict[str, str],
    ) -> ast.FnDecl:
        """*helper* with its ``forall`` binders renamed by *fresh*.

        Every use inside the helper names the binder, which shadows any type
        of its name there, so the renaming is the ordinary substitution of
        the old name by the new one; a nested helper rebinding the name
        keeps its own (:func:`_unshadowed`).  A slot reference keeps its
        index: the renamed bindings are exactly the ones it counted.
        """
        body = self._substitute_in_ast(helper, fresh)
        assert isinstance(body, ast.FnDecl)  # noqa: S101
        constraints = helper.forall_constraints
        if constraints:
            constraints = tuple(
                replace(c, type_var=fresh.get(c.type_var, c.type_var))
                for c in constraints
            )
        return replace(
            body,
            forall_vars=tuple(
                fresh.get(b, b) for b in helper.forall_vars or ()),
            forall_constraints=constraints,
        )

    def _substituted_slot_name(
        self, te: ast.TypeExpr, mapping: dict[str, str], env: AliasEnv,
    ) -> str | None:
        """Canonical slot name of ``te`` AFTER type-variable substitution —
        the name this binder carries in the clone.

        #1208: rendered by :func:`vera.naming.slot_name` against the origin
        module's alias environment, the same renderer the consumers rebuild
        the clone's scope with.  A name minted here that they would not mint
        is a De Bruijn recount against a scope neither of them has.
        """
        return naming.slot_name_or_none(
            self._substitute_type_expr(te, mapping), env)

    def _compute_scoped_reindex(
        self,
        decl: ast.FnDecl,
        mapping: dict[str, str],
        env: AliasEnv,
    ) -> dict[int, int]:
        """Scope-aware De Bruijn reindex for monomorphization (#769 gap 3).

        Returns ``{id(slot_ref_node): new_index}`` for every ``SlotRef`` in
        ``decl`` whose index changes when type-variable substitution merges
        formerly-distinct slot namespaces (``A -> Int, B -> Int``, or a
        type-var namespace merging with an already-concrete one — a body
        ``let @Int`` interposes for ``@A.0`` just the same).

        The pre-#769 implementation built a static ``(name, index) -> index``
        map from the PARAMETERS only and applied it body-wide.  That is
        unsound twice over: a ``let`` / match-binder / closure-param of a
        collapsing type interposes an extra binding for every LATER reference
        (one static entry cannot be right both before and after it), and the
        one-level slot-name truncation (``Array<Option<A>>`` ->
        ``"Array<Option>"``) hid genuine collapses entirely.

        This walker instead carries a binding stack of
        ``(old_name, new_name)`` pairs, pushed exactly where the checker
        binds slots — and therefore where the verifier's ``SlotEnv`` and
        codegen's ``WasmSlotEnv`` rebuild them when they consume the clone:

        * function parameters (in declaration order);
        * ``let`` / ``let``-destructuring bindings — pushed AFTER their RHS
          is walked (the RHS sees the pre-binding scope);
        * match-arm pattern binders, scoped to their arm, in left-to-right
          depth-first pattern order;
        * closure (``AnonFn``) parameters, pushed on the SHARED stack —
          closure bodies see enclosing bindings (spec ch. 5);
        * handler-clause operation parameters then handler state (clause
          scope, including the ``with`` state-update expression), and the
          handler state alone for the handled body — mirroring
          ``checker/control.py``;
        * block scopes push/pop, so an arm/branch ``let`` never leaks.

        Contracts (``requires``/``ensures``) resolve against a PARAMS-ONLY
        stack — they are boundary conditions, checked by the checker before
        the body binds anything, and both consumers rebuild exactly that
        scope for them.  ``where``-helpers are independent param-rooted
        scopes (their bodies cannot reference outer slots in any compiling
        program).  Refinement predicates are isolated single-binder scopes:
        the walker never descends into ``TypeExpr`` fields, so their indices
        are untouched (an outer collapse cannot shift a one-binder scope).

        Names come from :mod:`vera.naming` — the ONE renderer both consumers
        resolve the clone's scope against (#1208) — with the BIND side
        (``push``) and the REFERENCE side (``resolve``) rendered by the same
        function over the same environment.  They have to move together: a
        recount that pushes under one rendering and looks up under another
        silently mis-resolves, which is the whole failure mode this walker
        exists to prevent.  A reference that does not resolve against the
        walked scope keeps its index — the consumers surface dangling refs
        (hard E699 in codegen) exactly as they would have pre-substitution.

        TWO environments, because the recount spans a scope change.  The
        PRE-substitution side (the old name a ``push`` records and the key a
        ``resolve`` looks up) is rendered against *scope* — the module env
        NARROWED by the ``forall`` variables in scope over the function being
        walked (:func:`~vera.slots.fn_slot_scope`), which is what the CHECKER
        rendered the generic's own signature and body against: a type
        parameter shadows a same-named module alias for the whole signature
        (``type T = Int;`` + ``forall<T>``), so rendering the pre-substitution
        side against the bare module env collapses ``@Option<T>`` and
        ``@Option<Int>`` into one stack the checker kept apart, and every
        reference into that stack silently resolves onto the wrong parameter
        (#1208 review, probes ``m01``/``m03``/``v01``).

        The POST-substitution side is narrowed by the ``forall`` variables the
        CLONE declares — which is what the consumers rebuild from, so matching
        them is by construction rather than by argument.  For the function
        being cloned that is none of them (``monomorphize_fn`` clears its
        ``forall_vars``), which is why the bare env is right for the top-level
        walk.  It is NOT right one level down: substitution clears only the
        cloned function's own variables, so a ``where`` helper declared
        ``forall<U>`` still carries ``forall_vars=('U',)`` in the clone, and
        both consumers narrow by it when they re-render the helper.  Minting
        the helper's post-substitution names against the bare env instead
        resolves ``U`` through a same-named module alias (``type U = Int;`` →
        ``Option<Int>``) — a recount whose new names are names nobody looks
        up.  Narrowing by the variables that merely SURVIVE the substitution
        (``v not in mapping``) is not the same rule and was the same bug one
        case further out: it dropped a helper variable that shares a name with
        the parent's, and under an identity mapping (``forall<T>``
        instantiated at a module alias spelled ``T``) that variable is still
        written in the clone, so the post side minted ``Option<Int>`` where
        the consumers rebuild ``Option<T>`` (PR #1224 round-3).  Every
        currently-reachable instance of that shape is blocked upstream by
        `#1223 <https://github.com/aallan/vera/issues/1223>`_ — codegen drops
        a generic ``where``-helper under a generic parent before it can be
        run — so the rule is pinned as a differential against the consumers'
        own rebuild rather than end to end.  A ``where`` helper extends BOTH
        narrowings with its own parameters on top of its ancestors' — the same
        accumulation :func:`~vera.slots.fn_scopes` performs, because
        ``_check_fn`` adds to one shared type-parameter map rather than
        replacing it.  One environment per side, used by every rendering on
        that side: ``push`` mints both names, and ``resolve`` reads the
        pre-side key it minted and the post-side name it recorded, so the two
        cannot be scoped differently.
        """
        out: dict[int, int] = {}
        stack: list[tuple[str | None, str | None]] = []

        scope = fn_slot_scope(env, decl.forall_vars)
        # The clone this walk is minting names for declares NO type parameters
        # — `monomorphize_fn` clears them — so the consumers rebuild its scope
        # from the bare env, and so does the post side.
        post_scope = env
        # #1433: the substitution in force at the point being walked.  A
        # `where` helper's own `forall` binders shadow the enclosing
        # function's (spec §5.6.2), so inside the helper the mapping loses
        # them — the same narrowing `_substitute_in_ast` applies to the clone
        # this walk counts for, or the two would mint different names.
        active = mapping

        def push(te: ast.TypeExpr) -> None:
            stack.append((
                naming.slot_name_or_none(te, scope),
                self._substituted_slot_name(te, active, post_scope),
            ))

        def resolve(ref: ast.SlotRef) -> None:
            name = naming.slot_ref_key(ref, scope)
            seen = 0
            for pos in range(len(stack) - 1, -1, -1):
                if stack[pos][0] != name:
                    continue
                if seen == ref.index:
                    binder_new = stack[pos][1]
                    if binder_new is None:
                        return
                    new_idx = sum(
                        1 for later in stack[pos + 1:]
                        if later[1] == binder_new
                    )
                    if new_idx != ref.index:
                        out[id(ref)] = new_idx
                    return
                seen += 1

        def push_pattern(pat: ast.Pattern) -> None:
            if isinstance(pat, ast.BindingPattern):
                push(pat.type_expr)
            elif isinstance(pat, ast.ConstructorPattern):
                for sub in pat.sub_patterns:
                    push_pattern(sub)
            # Wildcard / nullary / literal patterns bind nothing.

        def walk_stmt(stmt: ast.Stmt) -> None:
            if isinstance(stmt, ast.LetStmt):
                walk(stmt.value)
                push(stmt.type_expr)
                return
            if isinstance(stmt, ast.LetDestruct):
                walk(stmt.value)
                for te in stmt.type_bindings:
                    push(te)
                return
            walk(stmt)

        def walk(v: object) -> None:
            if isinstance(v, ast.SlotRef):
                resolve(v)
                return  # type_args carry no slot references
            if isinstance(v, ast.TypeExpr):
                return  # refinement predicates: isolated scopes, untouched
            if isinstance(v, ast.Block):
                mark = len(stack)
                for stmt in v.statements:
                    walk_stmt(stmt)
                walk(v.expr)
                del stack[mark:]
                return
            if isinstance(v, ast.MatchExpr):
                walk(v.scrutinee)
                for arm in v.arms:
                    mark = len(stack)
                    push_pattern(arm.pattern)
                    walk(arm.body)
                    del stack[mark:]
                return
            if isinstance(v, ast.AnonFn):
                mark = len(stack)
                for param_te in v.params:
                    push(param_te)
                walk(v.body)
                del stack[mark:]
                return
            if isinstance(v, ast.HandleExpr):
                if v.state is not None:
                    walk(v.state.init_expr)
                for clause in v.clauses:
                    mark = len(stack)
                    for param_te in clause.params:
                        push(param_te)
                    if v.state is not None:
                        push(v.state.type_expr)
                    walk(clause.body)
                    if clause.state_update is not None:
                        walk(clause.state_update[1])
                    del stack[mark:]
                # The HANDLED body carries NO state slot binding in the
                # consumers: codegen routes handler state through host-side
                # state cells (_translate_handle_state translates the body
                # with the env unchanged; _collect_free_vars likewise), so the
                # walker must not count one — a phantom binding shifts every
                # same-named ref in the body to a dangling or wrong local
                # (adversarial panel, PR #972).  The checker agrees since
                # #973: it binds no body-scope state either, rejecting such
                # refs with E130.  Clause scopes above keep params + state:
                # that is what _collect_free_vars counts (and Exn clause
                # compilation pushes the thrown binder).
                walk(v.body)
                return
            if isinstance(v, ast.Node):
                for fld in fields(v):
                    if fld.name == "span":
                        continue
                    walk(getattr(v, fld.name))
                return
            if isinstance(v, tuple):
                for item in v:
                    walk(item)

        def walk_fn_scope(fn_decl: ast.FnDecl) -> None:
            nonlocal scope, post_scope, active
            del stack[:]
            for param_te in fn_decl.params:
                push(param_te)
            for contract in fn_decl.contracts:
                walk(contract)
            walk(fn_decl.body)
            # ``where`` blocks nest — recurse so every helper at every depth
            # gets its own param-rooted scope, matching the total
            # collect_calls_in_node walk (PR #972 review; a depth-1 walk left
            # nested helpers' collapsed indices stale).
            for nested in fn_decl.where_fns or ():
                saved = (scope, post_scope, active)
                scope = fn_slot_scope(scope, nested.forall_vars)
                # AS DECLARED on both sides.  Substitution clears only the
                # cloned function's own variables, so the helper carries its
                # `forall_vars` unchanged into the clone and the consumers
                # narrow by exactly them.  Narrowing the post side by the
                # SURVIVING ones instead dropped any helper variable that
                # shared a name with the parent's — under an identity mapping
                # (`forall<T>` instantiated at a module alias spelled `T`) the
                # variable is still written in the clone, so the post side
                # minted `Option<Int>` through the alias where the consumers
                # rebuild `Option<T>` (PR #1224 round-3).
                post_scope = fn_slot_scope(post_scope, nested.forall_vars)
                active = _unshadowed(active, nested.forall_vars)
                try:
                    walk_fn_scope(nested)
                finally:
                    scope, post_scope, active = saved

        walk_fn_scope(decl)
        return out

    def _substitute_in_ast(
        self, node: ast.Node, mapping: dict[str, str],
        reindex: dict[int, int] | None = None,
    ) -> ast.Node:
        """Recursively substitute type variable names in an AST subtree.

        Handles NamedType (type expressions) and SlotRef (slot references)
        as special cases; all other nodes are walked generically via
        dataclass fields.

        When reindex is provided, De Bruijn indices on SlotRef nodes are
        adjusted to account for namespace collisions (e.g. A→Int, B→Int
        causing Array<A> and Array<B> to merge into Array<Int>).
        """
        # Special case: NamedType — substitute type variable names
        if isinstance(node, ast.NamedType):
            mapped = mapping.get(node.name)
            if mapped is not None and "<" in mapped:
                # Parameterized type like "Map<String, Int>" — parse into
                # NamedType with type_args, standing where *node* stood
                # (its identity, #1679).
                return replace(self._parse_type_name(mapped),
                               node_id=node.node_id)
            new_name = mapped if mapped is not None else node.name
            new_args: tuple[ast.TypeExpr, ...] | None = node.type_args
            if node.type_args:
                new_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if new_name != node.name or new_args is not node.type_args:
                return replace(node, name=new_name, type_args=new_args)
            return node

        # Special case: SlotRef — substitute type_name and type_args,
        # and adjust the De Bruijn index if namespace collapse occurred
        # (scope-aware, keyed by node identity — see
        # ``_compute_scoped_reindex``).
        if isinstance(node, ast.SlotRef):
            mapped_name = mapping.get(node.type_name)
            if mapped_name is not None and "<" in mapped_name:
                # Parameterized type — parse into base name + type_args
                parsed = self._parse_type_name(mapped_name)
                new_type_name = parsed.name
                new_slot_args = parsed.type_args
            else:
                new_type_name = mapped_name if mapped_name is not None else node.type_name
                new_slot_args = node.type_args
            if node.type_args and new_slot_args is node.type_args:
                new_slot_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )

            # Adjust De Bruijn index if needed
            new_index = node.index
            if reindex:
                new_index = reindex.get(id(node), node.index)

            if (new_type_name != node.type_name
                    or new_slot_args is not node.type_args
                    or new_index != node.index):
                return replace(
                    node, type_name=new_type_name,
                    type_args=new_slot_args,
                    index=new_index,
                )
            return node

        # Special case: ResultRef — substitute type_name and type_args.  Parse a
        # parameterised mapping (T -> "Array<Int>") into base name + type_args,
        # mirroring the SlotRef/NamedType branches, so a generic postcondition's
        # @T.result becomes a canonical @Array<Int>.result rather than a
        # non-canonical type_name="Array<Int>" with no type_args (PR #767 review).
        if isinstance(node, ast.ResultRef):
            mapped_name = mapping.get(node.type_name)
            new_res_args: tuple[ast.TypeExpr, ...] | None
            if mapped_name is not None and "<" in mapped_name:
                parsed = self._parse_type_name(mapped_name)
                new_type_name = parsed.name
                new_res_args = parsed.type_args
            else:
                new_type_name = (
                    mapped_name if mapped_name is not None else node.type_name
                )
                new_res_args = node.type_args
            if node.type_args and new_res_args is node.type_args:
                new_res_args = tuple(
                    self._substitute_type_expr(ta, mapping)
                    for ta in node.type_args
                )
            if (new_type_name != node.type_name
                    or new_res_args is not node.type_args):
                return replace(
                    node, type_name=new_type_name, type_args=new_res_args,
                )
            return node

        # Generic case: recurse into all dataclass fields
        changes: dict[str, Any] = {}
        for f in fields(node):
            if f.name == "span":
                continue
            val = getattr(node, f.name)
            if f.name == "where_fns" and isinstance(node, ast.FnDecl) and val:
                # #1433: a helper's own `forall` binders shadow the enclosing
                # function's (spec §5.6.2).  Substituting through them cloned
                # `forall<T> fn h` under a parent instantiated at `Bool` at
                # `Bool`, whatever `h` was called at — `h(7)` then called an
                # i32 clone with an i64 and the module failed to load.
                new_val = tuple(
                    self._substitute_in_ast(
                        helper, _unshadowed(mapping, helper.forall_vars),
                        reindex,
                    )
                    for helper in val
                )
                if all(n is o for n, o in zip(new_val, val)):
                    new_val = val
            else:
                new_val = self._substitute_value(val, mapping, reindex)
            if new_val is not val:
                changes[f.name] = new_val

        if changes:
            return replace(node, **changes)
        return node

    def _substitute_value(
        self, val: Any, mapping: dict[str, str],
        reindex: dict[int, int] | None = None,
    ) -> Any:
        """Recursively substitute type variables in a field value."""
        if isinstance(val, ast.Node):
            return self._substitute_in_ast(val, mapping, reindex)
        if isinstance(val, tuple):
            new_items = tuple(
                self._substitute_value(v, mapping, reindex) for v in val
            )
            if any(n is not o for n, o in zip(new_items, val)):
                return new_items
            return val
        return val

    def _substitute_type_expr(
        self, te: ast.TypeExpr, mapping: dict[str, str],
    ) -> ast.TypeExpr:
        """Substitute type variables in a TypeExpr, returning a TypeExpr."""
        result = self._substitute_in_ast(te, mapping)
        assert isinstance(result, ast.TypeExpr)  # noqa: S101
        return result
