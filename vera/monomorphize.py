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

import contextlib
import re
from collections.abc import (
    Callable,
    Collection,
    Iterable,
    Iterator,
    Mapping,
)
from dataclasses import dataclass, field, fields, replace
from typing import Any, cast

from vera import ast, naming
from vera.naming import EMPTY_ALIAS_ENV, AliasEnv
from vera.slots import (
    bare_call_denotes_user_fn,
    effect_op_result_names,
    fn_slot_scope,
)
from vera.types import PRIMITIVES, REMOVED_ALIASES, SpanTypeTable

# Identifier tokens inside a rendered type name (`Map<String, Int>` →
# `Map`, `String`, `Int`).  #1271 matches type-variable names against these
# rather than by substring, so `Unit` never reads as a mention of `U`.
_TYPE_NAME_TOKENS = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")


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
    the shared registries (``_fn_ret_type_exprs`` /
    ``_module_fn_ret_type_exprs``) stay namespace-free by construction.

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


def importer_occupied_bare_names(program: ast.Program) -> set[str]:
    """The bare SOURCE names *program*'s own declarations occupy (#1274/F3).

    The importer-side input to :func:`module_qualified_generic_names`, computed
    once so codegen and the verifier cannot answer it differently.  Two Pass-0
    transforms move helper names out of the bare namespace before anything
    resolves against it:

    * ``qualify_nested_generic_decls`` renames every nested GENERIC helper to
      ``parent$where$name`` (#1014);
    * codegen's ``_hoist_nongeneric_where_helpers`` lifts every non-generic
      helper that has no generic ancestor to a ``$``-qualified top-level decl
      (#991).

    What survives with a bare name is therefore every top-level function, plus
    the helpers neither transform touches — a NON-generic helper under a
    generic ancestor (the hoist skips generic subtrees, and the qualification
    only renames generic nodes).

    The rule is deliberately stated over the SOURCE shape so it is idempotent
    across BOTH transforms and their composition: run it on any of those
    programs and the extra top-level entries are all ``$``-mangled, which can
    never equal a module's source identifier, so the answer this predicate
    consumes is unchanged.  That is what lets the verifier — which holds the
    pre-transform AST — and codegen — which holds the post-transform one —
    reach the same set, and all three legs are asserted directly over a program
    carrying every helper shape this rule distinguishes.

    Pre-fix they did not: the verifier's walk counted a non-generic
    ``where``-helper named ``gen2`` as occupying the bare name while codegen,
    reading the hoisted program, did not, so an imported ``gen2`` was
    qualified-only on one side and bare-name-owning on the other — codegen
    emitted ``gen2$Bool`` while the verifier verified ``mod$lib$gen2$Bool``,
    and neither covered the other's clone.
    """
    out: set[str] = set()

    def walk_helpers(decl: ast.FnDecl, generic_ancestor: bool) -> None:
        for wfn in decl.where_fns or ():
            if generic_ancestor and not wfn.forall_vars:
                out.add(wfn.name)
            walk_helpers(wfn, generic_ancestor or bool(wfn.forall_vars))

    for tld in program.declarations:
        decl = tld.decl
        if isinstance(decl, ast.FnDecl):
            out.add(decl.name)
            walk_helpers(decl, bool(decl.forall_vars))
    return out


def module_qualified_generic_names(
    module_program: ast.Program,
    name_filter: set[str] | None,
    local_fn_names: set[str],
    *,
    direct: bool = True,
) -> set[str]:
    """The module's top-level generics reached ONLY under ``mod$<path>$name``.

    One predicate, shared by codegen and the verifier, for the naming rule
    non-generic module functions already follow (``_register_shadowed_import``):
    a module function keeps the importer's BARE name only when that name in the
    importer's flat namespace denotes this very declaration — public, inside the
    importer's import filter, and unshadowed by a local declaration.  Anything
    else is qualified-only: its clones are emitted (and discovered) under
    ``mod$<path>$name``, and every bare call to it from its own module's bodies
    is rerouted onto that identity.

    Pre-#1274 the rule for generics was ``private`` alone (#1000 / #1029), which
    covered only the case where the bare name could not POSSIBLY denote the
    module's generic.  The other two qualified-only cases were silently wrong:

    * **public but locally shadowed** — the module's own bare call resolved to
      the IMPORTER's same-named generic, so both modules' ``gen2`` mangled to one
      ``gen2$Bool``, one overwrote the other, and the module ran the importer's
      body with the module's proved contract (a false Tier-1, and invalid WASM
      where the two clones' WAT types differ);
    * **public but outside the import filter** — registered in no clone
      namespace at all, so the module's own bare call assembled to an
      ``unknown func``.

    ``local_fn_names`` is the importer's occupied bare-name set (the same one
    ``_register_shadowed_import`` consults); ``name_filter`` is ``None`` for a
    wildcard import.  ``direct`` is ``ResolvedModule.direct``: a module reached
    only transitively contributes nothing to the entry's namespace, so all of
    its generics are qualified-only whatever their visibility.
    """
    out: set[str] = set()
    for tld in module_program.declarations:
        decl = tld.decl
        if not isinstance(decl, ast.FnDecl) or not decl.forall_vars:
            continue
        owns_bare_name = (
            # A TRANSITIVE module's declarations are not in the entry program's
            # namespace at all (spec §8.6.4 — visibility is the importer's
            # property), so none of them can own its bare name.  Without this
            # the `import_names` lookup answers `None` for such a module — the
            # spelling that means "wildcard import" — and every one of its
            # public generics was classified a bare-name owner.
            direct
            and (tld.visibility or "private") == "public"
            and (name_filter is None or decl.name in name_filter)
            and decl.name not in local_fn_names
        )
        if not owns_bare_name:
            out.add(decl.name)
    return out


def module_qualified_generic_targets(
    module_program: ast.Program,
    qualified_by_path: Mapping[tuple[str, ...], set[str]],
    public_generics_by_path: Mapping[tuple[str, ...], set[str]],
    own_path: tuple[str, ...],
) -> dict[str, tuple[str, ...]]:
    """Bare name → the module that OWNS it, for every qualified-only generic
    reachable by a bare call from *module_program*'s bodies (#1274 F1).

    A module's bare call resolves in ITS namespace, which holds its own
    declarations and what it imports.  Codegen has one flat WASM namespace,
    though, so a name this module resolves to a generic is only safe to leave
    bare when that generic owns the flat bare name — which
    :func:`module_qualified_generic_names` decides, from the ENTRY program's
    point of view, once per module.

    The per-module reroute set was that module's OWN qualified-only generics
    alone, which silently missed the hop: ``mid`` declares no generics and calls
    ``deep``'s by bare name, so nothing was rerouted and the entry program's
    same-named generic captured the call — ``vera verify`` clean, ``mid``'s
    proved postcondition violated at run.  This adds the imports' sets under the
    SAME predicate, keyed by which module each name belongs to, because the
    ``mod$<path>$name`` identity is per-owner and ``mid``'s call must reach
    ``mod$deep$gen``, not ``mod$mid$gen``.

    Visibility is read from *this* module's side: only a PUBLIC name inside this
    module's own import filter is reachable here at all, so a private or
    out-of-filter generic of a dependency contributes nothing (it is not in this
    namespace to be called).  The module's OWN generics are applied last, so a
    local declaration shadows an import exactly as §8.5.2 requires.
    """
    # Whatever this module declares owns its own bare calls (§8.5.2), so an
    # import never contributes a name the module itself defines — otherwise a
    # module that declares `gen` AND imports another module's `gen` would have
    # its own calls rerouted to the dependency's clone.
    own_names = importer_occupied_bare_names(module_program)
    targets: dict[str, tuple[str, ...]] = {}
    for imp in module_program.imports:
        dep_path = tuple(imp.path)
        exported = public_generics_by_path.get(dep_path)
        if not exported:
            continue
        allowed = None if imp.names is None else set(imp.names)
        for name in qualified_by_path.get(dep_path, set()):
            if (
                name in exported
                and name not in own_names
                and (allowed is None or name in allowed)
            ):
                targets[name] = dep_path
    for name in qualified_by_path.get(own_path, set()):
        targets[name] = own_path
    return targets


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
    environment.  ``ambiguous`` is the union of those names over every
    namespace, which is what codegen's E608 rail asks — it decides whether a
    PAIR of modules may share the flat namespace at all, a question no single
    namespace answers.  Both come off one walk, so the layer that refuses
    early and the layer that backstops it cannot disagree about which shape
    is ambiguous.

    One derivation because there are four consumers and they must not
    disagree: codegen narrows its per-declaration ownership table with it
    (``_scoped_fn_names``), codegen's E608 rail reads the ambiguity union,
    the CHECKER refuses its own namespace's clashes (#1304), and the verifier
    narrows discovery with it.  Two walks over the same imports could differ
    about a filter or a visibility, and the two sides of the #732
    differential would then discover different clones.
    """

    by_namespace: Mapping[tuple[str, ...] | None, frozenset[str]]
    ambiguous: frozenset[str]
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
    ``setdefault`` and the incumbent wins — measured, with a module exporting
    its own one-argument ``option_map``, as ``E201`` against the PRELUDE's
    two-argument signature.

    That makes the two halves of the result behave differently under this
    argument, and the earlier claim that the ambiguity half is "identical
    either way" was wrong.  A dependency MAY export a prelude-named
    declaration — the combinators are overridable, not reserved
    (:func:`vera.prelude.overridable_builtin_names`) — so two dependencies
    exporting ``option_map`` are ambiguous under ``prelude=()`` and are not
    under the populated set.  Codegen calls
    ``_collect_namespace_fn_names`` twice, before and after its prelude pass,
    and its E608 rail reads the FIRST (prelude-empty) answer because
    ``_register_modules`` runs between them; the checker passes its built-in
    snapshot and so reads the populated one.  The ordering is therefore
    load-bearing rather than incidental, and is pinned by
    ``test_the_prelude_argument_changes_the_ambiguity_half``.
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
    return NamespaceFnNames(
        by_namespace,
        frozenset(
            name for clashes in ambiguous_sources.values() for name in clashes
        ),
        ambiguous_sources,
    )


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
    clash on the constructor alone, which is the shape codegen separates as
    E610 from E609.

    Only the CHECKER reads this.  Codegen's E609/E610 rails ask a different
    question — whether two modules' declarations can share the flat
    namespace at all — and answer it from declarations rather than from any
    namespace's imports, so they refuse a superset and stay as they are.
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


def public_generic_names(module_program: ast.Program) -> set[str]:
    """The module's PUBLIC top-level generic names — what a dependent can name
    at all, before that dependent's own import filter narrows it."""
    return {
        tld.decl.name
        for tld in module_program.declarations
        if isinstance(tld.decl, ast.FnDecl) and tld.decl.forall_vars
        and (tld.visibility or "private") == "public"
    }


def reroute_module_qualified_generic_calls(
    decl: ast.FnDecl,
    qualified_generics: Collection[str],
    make_call: Callable[[ast.FnCall, tuple[ast.Expr, ...]], ast.Node],
) -> ast.FnDecl:
    """Shadow-aware rewrite of bare calls to a module's QUALIFIED-ONLY top-level
    generics (#1000, widened by #1274).

    An imported body (a generic, a non-generic fn, or another generic) may call
    one of its module's own generics by bare name.  Once the importer clones or
    discovers that body, the bare name is resolved in the IMPORTER's flat
    namespace — where it denotes the module's generic only when that generic
    owns it (see :func:`module_qualified_generic_names`).  For every generic
    that does NOT, each such ``FnCall`` is replaced by ``make_call(node,
    rerouted_args)``: codegen builds an ``ast.ModuleCall`` (resolved by the
    desugar to the module's ``mod$<path>$name`` clone), while the verifier
    builds a name-renamed ``FnCall`` keyed to that same ``mod$…`` discovery
    base.  The SHARED shadow-aware walk is what keeps the two sides' routing (and
    thus the #732 differential) in lockstep.

    Shadow-aware (PR #1029 review): a ``where``-helper sharing a module
    generic's name lexically owns the bare call for its whole scope (spec §5), so
    rerouting it would run/verify the module generic instead of the
    lexically-nearer helper (a wrong body / wrong contract).  Each ``FnDecl``
    level adds its helpers' names to the shadow set for its body AND subtree.
    Only the matched call NODE changes (recursively rerouted args); every other
    node — including nested ``AnonFn`` / ``where`` bodies — is structurally
    preserved with its span.
    """
    if not qualified_generics:
        return decl

    def walk(node: object, shadowed: frozenset[str]) -> object:
        if isinstance(node, ast.FnDecl):
            level = shadowed | {wfn.name for wfn in node.where_fns or ()}
            changes: dict[str, Any] = {}
            for f in fields(node):
                if f.name == "span":
                    continue
                val = getattr(node, f.name)
                new_val = walk(val, level)
                if new_val is not val:
                    changes[f.name] = new_val
            if changes:
                return replace(node, **changes)
            return node
        if (isinstance(node, ast.FnCall)
                and node.name in qualified_generics
                and node.name not in shadowed):
            new_args = tuple(
                cast("ast.Expr", walk(a, shadowed)) for a in node.args
            )
            return make_call(node, new_args)
        if isinstance(node, ast.Node):
            changes = {}
            for f in fields(node):
                if f.name == "span":
                    continue
                val = getattr(node, f.name)
                new_val = walk(val, shadowed)
                if new_val is not val:
                    changes[f.name] = new_val
            if changes:
                return replace(node, **changes)
            return node
        if isinstance(node, tuple):
            new_items = tuple(walk(v, shadowed) for v in node)
            if any(n is not o for n, o in zip(new_items, node)):
                return new_items
            return node
        return node

    result = walk(decl, frozenset())
    assert isinstance(result, ast.FnDecl)  # noqa: S101
    return result


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
        wfn.name: f"{prefix}$where${wfn.name}"
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
                    wfn, f"{prefix}$where${wfn.name}", combined,
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
    byte the ``_module_qualified_wasm_name`` / ``_module_qualified_base`` prefix.
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


def uninferred_type_arg_fix(
    rec: "UninferredTypeArg", table: SpanTypeTable | None,
) -> str:
    """The [E622] ``fix`` sentence for one un-inferable type argument.

    Names the ARGUMENT's own type where the checker recorded one, because a
    fix a reader applies literally has to check: `let @T = …` names the
    generic's type VARIABLE, which is not in scope at the call site (E170,
    then E121 on the slot reference), and is wrong outright for any forall
    variable not spelled ``T``.  Spelling `let @Int = …` instead gives a
    program that checks, verifies and runs.

    Falls back to a shape-only instruction when nothing named the argument's
    type — the honest answer when the compiler is reporting that it could not
    name it.
    """
    named = (checker_clone_type_name(table, rec.arg)
             if table is not None else None)
    if named is not None:
        return (
            f"Bind the argument to a slot of its own and pass the slot "
            f"reference: 'let @{named} = <the argument>;' then "
            f"'{rec.fn_name}(@{named}.0)'. The type argument is then read "
            f"from the declared slot type instead of being inferred from the "
            f"argument expression."
        )
    return (
        f"Bind the argument to a slot whose declared type is the argument's "
        f"own type — 'let @<Type> = <the argument>;' — and pass that slot "
        f"reference to '{rec.fn_name}'. The type argument is then read from "
        f"the declared slot type instead of being inferred from the argument "
        f"expression."
    )


def checker_clone_type_name(
    table: SpanTypeTable | None, expr: ast.Expr,
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

    Returns ``None`` when there is no table, no entry for this span, or a type
    with no clone-name spelling (a still-generic ``TypeVar``, a function type,
    the checker's unknown) — in which case the caller is exactly as informed as
    it was before, and [E622] reports the hole rather than guessing at it.
    """
    if table is None:
        return None
    key = ast.span_key(expr)
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
    table: SpanTypeTable | None, expr: ast.Expr,
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
    key = ast.span_key(expr)
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


def pipe_desugared_call(
    expr: ast.Expr,
) -> ast.FnCall | ast.ModuleCall | None:
    """The call a ``|>`` pipe denotes, or ``None`` if *expr* is not one.

    ``a |> f(x, y)`` means ``f(a, x, y)``: the piped value becomes the call's
    FIRST argument.  Four places have to agree on that shape — the checker's
    ``_check_pipe``, codegen's ``_translate_binary``, instantiation
    discovery's pipe arm (#913) and the two type namers (#1365) — so it is
    built here once rather than spelled four times.

    The desugared call keeps the right operand's OWN node type.  A
    ``ModuleCall`` right operand stays a ``ModuleCall`` (#1357): its ``path``
    is what routes the call to the declaring module's ``mod$<path>$name``
    clone, and rebuilding it as a bare-name ``FnCall`` discards that path, so
    the call lands on a name the importer's flat namespace does not have.
    That is precisely how a piped module generic lost its caller while the
    direct spelling of the same call worked.

    Returns ``None`` for a non-pipe, and for a pipe whose right operand is
    neither call shape: the checker rejects that, so a consumer meeting one
    has nothing to say about it either.
    """
    if not isinstance(expr, ast.BinaryExpr) or expr.op != ast.BinOp.PIPE:
        return None
    rhs = expr.right
    if isinstance(rhs, ast.ModuleCall):
        return ast.ModuleCall(
            path=rhs.path, name=rhs.name,
            args=(expr.left, *rhs.args), span=expr.span,
        )
    if isinstance(rhs, ast.FnCall):
        return ast.FnCall(
            name=rhs.name, args=(expr.left, *rhs.args), span=expr.span,
        )
    return None


@dataclass(frozen=True)
class UninferredTypeArg:
    """One generic call whose type argument could not be inferred (E622).

    Recorded when a generic's parameter is *exactly* a type variable (``@T``)
    and this walker cannot name the argument bound to it, so the type variable
    stays unbound.  Before #1327/#1366 such a variable was silently substituted
    with the phantom-var default ``Bool`` — a substitution the compiler has no
    evidence for, which registers an instantiation that the call-site rewrite
    (whose own namer may well succeed) never calls.  The program stays
    check-green and verify-clean and loses its caller at codegen (E602/E620),
    or loads as invalid WebAssembly.

    The default itself is retained for the genuine phantom: a type variable
    that no parameter position determines (``E`` in
    ``result_unwrap_or(Ok(x), d)``) is not inferable from arguments *by
    construction*, and the emitted WASM is identical whatever it is named.
    This record marks only the other case — the variable a parameter DOES
    determine, whose argument the walker could not type.

    Attributes
    ----------
    fn_name:
        The generic function being called.
    type_var:
        The ``forall`` variable left unbound.
    arg_kind:
        AST class name of the argument that could not be named (the shape
        whose arm is missing, e.g. ``IndexExpr`` for #1327, ``ModuleCall``
        for #1366).
    arg:
        The argument node itself, so the consumer can locate the diagnostic
        on the expression (through its own span/prelude resolution) rather
        than on the enclosing function.
    origin:
        The module whose namespace the walk was in when the call was seen,
        or ``None`` for the entry program.  Without it a consumer pairs an
        imported module's line number with the ENTRY file's name and source,
        so the diagnostic points at the wrong file and quotes the wrong line.
    """

    fn_name: str
    type_var: str
    arg_kind: str
    arg: ast.Expr
    origin: tuple[str, ...] | None = None


# Builtin function name → SIMPLE Vera return-type name (type args dropped).
# Consulted by Monomorphizer._infer_fncall_vera_type_simple() (instantiation
# discovery) AND by the WASM call-rewrite chain
# (InferenceMixin._infer_fncall_vera_type, vera/wasm/inference.py) — the two
# consultors that must agree on clone names, or discovery emits one mangled
# suffix while the call site references another (dangling E602, #769 gap 1b).
# REGISTRY-COMPLETE (#769): covers every registered builtin whose return has
# a concrete outer constructor (TypeEnv._register_builtins is the key oracle;
# tests/test_codegen_monomorphize.py::TestBuiltinReturnTables769 enforces it).
# Values preserve the rewrite chain's historical names verbatim — e.g.
# string_length is "Int" (the WAT-collapsed name), string_char_code is
# "Nat" — because clone-NAME agreement is the invariant, not name precision;
# changing a value is a clone-granularity decision, not a completion.
# Bare-TypeVar returns (option_unwrap_or, await, …) must stay OUT: a fixed
# entry would bind phantom vars.  Ability-op names (show/hash) and apply_fn
# are not registry builtins and keep their logic arms in the chain.
_BUILTIN_VERA_RETURN_TYPES: dict[str, str] = {
    # array
    "array_all": "Bool",
    "array_any": "Bool",
    "array_append": "Array",
    "array_concat": "Array",
    "array_filter": "Array",
    "array_find": "Option",
    "array_flatten": "Array",
    "array_length": "Int",
    "array_map": "Array",
    "array_mapi": "Array",
    "array_range": "Array",
    "array_reverse": "Array",
    "array_slice": "Array",
    "array_sort_by": "Array",
    # async
    "async": "Future",
    # base64
    "base64_decode": "Result",
    "base64_encode": "String",
    # bool_to
    "bool_to_string": "String",
    # byte_to
    "byte_to_int": "Int",
    "byte_to_string": "String",
    # char
    "char_to_lower": "String",
    "char_to_upper": "String",
    # decimal
    "decimal_abs": "Decimal",
    "decimal_add": "Decimal",
    "decimal_compare": "Ordering",
    "decimal_div": "Option",
    "decimal_eq": "Bool",
    "decimal_from_float": "Decimal",
    "decimal_from_int": "Decimal",
    "decimal_from_string": "Option",
    "decimal_mul": "Decimal",
    "decimal_neg": "Decimal",
    "decimal_round": "Decimal",
    "decimal_sub": "Decimal",
    "decimal_to_float": "Float64",
    "decimal_to_string": "String",
    # float
    "float_clamp": "Float64",
    "float_is_infinite": "Bool",
    "float_is_nan": "Bool",
    "float_to_int": "Int",
    "float_to_string": "String",
    # html
    "html_attr": "Option",
    "html_parse": "Result",
    "html_query": "Array",
    "html_text": "String",
    "html_to_string": "String",
    # int_to
    "int_to_byte": "Option",
    "int_to_float": "Float64",
    "int_to_nat": "Option",
    "int_to_string": "String",
    # is_
    "is_alpha": "Bool",
    "is_alphanumeric": "Bool",
    "is_digit": "Bool",
    "is_lower": "Bool",
    "is_upper": "Bool",
    "is_whitespace": "Bool",
    # json
    "json_array_get": "Option",
    "json_array_length": "Int",
    "json_as_array": "Option",
    "json_as_bool": "Option",
    "json_as_int": "Option",
    "json_as_number": "Option",
    "json_as_object": "Option",
    "json_as_string": "Option",
    "json_get": "Option",
    "json_get_array": "Option",
    "json_get_bool": "Option",
    "json_get_int": "Option",
    "json_get_number": "Option",
    "json_get_string": "Option",
    "json_has_field": "Bool",
    "json_keys": "Array",
    "json_parse": "Result",
    "json_stringify": "String",
    "json_type": "String",
    # map_
    "map_contains": "Bool",
    "map_get": "Option",
    "map_insert": "Map",
    "map_keys": "Array",
    "map_new": "Map",
    "map_remove": "Map",
    "map_size": "Int",
    "map_values": "Array",
    # math/misc
    "abs": "Nat",
    "acos": "Float64",
    "asin": "Float64",
    "atan": "Float64",
    "atan2": "Float64",
    "ceil": "Int",
    "clamp": "Int",
    "cos": "Float64",
    "e": "Float64",
    "floor": "Int",
    "infinity": "Float64",
    "log": "Float64",
    "log10": "Float64",
    "log2": "Float64",
    "max": "Int",
    "min": "Int",
    "nan": "Float64",
    "pi": "Float64",
    "pow": "Float64",
    "round": "Int",
    "sign": "Int",
    "sin": "Float64",
    "sqrt": "Float64",
    "tan": "Float64",
    # md_
    "md_extract_code_blocks": "Array",
    "md_has_code_block": "Bool",
    "md_has_heading": "Bool",
    "md_parse": "Result",
    "md_render": "String",
    # nat_to
    "nat_to_int": "Int",
    "nat_to_string": "String",
    # option
    "option_and_then": "Option",
    "option_map": "Option",
    # parse
    "parse_bool": "Result",
    "parse_float64": "Result",
    "parse_int": "Result",
    "parse_nat": "Result",
    # regex
    "regex_find": "Result",
    "regex_find_all": "Result",
    "regex_match": "Result",
    "regex_replace": "Result",
    # result
    "result_map": "Result",
    # set_
    "set_add": "Set",
    "set_contains": "Bool",
    "set_new": "Set",
    "set_remove": "Set",
    "set_size": "Int",
    "set_to_array": "Array",
    # string
    "string_char_code": "Nat",
    "string_chars": "Array",
    "string_concat": "String",
    "string_contains": "Bool",
    "string_ends_with": "Bool",
    "string_from_char_code": "String",
    "string_index_of": "Option",
    "string_join": "String",
    "string_length": "Int",
    "string_lines": "Array",
    "string_lower": "String",
    "string_pad_end": "String",
    "string_pad_start": "String",
    "string_repeat": "String",
    "string_replace": "String",
    "string_reverse": "String",
    "string_slice": "String",
    "string_split": "Array",
    "string_starts_with": "Bool",
    "string_strip": "String",
    "string_trim_end": "String",
    "string_trim_start": "String",
    "string_upper": "String",
    "string_words": "Array",
    # to_string
    "to_string": "String",
    # url
    "url_decode": "Result",
    "url_encode": "String",
    "url_join": "String",
    "url_parse": "Result",
}

# Builtins returning FULLY-CONCRETE parameterized types — maps function name
# to (outer_type, (inner_type, ...)) for _get_arg_type_info() and its WASM
# twin _get_arg_type_info_wasm (vera/wasm/inference.py imports this dict, so
# additions fix discovery and call-rewrite atomically).  REGISTRY-COMPLETE
# (#769): exactly the registered builtins whose return is an AdtType with
# type args and no embedded TypeVar, values as the registry's pretty names
# (nested inners like "Array<Json>" parse via _parse_type_name); enforced by
# tests/test_codegen_monomorphize.py::TestBuiltinReturnTables769.  Builtins
# whose return keeps a type var (array_map, map_get, …) must stay OUT —
# they are handled by the generic-return / arg-forwarding resolution.
_BUILTIN_PARAMETERIZED_RETURNS: dict[str, tuple[str, tuple[str, ...]]] = {
    # array
    "array_range": ("Array", ("Int",)),
    # base64
    "base64_decode": ("Result", ("String", "String")),
    # decimal
    "decimal_div": ("Option", ("Decimal",)),
    "decimal_from_string": ("Option", ("Decimal",)),
    # html
    "html_attr": ("Option", ("String",)),
    "html_parse": ("Result", ("HtmlNode", "String")),
    "html_query": ("Array", ("HtmlNode",)),
    # int_to
    "int_to_byte": ("Option", ("Byte",)),
    "int_to_nat": ("Option", ("Nat",)),
    # json
    "json_array_get": ("Option", ("Json",)),
    "json_as_array": ("Option", ("Array<Json>",)),
    "json_as_bool": ("Option", ("Bool",)),
    "json_as_int": ("Option", ("Int",)),
    "json_as_number": ("Option", ("Float64",)),
    "json_as_object": ("Option", ("Map<String, Json>",)),
    "json_as_string": ("Option", ("String",)),
    "json_get": ("Option", ("Json",)),
    "json_get_array": ("Option", ("Array<Json>",)),
    "json_get_bool": ("Option", ("Bool",)),
    "json_get_int": ("Option", ("Int",)),
    "json_get_number": ("Option", ("Float64",)),
    "json_get_string": ("Option", ("String",)),
    "json_keys": ("Array", ("String",)),
    "json_parse": ("Result", ("Json", "String")),
    # md_
    "md_extract_code_blocks": ("Array", ("String",)),
    "md_parse": ("Result", ("MdBlock", "String")),
    # parse
    "parse_bool": ("Result", ("Bool", "String")),
    "parse_float64": ("Result", ("Float64", "String")),
    "parse_int": ("Result", ("Int", "String")),
    "parse_nat": ("Result", ("Nat", "String")),
    # regex
    "regex_find": ("Result", ("Option<String>", "String")),
    "regex_find_all": ("Result", ("Array<String>", "String")),
    "regex_match": ("Result", ("Bool", "String")),
    "regex_replace": ("Result", ("String", "String")),
    # string
    "string_chars": ("Array", ("String",)),
    "string_index_of": ("Option", ("Nat",)),
    "string_lines": ("Array", ("String",)),
    "string_split": ("Array", ("String",)),
    "string_words": ("Array", ("String",)),
    # url
    "url_decode": ("Result", ("String", "String")),
    "url_parse": ("Result", ("UrlParts", "String")),
}


@dataclass(frozen=True)
class MonoContext:
    """Registration metadata for instantiation discovery + substitution.

    Built independently by each consumer — codegen from its layout/signature
    mixin state, the verifier from :class:`~vera.environment.TypeEnv` — but the
    shape is identical so :class:`Monomorphizer`'s leaf logic is shared.  All
    fields are AST-level (no WASM types), which is what lets the verifier import
    this module without dragging in the codegen backend.

    * ``generic_decls`` — generic function name → its ``FnDecl``.
    * ``ctor_to_adt`` — constructor name → owning ADT name.
    * ``ctor_tp_indices`` — constructor name → per-field ADT type-param index
      (``None`` for fields that bind no type param).  Lets sparse constructors
      like ``Err(e)`` map their single field to ``Result``'s *second* type param.
    * ``adt_tp_counts`` — ADT name → number of type parameters.
    * ``type_aliases`` / ``type_alias_params`` — alias name → body ``TypeExpr`` /
      declared alias parameter names (for FnType-alias argument resolution).
    * ``fn_ret_types`` — function name (top-level **and** ``where`` helpers,
      keyed by bare name) → *simple* Vera return-type name, **type args dropped**
      (``Map<String, Int>`` → ``"Map"``; contrast the full names
      ``_get_arg_type_info`` / ``_infer_vera_type_name`` carry).  Codegen builds
      it from its WAT signatures (i64→Int, i32→Bool, f64→Float64) to reproduce
      the prior ``_infer_fncall_vera_type_simple`` behaviour exactly; the
      verifier builds it from declared AST return types, keeping the *more
      precise* name (``Nat``, ``Byte``).  The two value-spaces are deliberately
      related by the fixed collapse ``{Nat→Int, Byte→Bool}`` — the verifier's
      discovered set is a sound superset under that normalization, which the
      #732 differential test maintains (its ``collapse`` table is the one place
      that mapping lives) and pins.
    * ``alias_env`` — the same alias namespace as the two maps above, carried
      as the one value :mod:`vera.naming` renders against (#1208).
    * ``fn_ret_type_exprs`` — function name (bare-keyed, same as ``fn_ret_types``)
      → declared return **TypeExpr** (type args RETAINED, unlike ``fn_ret_types``).
      Lets discovery recover a user fn's *parameterized* return (`maybe → Option<Decimal>`)
      in `Option<T>` argument position, mirroring the WASM call-rewrite's
      ``_fn_ret_type_exprs`` so the two consultors pick the same clone (#899 issue 1).
      Optional (defaults empty): a consumer that doesn't populate it simply
      loses the user-fn parameterized-return recovery, degrading to the prior
      (bare-name) behaviour rather than erroring.
    * ``fn_names`` — every function name this consumer's own table owns, used
      for ONE decision: whether a bare ``get``/``put`` CALL SITE is an effect
      operation here at all (#1207, #1284).  This is discovery's leg of
      :func:`~vera.slots.bare_call_denotes_user_fn`, the predicate codegen
      asks at its own dispatch through ``_bare_call_denotes_op`` and the
      checker asks when it resolves the name; discovery has to make the same
      call or the two consultors desync in the shadowed direction.  It is
      asked at the LOOKUP, never at the two registry installs — the declared
      row and the handler expression both record their ops unfiltered,
      exactly as codegen's two injection sites do.  Optional (defaults
      empty): a consumer that doesn't populate it treats no name as
      shadowed, which is the answer for a program that declares no function
      of an op's name — every program until one does.
    """

    generic_decls: dict[str, ast.FnDecl]
    ctor_to_adt: dict[str, str]
    ctor_tp_indices: dict[str, tuple[int | None, ...]]
    adt_tp_counts: dict[str, int]
    type_aliases: dict[str, ast.TypeExpr]
    type_alias_params: dict[str, tuple[str, ...]]
    fn_ret_types: dict[str, str]
    fn_ret_type_exprs: dict[str, ast.TypeExpr] = field(default_factory=dict)
    # #1208: the naming environment for this consumer's alias namespace — the
    # `type_aliases` / `type_alias_params` pair above as ONE value, plus the
    # declared-ADT names.  Defaulted empty so a consumer that has not been
    # threaded yet behaves exactly as before.
    alias_env: AliasEnv = EMPTY_ALIAS_ENV
    # #1207: the consumer's own function-name table (see the docstring).
    fn_names: frozenset[str] = frozenset()
    # #1299: the per-namespace visibility tables ``fn_names`` is NARROWED by
    # while a declaration is being walked.  ``fn_names`` is flat — every
    # symbol the consumer registered, including a module's private helpers —
    # so on its own it answers "user-owned" for a name the walked body cannot
    # see, and discovery then names a clone from that invisible declaration's
    # return type while the WASM rewrite names one from the operation's.  The
    # narrowing is entered per declaration by :meth:`namespace_scope`, which
    # each consumer wraps its seed walk in.  Defaulted ``None``: a consumer
    # that has not been threaded, or a walk entered outside any scope, keeps
    # the flat answer — never an EMPTY one, which would claim no name at all.
    namespace_fn_names: NamespaceFnNames | None = None
    # #1274 (F1): ``(module path, name)`` pairs whose generic is QUALIFIED-ONLY
    # — reached under ``mod$<path>$name``, never under the bare name.  A
    # ``ModuleCall`` to one of these must NOT be discovered as an instantiation
    # of whatever ``generic_decls`` holds for its bare name, because that entry
    # belongs to somebody else (the importer's same-named generic).  Defaulted
    # empty: a consumer that routes these by RENAMING the call instead (the
    # verifier) never presents such a node here, so it needs no entry.
    qualified_module_generics: frozenset[tuple[tuple[str, ...], str]] = (
        frozenset()
    )
    # #1327/#1366/#1369: the checker's span-keyed resolved-type table for the
    # ENTRY program — the single source both type namers fall back to when
    # their own walk names nothing (see :func:`checker_clone_type_name`).  The
    # ENTRY program's, deliberately: codegen and the verifier are both handed
    # exactly this table by the CLI, so both consultors back off to the same
    # answers and the #732 emitted-versus-discovered differential stays an
    # equality.  Threading a per-module table to only one of them would buy
    # reach on that side and a false Tier 1 on the other.  Defaulted ``None``:
    # a consumer that has not been threaded keeps the pre-#1327 behaviour,
    # where an unnameable argument is [E622] rather than a guess.
    expr_types: SpanTypeTable | None = None


class Monomorphizer:
    """Instantiation discovery + AST substitution over a :class:`MonoContext`.

    Stateless apart from ``ctx``; safe to construct per-pass.  Orchestration
    (the seed walk + transitive worklist, and whether to filter
    constraint-failing instances) is the caller's responsibility — see
    ``MonomorphizationMixin._monomorphize`` (codegen) and the verifier's
    per-instance loop (#732).
    """

    def __init__(self, ctx: MonoContext) -> None:
        self.ctx = ctx
        # #1207: the effect-op result-type registry IN SCOPE at the point the
        # discovery walk has reached — the discovery-side twin of codegen's
        # `_effect_op_result_vera`, MERGED over the enclosing registry at each
        # `handle` exactly as `_translate_handle_state` merges it — an inner
        # mapping overwrites a same-name outer one, an absent inner mapping
        # leaves the outer one answering.  See the `HandleExpr` arm in
        # `_collect_calls` for why the merge is load-bearing: an `Exn` handler
        # nested in a `State<Nat>` one must leave the enclosing result type in
        # scope, or discovery names `pick$Int` against the rewrite's
        # `pick$Nat` (#1207).  Seeded from a
        # function's declared effect row by `collect_calls_in_node`.  Walk
        # state, not context: it is pushed and popped by `_collect_calls` and
        # is empty outside a walk, so `Monomorphizer` stays re-entrant per
        # pass in the way its docstring promises.
        self._op_result_types: dict[str, str] = {}
        # #1271: the type VARIABLES in scope at the point the discovery walk has
        # reached — every enclosing ``forall`` binder, pushed and popped by
        # `collect_calls_in_node` exactly as `_op_result_types` is.  Walk state,
        # not context: empty outside a walk.
        self._scope_type_vars: frozenset[str] = frozenset()
        # #1271 memos over the fixed `ctx`, filled on first use.  Both are
        # derived purely from `ctx`, which no discovery walk mutates.
        self._ctx_type_vars_cached: frozenset[str] | None = None
        self._declared_types_cached: frozenset[str] | None = None
        # #1274 (F1): the module whose OWN shadowed generics the current scan is
        # keyed on, or ``None`` outside such a scan.  Walk state, like the two
        # above it — see `shadowed_module_scope`.
        self._shadowed_scan_path: tuple[str, ...] | None = None
        # #1299: the bare names visible where the walk currently is — the
        # namespace's own (see `namespace_scope`) plus the `where` helpers of
        # every enclosing function, accumulated by `collect_calls_in_node`
        # exactly as `_scope_type_vars` is.  ``None`` means no scope was
        # entered, and `_bare_call_is_user_fn` then answers from the flat
        # `ctx.fn_names` alone — the pre-#1299 behaviour.
        self._scope_fn_names: frozenset[str] | None = None
        # #1327/#1366: every type variable this walker could not infer from
        # the argument a parameter binds it to DIRECTLY — the fail-closed
        # record behind [E622].  Accumulated across the whole discovery run
        # (seed walk + transitive worklist) and drained by the consumer, which
        # turns each entry into a diagnostic: codegen refuses to emit a module
        # whose instantiation set rests on a guess, and the verifier refuses to
        # report a tier for a clone that may not be the one codegen emits.
        # Deduplicated on (fn_name, type_var, span) because the same call site
        # is walked once per re-seed round.
        self.uninferred_type_args: list[UninferredTypeArg] = []
        self._uninferred_seen: set[tuple[str, str, object]] = set()
        # The module namespace the walk is currently in (`namespace_scope`),
        # carried onto every record so a diagnostic names the right file.
        self._namespace_path: tuple[str, ...] | None = None

    @contextlib.contextmanager
    def namespace_scope(
        self, path: tuple[str, ...] | None,
    ) -> Iterator[None]:
        """Walk declarations that resolve bare names in *path*'s namespace.

        Inside this scope :meth:`_bare_call_is_user_fn` narrows the consumer's
        flat ``fn_names`` to what that namespace can actually NAME, so an
        imported module's private declaration stops claiming a bare ``get``
        the entry program's body meant as the ``State`` operation (#1299).

        A no-op when the consumer supplied no visibility tables: the walk then
        keeps answering from the flat table, which is what every consumer did
        before this existed.  ``path=None`` is the entry program's namespace,
        which is a real answer rather than an absence — a body there sees the
        entry's own declarations and its direct imports' public, in-filter
        names, and nothing else.
        """
        # #1327 (PR #1368 review): the PATH is recorded whatever the
        # consumer supplied, because a diagnostic raised from this walk has
        # to name the file the call is written in — that is a fact about
        # where the walk is, not about whether the consumer built visibility
        # tables.  The fn-name narrowing below stays conditional.
        # ONE save/restore for both fields.  Splitting it left the
        # visible-tables branch — the common one, since the verifier always
        # builds those tables and codegen builds them whenever
        # `_namespace_tables` is populated — restoring `_scope_fn_names` and
        # NOT `_namespace_path`, so the path stayed pinned after the block
        # exited.  A later record made outside any scope (the verifier's
        # `walk_seed` calls `_infer_type_args_from_args` directly) then took
        # the stale path as its origin and named a previously-walked module's
        # file: precisely the misattribution `origin` exists to prevent.
        saved_path = self._namespace_path
        saved = self._scope_fn_names
        self._namespace_path = path
        if self.ctx.namespace_fn_names is not None:
            self._scope_fn_names = self.ctx.namespace_fn_names.visible(path)
        try:
            yield
        finally:
            self._namespace_path = saved_path
            self._scope_fn_names = saved

    def _bare_call_is_user_fn(self, name: str) -> bool:
        """Discovery's leg of :func:`~vera.slots.bare_call_denotes_user_fn`.

        The consumer's own table AND the lexical scope the walk is in — a
        narrowing, never a widening, so a consumer that entered no scope (or
        supplied no tables) gets exactly the flat answer it got before.

        Every ``$``-bearing name is admitted whatever the scope says, on the
        same reasoning as codegen's ``_scoped_fn_names``: ``$`` is outside
        ``LOWER_IDENT``, so a mangled name is never what a bare source call
        spells, and a clone name reaching here after a rewrite must keep
        answering as the declaration it was minted from.
        """
        if not bare_call_denotes_user_fn(name, self.ctx.fn_names):
            return False
        if self._scope_fn_names is None or "$" in name:
            return True
        return name in self._scope_fn_names

    @contextlib.contextmanager
    def shadowed_module_scope(
        self, path: tuple[str, ...],
    ) -> Iterator[None]:
        """Scan a clone body against *path*'s OWN qualified-only generics.

        Inside this scope a ``ModuleCall`` targeting *path* is discovered
        normally: the table it is matched against holds that module's generics
        by bare name, so the entry found is the intended one.  Outside it the
        same node is skipped, because the flat table's entry for that bare name
        belongs to whoever owns it in the importer's namespace.

        Both sides drive it around the identical scan, so their discovered sets
        stay equal (#732).
        """
        saved = self._shadowed_scan_path
        self._shadowed_scan_path = path
        try:
            yield
        finally:
            self._shadowed_scan_path = saved

    def collect_calls_in_expr(
        self,
        expr: ast.Expr,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Collect every generic call site reachable from ``expr``.

        Public because it is the shared discovery contract: both codegen
        (Pass 1.5) and the verifier (#732) drive it, and per-monomorphization
        verification is sound only if the verifier discovers a superset of what
        codegen emits.  The walk is TOTAL over the AST — it visits every child
        via dataclass fields — so a generic call nested in ANY form
        (``ArrayLit``, ``IndexExpr``, ``InterpolatedString``, a quantifier, …)
        is discovered, not just the forms an explicit arm happened to list.

        This is byte-identical for compiling programs: a generic call in a form
        codegen can't lower would be a dangling reference, so any program that
        DOES compile already has every generic call in a walked position; the
        total walk only adds coverage for programs that wouldn't compile anyway.
        """
        self._collect_calls(expr, generic_decls, ctor_to_adt, instances)

    def collect_calls_in_node(
        self,
        fn: ast.FnDecl,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Collect generic calls reachable from a whole ``FnDecl`` — its body,
        its contract predicates, AND its ``where`` helpers.

        This is the function-level shared discovery contract.  A generic called
        only from a ``requires`` / ``ensures`` / ``decreases`` clause (which Vera
        lowers to a runtime contract check) or only from a ``where`` helper body
        is still emitted by codegen and invoked at runtime, so codegen's Pass 1.5
        and the verifier (#732) must BOTH seed from this node-level walk — not
        just ``decl.body``.  Walking only the body makes codegen miss the clone
        (a ``CodegenSkip`` at run time) and diverge from the verifier, which does
        walk contracts and helpers (PR #767 review).
        """
        # #1207: the function's DECLARED effect row is the outermost
        # effect-op scope for everything below — codegen's per-function
        # `effect_op_result_vera` (codegen/functions.py), rebuilt from the
        # same shared derivation, with this site's `_fn_sigs` shadow guard
        # spelled as `ctx.fn_names`.  Saved and restored so a `where` helper
        # (walked recursively below) cannot leak its own row outwards.
        saved_ops = self._op_result_types
        self._op_result_types = self._row_op_result_types(fn)
        # #1271: this function's own ``forall`` binders join the enclosing
        # scope's for the whole subtree (body, contracts, `where` helpers).
        # A helper under a generic ancestor is walked through this same door,
        # so the set accumulates down the nesting exactly as the binders do.
        saved_vars = self._scope_type_vars
        self._scope_type_vars = saved_vars | frozenset(fn.forall_vars or ())
        # #1299: and this function's own `where` helpers join the visible-name
        # scope for the same subtree, for the same reason the binders do — a
        # helper is in its parent's scope and in its siblings', and in nobody
        # else's.  Only inside a `namespace_scope`: outside one the walk keeps
        # the flat answer, and starting to accumulate would silently turn that
        # into an almost-empty scope.
        #
        # The walked function's OWN name is deliberately NOT added.  A
        # top-level one is already in its namespace's set, and a helper or a
        # clone is `$`-qualified and admitted by that rule — so adding it
        # changes no answer, and it made the scope carry the enclosing
        # CLONE's name, which differs between the two sides for one helper
        # walked under two instantiations.  Textually divergent, semantically
        # identical, and the differential could not tell those apart.
        saved_names = self._scope_fn_names
        if saved_names is not None:
            self._scope_fn_names = saved_names | {
                wfn.name for wfn in (fn.where_fns or ())
            }
        try:
            self._collect_calls_in_node_scoped(
                fn, generic_decls, ctor_to_adt, instances,
            )
        finally:
            self._op_result_types = saved_ops
            self._scope_type_vars = saved_vars
            self._scope_fn_names = saved_names

    def _binds_a_type_var(
        self,
        type_args: tuple[str, ...],
        decl: ast.FnDecl,
        generic_decls: dict[str, ast.FnDecl],
    ) -> bool:
        """Is *type_args* a phantom instantiation — one that binds a type
        VARIABLE rather than a type (#1271)?

        Discovery infers a callee's type arguments from its argument
        expressions.  Inside a still-generic scope those expressions can be
        typed by a variable rather than a type: ``pick(@U.1, @U.0)`` in
        ``forall<U> fn helper`` binds ``pick``'s variable to the NAME ``U``, and
        a callee's own declared return type can leak the same way
        (``b(leaf(…), …)`` binds ``b``'s variable to ``leaf``'s ``W``).  Neither
        is an instantiation: the resulting clone's parameter has no WASM type, so
        codegen emitted it only to skip it with a loud ``[E604]``, and the
        verifier discovered a matching phantom.  The REAL instantiation appears
        once the enclosing scope is bound — ``helper$Bool``'s body yields
        ``pick$Bool`` — which is why filtering here loses nothing.

        A name counts as a type variable when some ``forall`` in play binds it —
        the scope's own binders, the callee's, and those of every generic
        discovery is keyed on — and nothing in this namespace makes it a TYPE.
        That subtraction is what keeps a program whose data type happens to
        share a binder's spelling (``data T``) instantiating normally: a name
        that names a type is a type here, whatever some other signature calls
        its variable.

        Components are matched by identifier token, never by substring, so
        ``Option<U>`` is phantom while ``Unit`` is not.
        """
        type_vars = self._scope_type_vars | frozenset(decl.forall_vars or ())
        type_vars |= self._ctx_generic_type_vars()
        type_vars |= frozenset(
            v for gdecl in generic_decls.values()
            for v in (gdecl.forall_vars or ())
        )
        type_vars -= self._declared_type_names()
        if not type_vars:
            return False
        return any(
            token in type_vars
            for arg in type_args
            for token in _TYPE_NAME_TOKENS.findall(arg)
        )

    def _ctx_generic_type_vars(self) -> frozenset[str]:
        """Every ``forall`` binder across the context's generics, memoised.

        The context is fixed for a pass while ``_binds_a_type_var`` runs once
        per discovered call site, so recomputing this per site is pure cost.
        """
        cached = self._ctx_type_vars_cached
        if cached is None:
            cached = frozenset(
                v for gdecl in self.ctx.generic_decls.values()
                for v in (gdecl.forall_vars or ())
            )
            self._ctx_type_vars_cached = cached
        return cached

    def _declared_type_names(self) -> frozenset[str]:
        """Every name that denotes a TYPE here — the built-in primitives and
        the removed aliases the checker still recognizes, plus this namespace's
        ADTs and type aliases (memoised).

        The subtrahend of the #1271 type-variable test: a ``forall`` binder's
        spelling is only evidence of a variable where nothing else claims the
        name.  The primitives are in the set because a binder may legally BE
        spelled ``Int`` — the language does not reserve type names against
        binders — and reading that spelling as a variable poisons every genuine
        instantiation at ``Int`` anywhere in the program, dropping functions
        from a program that compiled before this filter existed.  Erring the
        other way costs only the pre-existing ``[E604]`` on the pathological
        template itself.

        Whether the checker should REJECT a primitive-spelled binder outright
        is a language question (it would make this subtraction unreachable for
        the primitives); it is deliberately not decided here.
        """
        cached = self._declared_types_cached
        if cached is None:
            cached = (
                frozenset(PRIMITIVES)
                | frozenset(REMOVED_ALIASES)
                | frozenset(self.ctx.adt_tp_counts)
                | frozenset(self.ctx.ctor_to_adt.values())
                | frozenset(self.ctx.type_aliases)
            )
            self._declared_types_cached = cached
        return cached

    def _row_op_result_types(self, fn: ast.FnDecl) -> dict[str, str]:
        """The effect-op result registry a function's declared row installs.

        Unfiltered by shadowing (#1284), matching both the handler-expression
        merge below and codegen's two injection sites: the table says what
        each op name results in, and whether a given call site is that
        operation is asked at the site, in ``_infer_vera_type_name``.
        """
        if not isinstance(fn.effect, ast.EffectSet):
            return {}
        return dict(effect_op_result_names(fn.effect.effects))

    def _collect_calls_in_node_scoped(
        self,
        fn: ast.FnDecl,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """:meth:`collect_calls_in_node`'s walk, with the op scope already set."""
        self.collect_calls_in_expr(
            fn.body, generic_decls, ctor_to_adt, instances,
        )
        for contract in fn.contracts:
            # Requires/Ensures/Invariant carry a single `.expr`; Decreases
            # carries `.exprs` (a tuple of termination measures).
            preds = list(getattr(contract, "exprs", ()) or ())
            single = getattr(contract, "expr", None)
            if single is not None:
                preds.append(single)
            for pred in preds:
                self.collect_calls_in_expr(
                    pred, generic_decls, ctor_to_adt, instances,
                )
        for wfn in fn.where_fns or ():
            self.collect_calls_in_node(
                wfn, generic_decls, ctor_to_adt, instances,
            )

    def collect_clone_nested_generic_instances(
        self,
        clone: ast.FnDecl,
        ctor_to_adt: dict[str, str],
    ) -> dict[str, tuple[ast.FnDecl, set[tuple[str, ...]]]]:
        """Discover instantiations of a monomorphized clone's still-generic
        ``where``-helpers (generic-under-generic, #1002).

        A ``forall`` helper under a GENERIC ancestor is carried — still generic
        — into every clone of the ancestor by :meth:`monomorphize_fn`, but the
        ancestor's own type variables are the only ones substituted, so the
        helper stays a template that nothing instantiates (its clone-body call
        dangles at ``unknown func``).  This is the SHARED leaf both sides drive
        to close that gap: given ``clone`` (a concrete-at-its-own-level clone),
        it returns ``{helper bare name: (helper FnDecl, {concrete type vectors})}``
        for each of ``clone``'s DIRECT generic ``where``-helpers, discovering
        each helper's instantiations by its bare name everywhere it is
        lexically visible inside ``clone`` — the clone body, the clone's
        contract predicates, and its sibling ``where``-helper bodies.

        The returned ``FnDecl`` is the helper AS CARRIED IN THE CLONE (the
        ancestor's type variables already substituted), so a nested generic
        whose signature references the ancestor's type parameter is keyed with
        that parameter already bound — which is what makes a per-clone concrete
        clone name (``outer$Int$where$ginner$U``) collision-free across distinct
        ancestor instantiations.  Only DIRECT generic helpers are returned;
        deeper nesting is reached when each helper's own clone is processed
        (monomorphizing it binds its type variable and re-exposes its subtree),
        so callers recurse per level rather than descending here.
        """
        generic_helpers = {
            wfn.name: wfn
            for wfn in (clone.where_fns or ())
            if wfn.forall_vars
        }
        if not generic_helpers:
            return {}
        found = self.collect_generic_helper_instances(
            generic_helpers, (clone,), ctor_to_adt,
        )
        return {
            name: (generic_helpers[name], cts)
            for name, cts in found.items()
            if cts
        }

    def collect_generic_helper_instances(
        self,
        helpers: dict[str, ast.FnDecl],
        bodies: Iterable[ast.FnDecl],
        ctor_to_adt: dict[str, str],
    ) -> dict[str, set[tuple[str, ...]]]:
        """Instantiations of *helpers* called from any of *bodies* (#1223).

        The leaf under :meth:`collect_clone_nested_generic_instances`, exposed
        separately because a helper family is not fully discovered from the
        ancestor clone alone.  A helper's own CONCRETE clone can call a SIBLING
        helper at a type only that clone knows: inside the still-generic
        ``outer<U>``, ``inner(@U.1, @U.0)`` binds ``inner``'s variable to the
        NAME ``U``, and the real ``inner<Bool>`` appears only once ``outer`` is
        monomorphized at ``Bool``.  Both sides therefore drive this over a
        GROWING body set — each clone produced is fed back in — rather than
        over the ancestor once, and they must drive the same leaf or the
        verifier stops covering what codegen emits.

        Returns ``{helper name: {concrete type vectors}}``, one entry per
        helper (possibly empty), so a caller can diff against what it has
        already emitted.
        """
        found: dict[str, set[tuple[str, ...]]] = {
            name: set() for name in helpers
        }
        for body in bodies:
            self.collect_calls_in_node(body, helpers, ctor_to_adt, found)
        return found

    def _collect_calls(
        self,
        node: object,
        generic_decls: dict[str, ast.FnDecl],
        ctor_to_adt: dict[str, str],
        instances: dict[str, set[tuple[str, ...]]],
    ) -> None:
        """Total AST recursion underlying :meth:`collect_calls_in_expr`."""
        # #774: a qualified call `m::g(…)` to an imported generic is an
        # ``ast.ModuleCall``, not a ``FnCall`` — discover it identically (same
        # arg-driven type inference) so the importer monomorphizes the same
        # instantiation for both call forms.  Keyed on ``generic_decls``: the
        # caller merges imported (unshadowed) generics into that dict, so a
        # ModuleCall only matches once its target is a known generic.
        if isinstance(node, (ast.FnCall, ast.ModuleCall)) and (
            node.name in generic_decls
        ) and not (
            # #1274 (F1): a qualified call whose target is QUALIFIED-ONLY is not
            # a call to the bare name at all — its clone is emitted under
            # ``mod$<path>$name`` by the shadowed path.  Discovering it against
            # the FLAT table would instantiate whichever generic happens to own
            # the bare name (the importer's), emitting a clone nothing calls and
            # the other side never verifies.  Only the QUALIFIED spelling is
            # skipped; a bare call to an unshadowed imported generic still
            # routes here, which is what #774 needs.
            #
            # Not skipped inside that module's OWN shadowed scan
            # (``shadowed_module_scope``): there the table IS the module's
            # generics keyed by bare name, so ``m::bb`` from ``m``'s own clone
            # body is exactly the entry meant — the #1000/#1029 private chain.
            isinstance(node, ast.ModuleCall)
            and tuple(node.path) != self._shadowed_scan_path
            and (tuple(node.path), node.name)
            in self.ctx.qualified_module_generics
        ):
            decl = generic_decls[node.name]
            type_args = self._infer_type_args_from_args(
                decl, node.args, ctor_to_adt, generic_decls,
            )
            if type_args is not None and not self._binds_a_type_var(
                type_args, decl, generic_decls,
            ):
                instances[node.name].add(type_args)
        # #913: a generic invoked via the ``|>`` pipe — ``x |> g(…)`` — desugars
        # to ``g(x, …)`` at BOTH the checker (`_check_pipe`) and codegen
        # (`_translate_binary`) boundaries, prepending the piped LHS as the
        # call's FIRST argument.  Discovery must reconstruct that same argument
        # list, or the bare RHS ``FnCall``/``ModuleCall`` (whose own `args`
        # omit the piped value) fails to bind the type variable that the piped
        # value supplies — so no ``g$Type`` clone is emitted and codegen lowers
        # the pipe to a call on a non-existent function (the enclosing fn is
        # dropped at run).  The RHS itself is walked by the generic field
        # recursion below, so an inner generic call reachable through the RHS
        # is still discovered; this branch only adds the pipe-desugared
        # instantiation.
        piped = (pipe_desugared_call(node)
                 if isinstance(node, ast.Expr) else None)
        if piped is not None:
            # #1357: walk the DESUGARED call rather than adding an
            # instantiation beside the raw pipe.  The raw right operand is a
            # call whose own `args` omit the piped value, so walking it as a
            # call in its own right inferred a generic's type arguments from
            # an argument list that is missing its first element — nothing
            # bound the type variable, and the phantom default registered a
            # `$Bool` clone that nothing calls, beside (or instead of) the one
            # the call site needs.  The desugared node carries the same
            # children, so nothing goes unwalked; it is simply seen as the
            # call it denotes.
            self._collect_calls(
                piped, generic_decls, ctor_to_adt, instances,
            )
            return
        # #1207: a `handle[State<T>]` installs its op registry over its BODY
        # only.  The state-init expression and the clause bodies belong to the
        # ENCLOSING context — the checker checks clauses before the handled
        # effect joins the row, and codegen threads the declaration-time
        # snapshot into every clause (#1211) — so a `get(())` there names the
        # OUTER cell.  Walking those children under this handler's scope would
        # make discovery pick the inner cell's clone where the rewrite calls
        # the outer's: the desync again, one level in.
        if isinstance(node, ast.HandleExpr):
            saved_ops = self._op_result_types
            # This arm hand-enumerates the children because they are walked in
            # DIFFERENT scopes, so it cannot use the generic `fields()`
            # recursion below.  That makes it the one place a new `HandleExpr`
            # field would become silently invisible to discovery — a missed
            # generic call is a dangling clone (E602) with no diagnostic
            # pointing here — so the enumeration is checked against the
            # dataclass rather than trusted.
            enumerated = {"effect", "state", "clauses", "body"}
            declared = {f.name for f in fields(node)} - {"span"}
            if declared != enumerated:  # pragma: no cover — guard
                msg = (
                    f"HandleExpr fields changed: {sorted(declared)}; this arm "
                    f"walks {sorted(enumerated)}.  Add the new field to the "
                    f"enclosing-scope group or to the handler-scope body walk "
                    f"— an unwalked child hides every generic call inside it."
                )
                raise AssertionError(msg)
            for child in (node.effect, node.state, node.clauses):
                self._collect_calls(
                    child, generic_decls, ctor_to_adt, instances,
                )
            # MERGED over the enclosing registry, not swapped for it — and
            # deliberately, because codegen merges too (`_translate_handle_state`
            # writes `{**saved_result_vera, **effect_op_result_names(...)}`, and
            # `_translate_handle_exn` leaves the registry untouched).  A handler
            # that contributes no result type must therefore leave the enclosing
            # one answering: `pick([get(()), 4], 9)` inside an `Exn` handler
            # nested in a `State<Nat>` one names `pick$Nat` on both sides.
            # Replacing here instead names `pick$Int` against the rewrite's
            # `pick$Nat` — measured: E602, `main` dropped, #1207 exactly.  The
            # inner entry still wins for a key it DOES supply, the merge being
            # ordered.  Pinned by `exn_nested_in_state` in
            # tests/test_mono_effect_op_naming_1207.py.
            self._op_result_types = {
                **saved_ops, **effect_op_result_names([node.effect]),
            }
            try:
                self._collect_calls(
                    node.body, generic_decls, ctor_to_adt, instances,
                )
            finally:
                self._op_result_types = saved_ops
            return
        if isinstance(node, ast.Node):
            for f in fields(node):
                if f.name == "span":
                    continue
                self._collect_calls(
                    getattr(node, f.name), generic_decls, ctor_to_adt,
                    instances,
                )
        elif isinstance(node, (tuple, list)):
            for item in node:
                self._collect_calls(
                    item, generic_decls, ctor_to_adt, instances,
                )

    def _infer_type_args_from_call(
        self,
        decl: ast.FnDecl,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer concrete type variable bindings from a call's arguments.

        Returns a tuple of concrete type names, one per forall_var, or
        None if inference fails.
        """
        return self._infer_type_args_from_args(
            decl, call.args, ctor_to_adt, generic_decls,
        )

    def _infer_type_args_from_args(
        self,
        decl: ast.FnDecl,
        args: tuple[ast.Expr, ...],
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> tuple[str, ...] | None:
        """Infer concrete type variable bindings from an argument tuple.

        The arg-driven core shared by ``FnCall`` and ``ModuleCall`` (#774): a
        qualified call to an imported generic carries the same positional
        arguments, so the type-parameter inference is identical to a bare call.

        Returns a tuple of concrete type names, one per forall_var, or
        None if inference fails.
        """
        forall_vars = decl.forall_vars
        if not forall_vars:
            return None

        # Type vars carrying an ability bound (`where Eq<T>`).  For these, a
        # `ConstructorCall` argument to a direct `@T` parameter must keep its
        # type argument (`Box<String>`, not bare `Box`) so the clone name, the
        # substituted slot type in the clone body, AND the E613 gate all see the
        # concrete field type — exactly as the slot-ref call form already does
        # (#772).  Unconstrained vars stay bare: a `Box<T>` clone is a uniform
        # pointer, so keeping one `id$Box` for every instantiation avoids
        # needless clone splitting for generics whose behaviour is type-blind.
        constrained_vars = frozenset(
            c.type_var for c in (decl.forall_constraints or ())
        )

        mapping: dict[str, str] = {}
        # #898: per-constrained-forall-var accumulator of a sparse
        # multi-parameter ADT's partial per-parameter recovery, MERGED across
        # every constructor argument bound to that var.  Each entry is
        # (base_name, [name-or-None per ADT type parameter]); `MkErr(5)` fills
        # one slot, `MkOk("x")` fills the other, so the two together yield the
        # fully-determined `Res<String, Int>` the checker's cross-argument merge
        # (`merge_inferred_types`) already accepted — keeping the monomorphizer
        # in lockstep so the emitted clone matches the type-checked call.
        partial_adt: dict[str, tuple[str, list[str | None]]] = {}
        # #1327/#1366: per-var record of a DIRECT `@T` parameter whose argument
        # this walker could not name.  Collected during unification and
        # consulted only for vars that end up unbound — a var another parameter
        # DID bind (`f(@T, @T)` with one nameable argument) is inferred, so the
        # unnameable sibling is not a failure.
        unnamed_direct: dict[str, ast.Expr] = {}
        for param_te, arg in zip(decl.params, args):
            self._unify_param_arg(param_te, arg, forall_vars, ctor_to_adt,
                                  mapping, generic_decls, constrained_vars,
                                  partial_adt, unnamed_direct)
        # #1395: a SECOND pass, for the variables the first left unbound.  The
        # checker is asked only into a hole, and only once every parameter has
        # had its say, so it can never displace a binding the walkers made —
        # which is what makes consulting a semantic type safe for a naming
        # vocabulary.  Skipped when nothing is unbound, so an ordinary call
        # pays one membership test.
        if any(tv not in mapping for tv in forall_vars):
            for param_te, arg in zip(decl.params, args):
                self._unify_param_arg(param_te, arg, forall_vars, ctor_to_adt,
                                      mapping, generic_decls, constrained_vars,
                                      partial_adt, unnamed_direct,
                                      consult_checker=True)

        # Materialise any merged sparse-ADT recovery.
        #
        # * Fully determined (every parameter now known across all arguments):
        #   promote the bare name to the full parameterised name so the E613
        #   gate and clone body see the concrete field types, and the emitted
        #   clone matches the type-checked call.
        # * Partially determined (a genuinely free parameter remains — the
        #   single-argument `id1(MkErr(5))` shape): materialise a name that
        #   still carries the RECOVERED components, with each free slot marked
        #   by the reserved `?` sentinel (`Res<?, Int>`).  This never names an
        #   emitted clone (the instance is always rejected by the ability gate),
        #   but it lets the gate distinguish an under-determined type whose
        #   known components ARE Eq (→ clearer E619, annotate the free param)
        #   from one whose known component is already non-Eq (→ accurate E613,
        #   annotation cannot help) — #898 diagnostic-accuracy fix.
        for tv, (base_name, slots) in partial_adt.items():
            if all(s is not None for s in slots):
                resolved = [s for s in slots if s is not None]
                mapping[tv] = f"{base_name}<{', '.join(resolved)}>"
            elif tv in constrained_vars:
                rendered = [s if s is not None else _FREE_TYPE_PARAM
                            for s in slots]
                mapping[tv] = f"{base_name}<{', '.join(rendered)}>"

        # Check all type vars are resolved; default unresolved phantom vars to
        # Bool (NOT Unit — see the rationale just below: Bool has an i32 repr)
        result = []
        for tv in forall_vars:
            if tv not in mapping:
                # #1327/#1366 — FAIL CLOSED before defaulting.  A var a DIRECT
                # `@T` parameter binds is determined by that argument's type;
                # arriving here means the walker could not name the argument,
                # so `Bool` would be a guess, not a phantom.  Record it: the
                # consumer reports [E622] rather than emitting a module (or a
                # tier) that rests on the guess.  Behaviour is otherwise
                # unchanged — the default is still applied, so the caller's
                # shape and every downstream table stay exactly as before and
                # the record is the only new signal.
                unnamed_arg = unnamed_direct.get(tv)
                if unnamed_arg is not None:
                    self._record_uninferred_type_arg(
                        decl.name, tv, unnamed_arg)
                # Phantom type variable (e.g. E in result_unwrap_or(Ok(x), d))
                # — the generated WASM is identical regardless of this type.
                # Use Bool (i32) rather than Unit (no WASM repr) so the
                # monomorphized body can still compile unused branches.
                mapping[tv] = "Bool"
            result.append(mapping[tv])
        return tuple(result)

    def _record_uninferred_type_arg(
        self, fn_name: str, type_var: str, arg: ast.Expr,
    ) -> None:
        """Record an un-inferable DIRECT type argument (#1327/#1366, [E622]).

        Deduplicated on ``(fn_name, type_var, span)``: discovery re-walks the
        same call site once per worklist re-seed round, and one call site is
        one diagnostic.
        """
        span = getattr(arg, "span", None)
        key = (
            fn_name,
            type_var,
            (span.line, span.column, span.end_line, span.end_column)
            if span is not None else None,
        )
        if key in self._uninferred_seen:
            return
        self._uninferred_seen.add(key)
        self.uninferred_type_args.append(UninferredTypeArg(
            fn_name=fn_name,
            type_var=type_var,
            arg_kind=type(arg).__name__,
            arg=arg,
            origin=self._namespace_path,
        ))

    def _unify_param_arg(
        self,
        param_te: ast.TypeExpr,
        arg: ast.Expr,
        forall_vars: tuple[str, ...],
        ctor_to_adt: dict[str, str],
        mapping: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
        constrained_vars: frozenset[str] = frozenset(),
        partial_adt: dict[str, tuple[str, list[str | None]]] | None = None,
        unnamed_direct: dict[str, ast.Expr] | None = None,
        consult_checker: bool = False,
    ) -> None:
        """Unify a parameter TypeExpr against an argument to bind type vars.

        ``unnamed_direct`` (#1327/#1366) collects, per type variable, the
        argument of a DIRECT ``@T`` parameter this walker could not name — the
        evidence [E622] is raised on.  Optional so a caller that only wants the
        binding (no fail-closed reporting) is unaffected.
        """
        if isinstance(param_te, ast.RefinementType):
            self._unify_param_arg(
                param_te.base_type, arg, forall_vars, ctor_to_adt, mapping,
                generic_decls, constrained_vars, partial_adt, unnamed_direct,
                consult_checker,
            )
            return

        if not isinstance(param_te, ast.NamedType):
            return

        if param_te.name in forall_vars:
            # Direct type variable — infer from argument
            vera_type = self._infer_vera_type_name(
                arg, ctor_to_adt, generic_decls)
            if (param_te.name in constrained_vars
                    and isinstance(arg, ast.ConstructorCall)):
                # `_infer_vera_type_name` drops the type argument for a
                # `ConstructorCall` (returns bare `Box`).  For a CONSTRAINED
                # var the type argument is load-bearing (the ability check and
                # the clone body's structural `==` both need it), so recover the
                # parameterized name via `_get_arg_type_info` — the same routine
                # the `Option<T>` parameterized path uses (#772).
                info = self._get_arg_type_info(arg, ctor_to_adt)
                if info is not None:
                    base_name, arg_names = info
                    if arg_names and all(a is not None for a in arg_names):
                        resolved = [a for a in arg_names if a is not None]
                        vera_type = f"{base_name}<{', '.join(resolved)}>"
                    elif arg_names and partial_adt is not None:
                        # #898: PARTIAL recovery — this constructor pins only
                        # some of the ADT's type parameters (`MkErr(5)` fills
                        # `B`, not `A`).  Accumulate the per-slot info under this
                        # forall var, MERGING with any sibling argument's
                        # recovery (`MkOk("x")` fills `A`), so the fully-
                        # determined `Res<String, Int>` is materialised after
                        # every argument is seen.  A later slot overwrites None,
                        # never a concrete name (siblings agree on shared slots
                        # because the checker already accepted the call — a
                        # genuine conflict is an E205 there, never reaching mono).
                        prev = partial_adt.get(param_te.name)
                        if prev is None or prev[0] != base_name:
                            slots: list[str | None] = list(arg_names)
                            partial_adt[param_te.name] = (base_name, slots)
                        else:
                            slots = prev[1]
                            for i, name in enumerate(arg_names):
                                if name is not None and i < len(slots):
                                    slots[i] = name
            if vera_type and param_te.name not in mapping:
                mapping[param_te.name] = vera_type
            elif not vera_type and unnamed_direct is not None:
                # #1327/#1366: the parameter IS the type variable, so this
                # argument's type is the instantiation — and no arm named it.
                # Remember the argument (first one wins, matching the
                # first-binding-wins rule above) so the result loop can tell a
                # genuine phantom from a walker gap.  Recorded even when
                # `partial_adt` recovery ran: that path only fills a
                # CONSTRAINED var's parameterized name, and leaves `vera_type`
                # falsy exactly when nothing was recovered.
                unnamed_direct.setdefault(param_te.name, arg)
            return

        # Parameterized type like Option<T> — match type args
        if param_te.type_args:
            # Handle type alias for FnType matched against a callable
            # arg — either an AnonFn literal or a SlotRef whose static
            # type is itself an FnType alias.  #604: pre-fix, only the
            # AnonFn branch fired; SlotRef-typed-as-FnType-alias args
            # like ``@Doubler.0`` skipped this branch and left the
            # ``B`` type var unbound, hitting the ``"Bool"`` phantom-
            # var default at result-building time and producing wrong
            # mono suffixes.  The helper now resolves either shape.
            alias_concrete = self._infer_fn_alias_type_args(
                param_te, arg,
            )
            if alias_concrete is not None:
                for param_ta, concrete_name in zip(
                    param_te.type_args, alias_concrete,
                ):
                    self._unify_type_arg_pair(
                        param_ta, concrete_name, forall_vars, mapping,
                    )
                return

            arg_info = self._get_arg_type_info(arg, ctor_to_adt)
            if arg_info is None and consult_checker:
                # #1395: a variable reached only through this parameter's
                # TYPE ARGUMENTS is bound here rather than by the type
                # namer, and this helper carries the same missing arms the
                # namers did — none for an indexed argument, none for a
                # nested module call — so the variable stayed unbound and
                # the phantom default named the clone.  A
                # `fn head(@Array<T> -> @T)` then returned i32 where `Int`
                # needs i64: check-green, verify-clean, invalid WASM.
                #
                # Consulted ONLY into a hole, and only after every
                # parameter has bound what it can — see
                # `checker_arg_type_info`.  The checker's answer is a
                # semantic type and the walkers' is a naming vocabulary, so
                # asking earlier lets `Option<Nat>` displace the `Int` a
                # later parameter's literal supplies.
                arg_info = checker_arg_type_info(self.ctx.expr_types, arg)
            if arg_info and arg_info[0] == param_te.name:
                for param_ta, arg_ta_name in zip(
                    param_te.type_args, arg_info[1]
                ):
                    # arg_ta_name is None for unknown type-param positions
                    # (e.g. T in Err(e) where only E can be inferred from Err).
                    if arg_ta_name is not None:
                        self._unify_type_arg_pair(
                            param_ta, arg_ta_name, forall_vars, mapping,
                        )

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

    def _infer_vera_type_name(
        self,
        expr: ast.Expr,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> str | None:
        """The simple Vera type name of an expression, from one source.

        This walker first, the CHECKER second — the precedence and its
        rationale are stated once, on :func:`checker_clone_type_name`.  The
        WASM call-rewrite twin (``InferenceMixin._infer_vera_type``) asks the
        same two sources in the same order over the same table, so a shape
        either walker cannot name is now named identically for both instead of
        becoming a clone only one of them believes in.
        """
        walked = self._walk_vera_type_name(expr, ctor_to_adt, generic_decls)
        if walked is not None:
            return walked
        return checker_clone_type_name(self.ctx.expr_types, expr)

    def _walk_vera_type_name(
        self,
        expr: ast.Expr,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl] | None = None,
    ) -> str | None:
        """Infer the simple Vera type name of an expression, syntactically."""
        if isinstance(expr, ast.IntLit):
            return "Int"
        if isinstance(expr, ast.BoolLit):
            return "Bool"
        if isinstance(expr, ast.FloatLit):
            return "Float64"
        if isinstance(expr, ast.UnitLit):
            return "Unit"
        if isinstance(expr, (ast.SlotRef, ast.ResultRef)):
            # #1369: a `ResultRef` shares this arm.  `@T.result` carries the
            # same declared @Type shape as a slot reference (`type_name` plus
            # optional `type_args`, no index), and the WASM call-rewrite twin
            # has read it that way since #912 — but discovery had no arm for
            # it at all, so a generic called from an `ensures` with
            # `@Int.result` left its type variable unbound and fell to the
            # phantom-var default: `gok$Bool` registered against the rewrite's
            # `gok$Int`.  A helper reached ONLY through the postcondition
            # therefore dangled and dropped its caller (E602 → E620) on
            # check-green, verify-green source; one also called from
            # `requires` with a slot reference survived by coincidence,
            # emitting a wasted `$Bool` clone beside the `$Int` one the call
            # actually needed.  Arm-for-arm parity with the twin is the
            # contract this family lives by (#1286), so the two now answer
            # identically here as well.
            if expr.type_args:
                # Include type args for parameterized types like Map<String, Int>
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(self._format_type_name(ta))
                    else:
                        return expr.type_name
                return f"{expr.type_name}<{', '.join(arg_names)}>"
            return expr.type_name
        if isinstance(expr, ast.ConstructorCall):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.NullaryConstructor):
            return ctor_to_adt.get(expr.name)
        if isinstance(expr, ast.BinaryExpr):
            if expr.op in (ast.BinOp.EQ, ast.BinOp.NEQ, ast.BinOp.LT,
                           ast.BinOp.GT, ast.BinOp.LE, ast.BinOp.GE,
                           ast.BinOp.AND, ast.BinOp.OR, ast.BinOp.IMPLIES):
                return "Bool"
            piped = pipe_desugared_call(expr)
            if piped is not None:
                # #1365: a PIPE's value is the RIGHT-hand call's RESULT, not
                # the piped-in value.  Naming it from the left operand is
                # right only where the stage preserves the type, and silently
                # wrong the moment one does not: `@Int.0 |> to_b() |> gid()`
                # instantiated `gid` at `Int` and called it with the `Bool`
                # `to_b` produced, so the module failed WASM validation at
                # load from check-green, verify-clean source.  Name the
                # desugared call instead — the same `(lhs, *rhs.args)` shape
                # the checker's `_check_pipe`, codegen's `_translate_binary`
                # and discovery's own #913 instantiation arm all build — so a
                # chain types stage by stage.  The twin
                # (`InferenceMixin._infer_vera_type`) carries the identical
                # arm: the two must land on the same name or the discovered
                # clone dangles at the call the rewrite emits.
                return self._infer_vera_type_name(
                    piped, ctor_to_adt, generic_decls)
            return self._infer_vera_type_name(
                expr.left, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.UnaryExpr):
            if expr.op == ast.UnaryOp.NOT:
                return "Bool"
            return self._infer_vera_type_name(
                expr.operand, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.IfExpr):
            # #1286: the first branch that yields a name, mirroring the
            # WASM call-rewrite twin (`InferenceMixin._infer_vera_type`,
            # vera/wasm/inference.py) arm for arm.  The two consultors must
            # land on the SAME name or the discovered clone dangles at the
            # call the rewrite emits (E602) — so the join lands on both
            # sides together, exactly as the #1276 WAT deciders did.
            then_vt = self._infer_vera_type_name(
                expr.then_branch.expr, ctor_to_adt, generic_decls)
            if then_vt is not None:
                return then_vt
            return self._infer_vera_type_name(
                expr.else_branch.expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.Block):
            # #1286 (PR review): a `Block` names its TRAILING expression's
            # type, exactly as the rewrite twin's `Block` arm does.  This is
            # not a defensive add — the transformer leaves a braced match arm
            # body AS a `Block` (`Some(@Int) -> { let @Int = …; @Int.0 }`),
            # and a braced `if` branch whose tail is itself braced likewise.
            # Without the arm, discovery answered `None` for every
            # block-bodied arm while the rewrite — which HAS the arm — named
            # the concrete clone: `idg$Int` emitted at the call and never
            # registered, so a check-green `main` was dropped (E602).  Same
            # divergence the `MatchExpr` arm below closes, one shape over.
            return self._infer_vera_type_name(
                expr.expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.MatchExpr):
            # #1286: discovery had NO `MatchExpr` arm at all, so a `match`
            # argument answered `None` and the instantiation fell to the
            # phantom-var default while the rewrite named it from arm 0 —
            # a dangling `idg$Int` that dropped the caller (E602) on
            # check-green source, even with every arm completing.  The join
            # closes the gap and the desync in one arm.
            for arm in expr.arms:
                arm_vt = self._infer_vera_type_name(
                    arm.body, ctor_to_adt, generic_decls)
                if arm_vt is not None:
                    return arm_vt
            return None
        if isinstance(expr, ast.HandleExpr):
            # #1286 (PR review sweep): the third shape of the one gap — a
            # `handle` in argument position is named from its body's trailing
            # expression by the rewrite twin and by nothing here, so it
            # dangled exactly like the block-bodied arm above.  Measured, not
            # inferred: `idg(handle[Exn<Bool>] { … } in { 42 })` is
            # check-green and drops `main` at E602 without this arm.
            return self._infer_vera_type_name(
                expr.body.expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.StringLit):
            return "String"
        if isinstance(expr, ast.InterpolatedString):
            return "String"
        if isinstance(expr, ast.ArrayLit):
            return "Array"
        # #1207: an effect operation in a value position is not in any fn
        # table, so it has to be answered from the op registry in scope —
        # the same table (`vera.slots.effect_op_result_names`) the WASM
        # call-rewrite consults at `_infer_vera_type`'s matching arm.  Before
        # this, a `get(())` fixing a generic's type variable fell through to
        # `fn_ret_types` / the builtin table, missed both, and left the
        # instantiation to the phantom default while the rewrite named the
        # cell's type: the clone discovery emitted dangled at the call the
        # rewrite emitted (loud E602, caller dropped with E620).
        # #1284: and only when this call site IS the operation.  The registry
        # is populated unfiltered — it records what each op name results in,
        # which is a fact about the row and the handler, not about the
        # program's declarations — so the shadow question is asked here, at
        # the site, exactly as codegen's `_infer_vera_type` asks it through
        # `_bare_call_denotes_op`.  Filtering at the two installation sites
        # instead is what desynced them: the declared-row install filtered and
        # the handler-expression merge did not, so a user `fn get` called
        # under a `handle[State<T>]` named the CELL's clone here and the
        # user function's return type there.
        # #1299: over the LEXICAL scope the walk is in, not the flat table.
        # An imported module's `private fn get` is in `ctx.fn_names` — the
        # guard rail needs its symbol — and claimed this call site, so
        # discovery named a clone from that declaration's return type
        # (`idg$Bool`) while the WASM rewrite named one from the cell's
        # (`idg$Int`): check-green source that failed to load.
        if (isinstance(expr, ast.FnCall)
                and not self._bare_call_is_user_fn(expr.name)
                and expr.name in self._op_result_types):
            return self._op_result_types[expr.name]
        if isinstance(expr, ast.FnCall) and generic_decls:
            return self._infer_fncall_vera_type(
                expr, ctor_to_adt, generic_decls)
        if isinstance(expr, ast.FnCall):
            return self._infer_fncall_vera_type_simple(expr)
        return None

    def _infer_fncall_vera_type(
        self,
        call: ast.FnCall,
        ctor_to_adt: dict[str, str],
        generic_decls: dict[str, ast.FnDecl],
    ) -> str | None:
        """Infer the Vera return type of a function call.

        For generic calls, infers type variable bindings from arguments,
        then substitutes into the return TypeExpr.
        """
        # #769 logic-arm parity with the WASM call-rewrite chain
        # (InferenceMixin._infer_fncall_vera_type, vera/wasm/inference.py):
        # apply_fn / async / await need call-shape context no fixed table can
        # hold, so each side carries the same arm — a name inferred here must
        # equal the rewrite's, or the discovered clone dangles and the caller
        # is skipped (E602).  These names cannot be user-redefined (E151), so
        # the arms fire only for the real builtins.
        if call.name == "apply_fn" and call.args:
            ret_te: ast.TypeExpr | None = self._closure_arg_return_te(
                call.args[0])
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if isinstance(ret_te, ast.NamedType):
                return self._format_type_name(ret_te)
        if call.name == "async" and call.args:
            inner = self._infer_vera_type_name(
                call.args[0], ctor_to_adt, generic_decls)
            return f"Future<{inner}>" if inner else "Future"
        if call.name == "await" and call.args:
            inner = self._infer_vera_type_name(
                call.args[0], ctor_to_adt, generic_decls)
            if inner and inner.startswith("Future<") and inner.endswith(">"):
                return inner[7:-1]
            return inner
        if call.name in generic_decls:
            decl = generic_decls[call.name]
            type_args = self._infer_type_args_from_call(
                decl, call, ctor_to_adt, generic_decls,
            )
            if type_args and decl.forall_vars:
                mapping = dict(zip(decl.forall_vars, type_args))
                ret_te = decl.return_type
                # Unwrap an inline refinement to its base, mirroring the
                # rewrite side's generic branch (vera/wasm/inference.py) —
                # the two consultors must land on the same name (PR #972
                # review; both previously agreed via the WAT collapse only
                # by coincidence for refined returns).
                if isinstance(ret_te, ast.RefinementType):
                    ret_te = ret_te.base_type
                if isinstance(ret_te, ast.NamedType):
                    return mapping.get(ret_te.name, ret_te.name)
        return self._infer_fncall_vera_type_simple(call)

    def _closure_arg_return_te(self, arg: ast.Expr) -> ast.TypeExpr | None:
        """Declared return TypeExpr of a callable argument (#769).

        The discovery-side mirror of the rewrite chain's
        ``_closure_arg_return_type`` dispatch: an inline ``AnonFn`` yields its
        declared return type; a ``SlotRef`` typed as an ``FnType`` alias
        resolves TRANSITIVELY through the shared ``resolve_fn_type_alias``
        (#867) to the terminal ``FnType``'s return type.
        """
        if isinstance(arg, ast.AnonFn):
            return arg.return_type
        if isinstance(arg, ast.SlotRef):
            fn_te = resolve_fn_type_alias(
                ast.NamedType(name=arg.type_name, type_args=arg.type_args),
                self.ctx.type_aliases,
                self.ctx.type_alias_params,
            )
            if fn_te is not None:
                return fn_te.return_type
        return None

    def _infer_fncall_vera_type_simple(self, call: ast.FnCall) -> str | None:
        """Infer Vera return type from registered function signatures.

        Builtin handle types (Decimal, Map, Set, …) are resolved from the
        static table first; everything else comes from ``ctx.fn_ret_types``,
        which each consumer pre-populates (codegen from its WAT signatures,
        the verifier from declared AST return types).
        """
        # A name registered in fn_ret_types is a REAL declaration in this
        # program — a user fn, or a user OVERRIDE of an E151-exempt prelude
        # combinator (#815: option_map, the json_* family, html_attr) — and
        # its declared type wins over the builtin table (the #908 show/hash
        # gate, generalised; adversarial panel, PR #972).  Opaque builtins
        # (string_chars, decimal_*, …) are never registered there, so they
        # fall through to the table as before.
        declared = self.ctx.fn_ret_types.get(call.name)
        if declared is not None:
            return declared
        return _BUILTIN_VERA_RETURN_TYPES.get(call.name)

    @staticmethod
    def _parse_type_name(name: str) -> ast.NamedType:
        """Parse a full type name string into a NamedType AST node.

        E.g. "Map<String, Int>" → NamedType("Map", (NamedType("String"),
        NamedType("Int"))).  Handles nested types like
        "Map<String, Array<Int>>".
        """
        if "<" not in name:
            return ast.NamedType(name=name, type_args=None)
        base = name[:name.index("<")]
        inner = name[name.index("<") + 1:-1]  # strip outer < >
        # Split at top-level commas (respecting nesting)
        args: list[str] = []
        depth = 0
        current: list[str] = []
        for ch in inner:
            if ch == "<":
                depth += 1
                current.append(ch)
            elif ch == ">":
                depth -= 1
                current.append(ch)
            elif ch == "," and depth == 0:
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

    def _get_arg_type_info(
        self, expr: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> tuple[str, tuple[str | None, ...]] | None:
        """Get (type_name, type_arg_names) for an argument expression.

        Used to match parameterized types like Option<T> against
        concrete arguments like @Option<Int>.0.  Type arg entries may be
        None for positions that cannot be inferred from the argument (e.g.
        T in Err(e) where only E is resolved from Err).
        """
        if isinstance(expr, ast.SlotRef):
            if expr.type_args:
                arg_names = []
                for ta in expr.type_args:
                    if isinstance(ta, ast.NamedType):
                        arg_names.append(self._format_type_name(ta))
                    else:
                        return None
                return (expr.type_name, tuple(arg_names))
            return (expr.type_name, ())
        if isinstance(expr, ast.ConstructorCall):
            adt_name = ctor_to_adt.get(expr.name)
            if adt_name:
                # Use the per-field ADT type-param index mapping when available.
                # This correctly handles sparse constructors like Err(e) whose
                # single field maps to Result's *second* type param (E, index 1),
                # not the first (T, index 0) as naïve positional zipping implies.
                field_tp_idx = self.ctx.ctor_tp_indices.get(expr.name)
                adt_tp_count = self.ctx.adt_tp_counts.get(adt_name, 0)
                if field_tp_idx is not None and adt_tp_count > 0:
                    result_tps: list[str | None] = [None] * adt_tp_count
                    for field_i, tp_idx in enumerate(field_tp_idx):
                        if tp_idx is not None and field_i < len(expr.args):
                            t = self._infer_vera_type_name(
                                expr.args[field_i], ctor_to_adt)
                            if t is not None:
                                result_tps[tp_idx] = t
                            # If t is None, leave position as None (unknown)
                    return (adt_name, tuple(result_tps))
                # Fall back to positional inference for constructors without
                # mapping info (e.g. user-defined ADTs not yet registered).
                arg_types = []
                for a in expr.args:
                    t = self._infer_vera_type_name(a, ctor_to_adt)
                    if t:
                        arg_types.append(t)
                    else:
                        return None
                return (adt_name, tuple(arg_types))
        if isinstance(expr, ast.ArrayLit):
            # Infer the element type from the first element — FULL-DEPTH when
            # the element itself carries type-arg info (a nested literal or a
            # constructor call), so ``Array<Array<E>>`` binds ``E`` from
            # ``[[1, 2]]`` and ``Array<Option<T>>`` binds ``T`` from
            # ``[Some(1)]`` via the recursive unifier (#769 gap 2).  The WASM
            # twin's ArrayLit branch (vera/wasm/inference.py) mirrors this
            # exactly — element-name granularity is part of the clone-name
            # agreement contract (#772), so the two sides must move together.
            if expr.elements:
                elem_type = self._array_elem_type_name(
                    expr.elements[0], ctor_to_adt,
                )
                if elem_type:
                    return ("Array", (elem_type,))
            return ("Array", ())
        if isinstance(expr, ast.FnCall):
            # Builtins returning parameterized types (e.g. decimal_div →
            # Option<Decimal>).  Gated on non-registration: a name in
            # fn_ret_types is a real decl — possibly a user override of an
            # E151-exempt prelude combinator (#815) — whose DECLARED return
            # must win (it resolves via fn_ret_type_exprs below; adversarial
            # panel, PR #972).
            if expr.name not in self.ctx.fn_ret_types:
                param_ret = _BUILTIN_PARAMETERIZED_RETURNS.get(expr.name)
                if param_ret is not None:
                    return param_ret
            if expr.name in ("array_concat", "array_append",
                             "array_slice", "array_filter"):
                if expr.args:
                    return self._get_arg_type_info(expr.args[0], ctor_to_adt)
            # #899 issue 1: a NON-generic user fn returning a parameterized type
            # (`maybe → Option<Decimal>`) in `Option<T>` position must expose its
            # type args so `T` binds from THIS argument.  Mirrors the WASM
            # call-rewrite `_get_arg_type_info_wasm` FnCall branch
            # (vera/wasm/inference.py) so discovery and call-rewrite pick the
            # same clone — else discovery emits `first_opt$Bool` while the call
            # site references `first_opt$Decimal`, a dangling reference (E602).
            # GENERIC calls are excluded: their declared return is over the
            # callee's OWN type vars, not concrete types, so their type args
            # would bind a phantom var — they fall through to the generic-return
            # resolution instead (same exclusion the call-rewrite side applies).
            if expr.name in (self.ctx.generic_decls or {}):
                return None
            ret_te = self.ctx.fn_ret_type_exprs.get(expr.name)
            if isinstance(ret_te, ast.RefinementType):
                ret_te = ret_te.base_type
            if isinstance(ret_te, ast.NamedType) and ret_te.type_args:
                ta_names: list[str | None] = []
                for ta in ret_te.type_args:
                    if isinstance(ta, ast.NamedType) and not ta.type_args:
                        ta_names.append(self._format_type_name(ta))
                    else:
                        ta_names.append(None)
                return (ret_te.name, tuple(ta_names))
        return None

    def _array_elem_type_name(
        self, elem: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> str | None:
        """FULL-DEPTH type name of an array-literal element (#769 gap 2).

        Prefers the parameterized recovery (``Some(1)`` → ``"Option<Int>"``,
        ``[1, 2]`` → ``"Array<Int>"``) when every type-arg position is known;
        falls back to the simple name (``"Int"``, ``"String"``) otherwise —
        the pre-#769 behavior, so under-determined elements degrade rather
        than mis-bind.
        """
        info = self._get_arg_type_info(elem, ctor_to_adt)
        if info is not None:
            outer, args = info
            if args and all(a is not None for a in args):
                return f"{outer}<{', '.join(a for a in args if a is not None)}>"
        return self._infer_vera_type_name(elem, ctor_to_adt)

    def full_arg_type_name(
        self, expr: ast.Expr, ctor_to_adt: dict[str, str],
    ) -> str | None:
        """Fully-qualified Vera type name of an argument expression (#932).

        The DERIVABILITY-decision counterpart of the one-level names
        :meth:`_get_arg_type_info` / :meth:`_infer_vera_type_name` recover.
        Recurses through nested ``ConstructorCall`` fields so every level's type
        argument is reconstructed: a `Cons(Cons(1, Nil), Nil)` operand yields the
        FULLY-qualified ``List<List<Int>>`` rather than the one-level
        ``List<List>`` the flat recovery produces (the residue that the
        codegen-side Eq-derivability gate then treats as a lost-type-arg clone
        and spuriously E613s).

        This is the mono-side mirror of ``OperatorsMixin._full_ctor_type_name``
        (vera/wasm/operators.py, #923's DIRECT-``==`` recovery).  It is consumed
        ONLY for the Eq-derivability decision (`_check_constraints`) — the
        mangled CLONE NAME codegen emits and looks up stays the truncated
        one-level name (`eq2$List<List>`) that `_get_arg_type_info` produces, so
        the clone-mangling contract `_unify_param_arg` relies on is unchanged
        (the #772 hard constraint).

        Falls back to the bare :meth:`_infer_vera_type_name` for a
        non-``ConstructorCall`` operand (a nested `[1]` bottoms out at the bare
        `Array`, a nullary `Nil` at the bare `List`).  Returns ``None`` only when
        the base ADT name itself cannot be resolved; a field whose type argument
        cannot be inferred leaves that position bare, matching the lost-type-arg
        shape the derivability gate already handles.
        """
        if not isinstance(expr, ast.ConstructorCall):
            return self._infer_vera_type_name(expr, ctor_to_adt)
        base = ctor_to_adt.get(expr.name)
        if base is None:
            return None
        tp_indices = self.ctx.ctor_tp_indices.get(expr.name)
        tp_count = self.ctx.adt_tp_counts.get(base, 0)
        if not tp_indices or tp_count == 0:
            return base
        slots: list[str | None] = [None] * tp_count
        for field_i, tp_idx in enumerate(tp_indices):
            if tp_idx is not None and field_i < len(expr.args):
                slots[tp_idx] = self.full_arg_type_name(
                    expr.args[field_i], ctor_to_adt,
                )
        if all(s is not None for s in slots):
            return f"{base}<{', '.join(s for s in slots if s is not None)}>"
        return base

    def _resolve_arg_fn_shape(
        self,
        arg: ast.Expr,
    ) -> tuple[tuple[ast.TypeExpr, ...], ast.TypeExpr] | None:
        """Return ``(param_types, return_type)`` for an arg that's callable.

        Two arg shapes resolve:

        * ``AnonFn`` literal — its declared params + return type.
        * ``SlotRef`` whose static type is an FnType alias (e.g.
          ``@Doubler.0`` where ``type Doubler = fn(Int -> Int)``) —
          the alias's resolved params + return type.  For a
          *parameterised* alias like
          ``type Mapper<T> = fn(T -> T) effects(pure)``, the
          ``SlotRef``'s type-args are substituted into the alias body
          first so ``@Mapper<Int>.0`` returns
          ``(NamedType("Int"),), NamedType("Int")`` rather than the
          unsubstituted ``T``.  Without substitution, the downstream
          ``_infer_fn_alias_type_args`` matcher would bind alias-local
          names instead of concrete ones, producing mono suffixes
          like ``option_map$T_JT`` rather than ``option_map$Int_JInt``
          (CR-4 on PR #659).

        Returns ``None`` for any other arg shape.  Used by
        :meth:`_infer_fn_alias_type_args` to bind generic type variables
        from a closure-shaped argument uniformly across both forms.

        Fixes #604: pre-fix, only the AnonFn form was resolved.  When a
        prelude generic like ``option_map<VeraA, VeraB>(@Option<VeraA>,
        @VeraOptionMapFn<VeraA, VeraB>)`` was called with a ``SlotRef``
        typed as an FnType alias instead
        of an inline ``AnonFn``, ``B`` failed to bind and defaulted to
        ``Bool`` (the phantom-var fallback in :meth:`_infer_type_args_from_call`),
        producing the wrong mono suffix (``option_map$Int_JBool``) and
        an ``indirect call type mismatch`` trap at runtime.
        """
        if isinstance(arg, ast.AnonFn):
            return (tuple(arg.params), arg.return_type)
        if isinstance(arg, ast.SlotRef):
            # Resolved transitively through the alias chain via the
            # shared resolver (#867 / PR #880 review — the single-hop
            # lookup here made a two-hop-alias-typed closure slot fail
            # shape resolution, so a closure-bound type param fell to
            # the phantom-var default: wrong mono suffix, WASM trap).
            # The resolver substitutes the SlotRef's type_args into a
            # parameterised alias's body per hop (CR-5 on PR #659);
            # arity-mismatch on parameterised aliases is rejected
            # upstream by the type checker ([E133], #660).
            fn_type = resolve_fn_type_alias(
                ast.NamedType(name=arg.type_name, type_args=arg.type_args),
                self.ctx.type_aliases,
                self.ctx.type_alias_params,
            )
            if fn_type is not None:
                return (tuple(fn_type.params), fn_type.return_type)
        return None

    def _infer_fn_alias_type_args(
        self,
        param_te: ast.NamedType,
        arg: ast.Expr,
    ) -> tuple[str, ...] | None:
        """Infer concrete types for a type alias's params from a callable arg.

        When ``param_te`` is e.g. ``NamedType("MapFn", [A, B])``
        which aliases ``fn(A -> B)``, and the argument is callable (an
        ``AnonFn`` literal or a ``SlotRef`` typed as an FnType alias)
        with concrete param/return types, infer one concrete type name
        per alias type parameter.

        Returns a tuple of concrete type names aligned to the alias's
        type parameters, or ``None`` if inference fails.
        """
        arg_shape = self._resolve_arg_fn_shape(arg)
        if arg_shape is None:
            return None
        arg_params, arg_return = arg_shape

        type_aliases = self.ctx.type_aliases
        type_alias_params = self.ctx.type_alias_params

        alias_params = type_alias_params.get(param_te.name)
        if (
            not alias_params
            or not param_te.type_args
            or len(alias_params) != len(param_te.type_args)
        ):
            return None

        # Resolve the param alias's body transitively (#867 / PR #880
        # review): the HOF's declared fn param may itself be an alias
        # chain (`type MapFn2<X, Y> = MapFn<X, Y>;`).  Resolving the
        # chain instantiated at the alias's *own* param names keeps the
        # terminal FnType body expressed in `alias_params` names —
        # including across renaming hops — so the positional matching
        # below is untouched.
        alias_te = resolve_fn_type_alias(
            ast.NamedType(
                name=param_te.name,
                type_args=tuple(
                    ast.NamedType(name=p, type_args=None)
                    for p in alias_params
                ),
            ),
            type_aliases,
            type_alias_params,
        )
        if alias_te is None:
            return None

        # Match the FnType body against the arg's shape to build an
        # alias-local mapping:  alias_param_name -> concrete_type_name
        alias_mapping: dict[str, str] = {}

        # Match parameter types positionally
        for fn_param_te, arg_param_te in zip(
            alias_te.params, arg_params,
        ):
            if (
                isinstance(fn_param_te, ast.NamedType)
                and fn_param_te.name in alias_params
                and isinstance(arg_param_te, ast.NamedType)
            ):
                alias_mapping[fn_param_te.name] = arg_param_te.name

        # Match return type
        ret = alias_te.return_type
        if isinstance(ret, ast.NamedType) and ret.name in alias_params:
            if isinstance(arg_return, ast.NamedType):
                alias_mapping[ret.name] = arg_return.name
            elif isinstance(arg_return, ast.FnType):
                # Return type is itself a FnType — map to "Fn"
                alias_mapping[ret.name] = "Fn"
        # Handle ADT return types like Option<B> where B is an alias param
        if isinstance(ret, ast.NamedType) and ret.type_args:
            for ret_ta in ret.type_args:
                if (
                    isinstance(ret_ta, ast.NamedType)
                    and ret_ta.name in alias_params
                    and isinstance(arg_return, ast.NamedType)
                ):
                    # For Option<B> matched against Option<Int>, extract
                    # B from the arg's return type args
                    if arg_return.type_args:
                        idx = [
                            i for i, rta in enumerate(ret.type_args)
                            if (isinstance(rta, ast.NamedType)
                                and rta.name == ret_ta.name)
                        ]
                        if idx:
                            pos = idx[0]
                            if pos < len(arg_return.type_args):
                                art = arg_return.type_args[pos]
                                if isinstance(art, ast.NamedType):
                                    alias_mapping[ret_ta.name] = art.name

        # Produce result in alias param order
        result: list[str] = []
        for ap in alias_params:
            if ap not in alias_mapping:
                return None
            result.append(alias_mapping[ap])
        return tuple(result)

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
        env = self.ctx.alias_env if alias_env is None else alias_env
        mapping = dict(zip(decl.forall_vars, concrete_types))
        mangled = self._mangle_fn_name(decl.name, concrete_types)

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

        def push(te: ast.TypeExpr) -> None:
            stack.append((
                naming.slot_name_or_none(te, scope),
                self._substituted_slot_name(te, mapping, post_scope),
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
                # with the env unchanged; _walk_free_vars likewise), so the
                # walker must not count one — a phantom binding shifts every
                # same-named ref in the body to a dangling or wrong local
                # (adversarial panel, PR #972).  The checker agrees since
                # #973: it binds no body-scope state either, rejecting such
                # refs with E130.  Clause scopes above keep params + state:
                # that is what _walk_free_vars counts (and Exn clause
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
            nonlocal scope, post_scope
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
                saved = (scope, post_scope)
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
                try:
                    walk_fn_scope(nested)
                finally:
                    scope, post_scope = saved

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
                # NamedType with type_args
                return self._parse_type_name(mapped)
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
