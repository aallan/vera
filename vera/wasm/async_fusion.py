"""Shared fusion predicates for the concurrent ``<Async>`` lowering (#841).

``async(e)`` lowers one of two ways:

* **Fused** — ``e`` is a direct ``Http.get``/``Http.post`` call whose
  argument expressions are call-free.  The whole ``async(Http.get(url))``
  becomes a single ``vera.async_http_get`` host import that submits the
  request to a host worker thread and returns a ``Future`` as a
  #578-tagged handle wrapper (kind 4).
* **Eager** — everything else keeps the identity lowering (the checker's
  W002 warning documents the eager cases whose effect row is not
  commutative).

The call-free restriction keeps codegen strictly narrower than the
checker's W002 whitelist: any expression W002 warns about contains an
effectful call, so a warned ``async`` can never be fused — the warning
"evaluates eagerly" is never false.

Import emission is decided twice — by the ``_scan_io_ops`` pre-scan in
``vera/codegen/compilability.py`` and by the ``WasmContext`` translation
in ``vera/wasm/calls_markup.py`` — and merged at module assembly.  Both
passes MUST agree on which calls fuse, or a fused call site references an
import the pre-scan suppressed (WAT compile error) / the pre-scan emits a
sync import the translation never calls.  These predicates are that
single source of truth; do not re-derive the conditions inline.
"""

from __future__ import annotations

import dataclasses
from collections.abc import Mapping

from vera import ast
from vera.monomorphize import resolve_fn_type_alias, resolve_type_alias

# Http op name → (fused import name, expected arity).
_FUSABLE_HTTP_OPS: dict[str, tuple[str, int]] = {
    "get": ("async_http_get", 1),
    "post": ("async_http_post", 2),
}


def _expr_is_call_free(node: ast.Node) -> bool:
    """True iff the expression subtree contains no calls at all.

    Conservative purity-by-shape: literals, slot references, operators,
    and constructors qualify; any ``FnCall`` / ``QualifiedCall`` /
    ``AnonFn`` disqualifies (a lambda literal is inert, but rejecting it
    costs only a missed fusion, never a false W002; a pipe is the call it
    stands for, written as one by the transform, so it is covered too).
    """
    if isinstance(node, (ast.FnCall, ast.QualifiedCall, ast.AnonFn)):
        return False
    if not dataclasses.is_dataclass(node):
        return True
    for f in dataclasses.fields(node):
        value = getattr(node, f.name)
        items = value if isinstance(value, tuple) else (value,)
        for item in items:
            if isinstance(item, ast.Node) and not _expr_is_call_free(item):
                return False
    return True


def fused_async_arg_target(arg: ast.Expr) -> str | None:
    """Return the fused import name for ``async(arg)``, or None if eager.

    Fuses exactly the shape ``async(Http.get(e))`` / ``async(Http.post(
    e1, e2))`` where every ``e`` is call-free (evaluated eagerly on the
    guest thread before the request is submitted, preserving program
    order for the argument expressions themselves).
    """
    if not isinstance(arg, ast.QualifiedCall) or arg.qualifier != "Http":
        return None
    target = _FUSABLE_HTTP_OPS.get(arg.name)
    if target is None or len(arg.args) != target[1]:
        return None
    if not all(_expr_is_call_free(a) for a in arg.args):
        return None
    return target[0]


def fused_async_target(call: ast.FnCall) -> str | None:
    """``fused_async_arg_target`` lifted to the ``async(...)`` FnCall."""
    if call.name != "async" or len(call.args) != 1:
        return None
    return fused_async_arg_target(call.args[0])


def _is_future_result_string_type(
    type_name: str, type_args: tuple[ast.TypeExpr, ...] | None,
) -> bool:
    """True iff the slot type is exactly ``Future<Result<String, String>>``.

    This is the only Vera type a fused future inhabits (only Http ops
    fuse, and both return ``Result<String, String>``), and it is always
    represented as a heap pointer — which is what makes the runtime
    tag-probe at the await site memory-safe.  ``Future<Int>`` (i64) and
    other value-typed futures never carry a fused handle and keep the
    identity lowering.
    """
    if type_name != "Future" or not type_args or len(type_args) != 1:
        return False
    inner = type_args[0]
    return (
        isinstance(inner, ast.NamedType)
        and inner.name == "Result"
        and inner.type_args is not None
        and len(inner.type_args) == 2
        and all(
            isinstance(ta, ast.NamedType)
            and ta.name == "String"
            and not ta.type_args
            for ta in inner.type_args
        )
    )


def _canonicalize_type_expr_aliases(
    te: ast.TypeExpr,
    type_aliases: Mapping[str, ast.TypeExpr],
    type_alias_params: Mapping[str, tuple[str, ...] | None],
    _active: frozenset[str] = frozenset(),
) -> ast.TypeExpr | None:
    """``te`` with every type alias replaced by its terminal target,
    recursively.

    :func:`resolve_type_alias` resolves the OUTER alias chain only —
    ``type F = G`` down to ``Future<...>`` — but leaves an alias sitting
    INSIDE the terminal's type arguments untouched (``Future<R>`` with
    ``type R = Result<String, String>``).  The fused-await classifier's
    terminal check is exact-shape, so a payload alias hides the shape
    just as effectively as an outer one — the same #1109 mis-lower one
    level down (PR #1110 review).  This walk canonicalizes both levels:
    resolve the outer chain, then recurse into the terminal
    ``NamedType``'s type arguments.

    ``_active`` is the path-local cycle guard: names already being
    resolved on THIS recursion path.  A cyclic payload alias
    (``type A = Future<A>``, or the mutual ``A = Future<B> / B = Array<A>``)
    regenerates itself one descent at a time — the outer resolver's
    seen-set never fires because each hop terminates at a non-alias
    container — so without the guard the walk spins (RecursionError,
    PR #1111-review).  Detecting the repeat yields ``None`` and the
    caller falls to its conservative identity lowering.  The set unions
    per descent, so it unwinds with the path: a name repeated across
    SIBLING branches (``Pair<R, R>``) is not a cycle and still resolves
    (the checker rejects alias cycles upstream with ``[E132]``, #1059 —
    this is defence-in-depth, matching :func:`resolve_type_alias` and
    ``_canonicalize_alias_slot_name``).
    """
    resolved = resolve_type_alias(te, type_aliases, type_alias_params)
    if resolved is None:
        return None
    if isinstance(resolved, ast.NamedType) and resolved.type_args:
        args: list[ast.TypeExpr] = []
        for arg in resolved.type_args:
            # The cycle probe unwraps refinement layers first: a
            # refinement-wrapped alias (`Future<{ @A | true }>`) cycles
            # through the refinement's BASE, and the resolver peels the
            # refinement inside the recursion — so guarding on the bare
            # argument's name alone would miss the repeat and spin
            # (PR #1110 review).  Direct `NamedType` arguments probe as
            # themselves, unchanged.
            probe = arg
            while isinstance(probe, ast.RefinementType):
                probe = probe.base_type
            if isinstance(probe, ast.NamedType) and probe.name in _active:
                return None
            canonical = _canonicalize_type_expr_aliases(
                arg, type_aliases, type_alias_params,
                (_active | {probe.name})
                if isinstance(probe, ast.NamedType)
                else _active,
            )
            if canonical is None:
                return None
            args.append(canonical)
        resolved = ast.NamedType(name=resolved.name, type_args=tuple(args))
    return resolved


def _resolves_to_future_result_string(
    te: ast.TypeExpr,
    type_aliases: Mapping[str, ast.TypeExpr],
    type_alias_params: Mapping[str, tuple[str, ...] | None],
) -> bool:
    """True iff ``te`` — with type aliases resolved transitively, at the
    outer level AND inside type arguments — is exactly
    ``Future<Result<String, String>>``.

    Aliases are transparent everywhere else in the language; the
    fused-await classifier resolves them too (#1109), so an alias-typed
    slot, an alias-spelled declared return, or a payload-aliased
    ``Future<R>`` participates exactly like the literal spelling.  The
    #843 ``apply_fn`` arm already resolved fn-type aliases through
    :func:`resolve_fn_type_alias`; this helper routes every OTHER
    classification site through the same recursive canonicalization
    (:func:`_canonicalize_type_expr_aliases`) so their alias coverage
    cannot drift.  Discrimination is unchanged: only the exact terminal
    spelling classifies — an alias to ``Future<Result<Int, Int>>``,
    ``Future<String>``, or a non-``Future`` still canonicalizes to a
    shape the check rejects (identity lowering).  A cyclic or otherwise
    unresolvable shape conservatively returns ``False`` — the pre-#1109
    behaviour for shapes the resolver cannot see through.
    """
    resolved = _canonicalize_type_expr_aliases(te, type_aliases, type_alias_params)
    return (
        isinstance(resolved, ast.NamedType)
        and _is_future_result_string_type(resolved.name, resolved.type_args)
    )


def compute_future_ret_fns(
    fn_ret_type_exprs: dict[str, ast.TypeExpr],
    type_aliases: dict[str, ast.TypeExpr] | None = None,
    type_alias_params: dict[str, tuple[str, ...]] | None = None,
) -> frozenset[str]:
    """Names of fns declared to return ``Future<Result<String, String>>``.

    Derived from the codegen return-type registry
    (``_fn_ret_type_exprs``), which covers local functions
    (``registration.py``) AND imported module functions (the #628
    harvest in ``modules.py``) — so both the unqualified imported-call
    shape ``await(grab(...))`` and the qualified ``await(m::grab(...))``
    classify correctly (PR #842 review, critical finding: a
    local-declarations-only scan missed cross-module futures and the
    await lowered to identity).  Computed once per program in
    ``vera/codegen/core.py`` after Pass 0/1 registration and consumed
    by both import-emission passes (the ``_scan_io_ops`` pre-scan and
    the ``WasmContext`` await lowering) so the two agree on which
    directly-awaited call results need the fused-handle runtime check.
    The match resolves type aliases transitively (#1109) — a helper
    declared ``-> @MyFut`` with
    ``type MyFut = Future<Result<String, String>>`` participates
    exactly like the literal spelling.
    """
    aliases = type_aliases if type_aliases is not None else {}
    alias_params = type_alias_params if type_alias_params is not None else {}
    names: set[str] = set()
    for fn_name, ret in fn_ret_type_exprs.items():
        if _resolves_to_future_result_string(ret, aliases, alias_params):
            names.add(fn_name)
    return frozenset(names)


def compute_future_ret_module_fns(
    module_fn_ret_type_exprs: dict[tuple[tuple[str, ...], str], ast.TypeExpr],
    type_aliases: dict[str, ast.TypeExpr] | None = None,
    type_alias_params: dict[str, tuple[str, ...]] | None = None,
) -> frozenset[tuple[tuple[str, ...], str]]:
    """(module path, name) pairs returning ``Future<Result<String, String>>``.

    The qualified companion to :func:`compute_future_ret_fns`: a
    module-qualified ``await(m::grab(...))`` must classify by the
    resolved target's return type, not by the bare name — a colliding
    local ``grab`` with a different future shape would otherwise
    misclassify the qualified call in both directions (PR #842 review
    round 2, confirmed with a name-collision repro).
    """
    aliases = type_aliases if type_aliases is not None else {}
    alias_params = type_alias_params if type_alias_params is not None else {}
    pairs: set[tuple[tuple[str, ...], str]] = set()
    for key, ret in module_fn_ret_type_exprs.items():
        if _resolves_to_future_result_string(ret, aliases, alias_params):
            pairs.add(key)
    return frozenset(pairs)


# `resolve_fn_type_alias` — the single transitive-alias-to-fn-type
# resolver every consultor shares — moved to `vera/monomorphize.py`
# (the codegen-free shared home, #732 precedent) when the PR #880
# review extended its consumer set to the generic-HOF consultors in
# `vera/monomorphize.py` itself: this module imports from
# `vera.monomorphize`, so hosting the resolver here would have made
# the monomorphizer's import an import cycle.  Imported above and
# still consumed by `_apply_fn_closure_ret_type` below.


def _apply_fn_closure_ret_type(
    closure_arg: ast.Expr,
    type_aliases: Mapping[str, ast.TypeExpr],
    type_alias_params: Mapping[str, tuple[str, ...] | None],
) -> ast.TypeExpr | None:
    """Declared return TypeExpr of the closure an ``apply_fn`` applies.

    Mirrors the two closure-arg shapes ``_infer_apply_fn_return_type``
    (``vera/wasm/inference.py``) supports for the ``call_indirect``
    signature — the same shapes the checker types ``apply_fn`` against:

    * a ``SlotRef`` into a ``FnType`` type alias (a let-bound or
      parameter closure ref), resolved **transitively** through the alias
      chain (``type Fetcher = InnerFetcher;`` — #867) with the slot's
      bound type args substituted for a generic alias's params, via the
      shared :func:`resolve_fn_type_alias`, and
    * an inline ``AnonFn`` closure literal.

    Returns ``None`` for any other shape, signalling that the declared
    return type is not statically resolvable here.  The identity-await
    fallback that follows is safe because each unresolvable shape has
    its own loud backstop, mirrored from what the ``apply_fn``
    translation does with it:

    * a **``FnCall``-shaped closure arg** (e.g. ``apply_fn(make_fn(), …)``)
      is rejected by the translation with ``[E616]`` and the function is
      skipped;
    * a **``SlotRef`` through an alias chain that never reaches a
      ``FnType``** falls to the ``i64`` signature default, so the
      ``call_indirect`` type mismatch traps at WASM validation.

    Either way no fused wrapper silently reaches an identity await
    (#843 floor).  This consultor and ``_infer_apply_fn_return_type``
    resolve the SlotRef through the same :func:`resolve_fn_type_alias`,
    so their depth-N coverage cannot drift.
    """
    if isinstance(closure_arg, ast.SlotRef):
        fn_type = resolve_fn_type_alias(
            ast.NamedType(
                name=closure_arg.type_name,
                type_args=closure_arg.type_args,
            ),
            type_aliases,
            type_alias_params,
        )
        return fn_type.return_type if fn_type is not None else None
    if isinstance(closure_arg, ast.AnonFn):
        return closure_arg.return_type
    return None


def apply_fn_awaits_fused_future(
    arg: ast.Expr,
    type_aliases: Mapping[str, ast.TypeExpr],
    type_alias_params: Mapping[str, tuple[str, ...] | None],
) -> bool:
    """True iff ``arg`` is ``apply_fn(closure, …)`` whose closure's
    declared return type is ``Future<Result<String, String>>``.

    This is the #843 indirect-closure arm: the call target is a runtime
    value (a fn-typed slot or an inline ``AnonFn``), not a name in the
    return-type registry, so it is classified by the closure's *declared*
    return type instead — the post-#854 precedent of consulting declared
    types rather than WASM-width inference.  When the closure's return
    type is not statically resolvable (a shape ``_apply_fn_closure_ret_type``
    cannot see through), this returns ``False`` and the await keeps its
    identity lowering — safe because each such shape fails loudly
    elsewhere: ``[E616]`` for a ``FnCall``-shaped closure arg, the #867
    WASM-validation trap for an alias-of-alias slot (see
    ``_apply_fn_closure_ret_type``).
    """
    if not (
        isinstance(arg, ast.FnCall)
        and arg.name == "apply_fn"
        and len(arg.args) >= 2
    ):
        return False
    ret = _apply_fn_closure_ret_type(
        arg.args[0], type_aliases, type_alias_params,
    )
    if ret is None:
        return False
    # The closure's declared return may itself spell the future type
    # through an alias (`fn(String -> F)` with `type F = Future<...>`)
    # — resolve it before the literal check, like every other site
    # (#1109).
    return _resolves_to_future_result_string(
        ret, type_aliases, type_alias_params,
    )


def await_needs_check(
    arg: ast.Expr,
    future_ret_fns: frozenset[str] | set[str],
    future_ret_module_fns: (
        frozenset[tuple[tuple[str, ...], str]]
        | set[tuple[tuple[str, ...], str]]
    ) = frozenset(),
    type_aliases: Mapping[str, ast.TypeExpr] | None = None,
    type_alias_params: Mapping[str, tuple[str, ...] | None] | None = None,
) -> bool:
    """True iff ``await(arg)`` must emit the runtime fused-handle check.

    Matches every shape that can carry a fused future to an await site:
    a ``Future<Result<String, String>>``-typed slot (let binding or
    parameter — spelled literally or through a type alias, resolved
    transitively, #1109), a directly-composed fused ``async(...)``, a
    call — bare, imported, or module-qualified — to a function whose
    declared return type is that future type (``future_ret_fns``,
    computed in ``vera/codegen/core.py`` from the cross-module
    return-type registry), an ``apply_fn`` on a closure whose *declared*
    return type is that future type (the #843 indirect-closure arm,
    classified via ``type_aliases`` + ``type_alias_params`` — the
    latter drives the generic-alias type-arg substitution), and
    ``if``/``match``/block compositions of those.  Shapes outside this
    set keep the identity lowering.  Keep this predicate's coverage in
    sync with every call shape codegen can produce.
    """
    aliases = type_aliases if type_aliases is not None else {}
    alias_params = type_alias_params if type_alias_params is not None else {}
    if isinstance(arg, ast.SlotRef):
        return _resolves_to_future_result_string(
            ast.NamedType(name=arg.type_name, type_args=arg.type_args),
            aliases, alias_params,
        )
    if isinstance(arg, ast.FnCall):
        if fused_async_target(arg) is not None:
            return True
        if arg.name == "apply_fn":
            return apply_fn_awaits_fused_future(arg, aliases, alias_params)
        return arg.name in future_ret_fns
    if isinstance(arg, ast.ModuleCall):
        return (tuple(arg.path), arg.name) in future_ret_module_fns
    if isinstance(arg, ast.Block):
        return arg.expr is not None and await_needs_check(
            arg.expr, future_ret_fns, future_ret_module_fns,
            aliases, alias_params,
        )
    if isinstance(arg, ast.IfExpr):
        if await_needs_check(
            arg.then_branch, future_ret_fns, future_ret_module_fns,
            aliases, alias_params,
        ):
            return True
        return arg.else_branch is not None and await_needs_check(
            arg.else_branch, future_ret_fns, future_ret_module_fns,
            aliases, alias_params,
        )
    if isinstance(arg, ast.MatchExpr):
        return any(
            await_needs_check(
                arm.body, future_ret_fns, future_ret_module_fns,
                aliases, alias_params,
            )
            for arm in arg.arms
        )
    return False
