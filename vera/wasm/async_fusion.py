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

from vera import ast

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
    costs only a missed fusion, never a false W002; pipes desugar to
    ``FnCall`` before codegen, so they are covered transitively).
    """
    if isinstance(node, (ast.FnCall, ast.QualifiedCall, ast.AnonFn)):
        return False
    import dataclasses

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


def compute_future_ret_fns(program: ast.Program) -> frozenset[str]:
    """Names of fns declared to return ``Future<Result<String, String>>``.

    Computed once per program in ``vera/codegen/core.py`` and consumed
    by both import-emission passes (the ``_scan_io_ops`` pre-scan and
    the ``WasmContext`` await lowering) so the two agree on which
    directly-awaited call results need the fused-handle runtime check.
    The match is on the literal type expression — an alias like
    ``type MyFut = Future<Result<String, String>>`` does not
    participate (documented in spec §9.5.4; the wrapper tag keeps a
    missed check loud rather than silent).
    """
    names: set[str] = set()
    for tld in program.declarations:
        decl = tld.decl
        if not isinstance(decl, ast.FnDecl):
            continue
        ret = decl.return_type
        if isinstance(ret, ast.NamedType) and _is_future_result_string_type(
            ret.name, ret.type_args,
        ):
            names.add(decl.name)
    return frozenset(names)


def await_needs_check(
    arg: ast.Expr, future_ret_fns: frozenset[str] | set[str],
) -> bool:
    """True iff ``await(arg)`` must emit the runtime fused-handle check.

    Matches every shape that can carry a fused future to an await site:
    a ``Future<Result<String, String>>``-typed slot (let binding or
    parameter), a directly-composed fused ``async(...)``, a call to a
    function whose declared return type is that future type
    (``future_ret_fns``, computed in ``vera/codegen/core.py``), and
    ``if``/``match``/block compositions of those.  Shapes outside this
    set keep the identity lowering; a fused wrapper reaching one anyway
    is caught loudly by the consumer's ``match`` (the wrapper tag
    0xFEEDC004 matches no constructor → trap), never read silently.
    """
    if isinstance(arg, ast.SlotRef):
        return _is_future_result_string_type(arg.type_name, arg.type_args)
    if isinstance(arg, ast.FnCall):
        if fused_async_target(arg) is not None:
            return True
        return arg.name in future_ret_fns
    if isinstance(arg, ast.Block):
        return arg.expr is not None and await_needs_check(
            arg.expr, future_ret_fns,
        )
    if isinstance(arg, ast.IfExpr):
        if await_needs_check(arg.then_branch, future_ret_fns):
            return True
        return arg.else_branch is not None and await_needs_check(
            arg.else_branch, future_ret_fns,
        )
    if isinstance(arg, ast.MatchExpr):
        return any(
            await_needs_check(arm.body, future_ret_fns) for arm in arg.arms
        )
    return False
