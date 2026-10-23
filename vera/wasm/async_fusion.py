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

Import emission is decided once, by the ``WasmContext`` translation in
``vera/wasm/calls_markup.py``, which registers the import each fused call
or checked await calls (#735).  These predicates are the single source of
truth for that translation, their one reader; do not re-derive the
conditions inline.
"""

from __future__ import annotations

import dataclasses

from vera import ast
from vera.types import STRING, AdtType, Type, base_type

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


def is_fused_future_type(ty: Type | None) -> bool:
    """True iff *ty*, a type the checker gave a value, is exactly
    ``Future<Result<String, String>>``, the only type a fused future
    inhabits (only `Http` operations fuse, and both return
    ``Result<String, String>``).  An alias of it is the type itself: the
    checker's types hold no alias.  A value of this type is always a heap
    pointer, which is what makes the runtime tag probe at the await site
    memory-safe; ``Future<Int>`` (an i64) and every other future keep the
    identity lowering."""
    if ty is None:
        return False
    ty = base_type(ty)
    if not (isinstance(ty, AdtType) and ty.name == "Future"
            and len(ty.type_args) == 1):
        return False
    inner = base_type(ty.type_args[0])
    return (isinstance(inner, AdtType) and inner.name == "Result"
            and len(inner.type_args) == 2
            and all(base_type(a) == STRING for a in inner.type_args))
