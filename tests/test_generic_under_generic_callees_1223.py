"""#1223: a generic `where`-helper under a GENERIC parent instantiates its
own generic callees.

`forall<T> fn parent` carrying a `forall<U> fn helper` is the #1002 shape:
the helper stays generic inside every clone of the parent, and both sides
already instantiate the HELPER per its concrete call sites (codegen's
`_instantiate_hoisted_generic`, the verifier's `record_nested`).  Neither
side then walked the helper CLONE's own body.  A top-level generic called
from inside the helper — `pick(@U.1, @U.0)` — was therefore discovered
only in its still-generic spelling, binding the type variable's own NAME
(`pick$U`, a clone whose `@U` parameter is not a WASM type), while the
call-rewrite asked for the concrete `pick$Bool`.  The result on a
check-clean, verify-clean program:

    [E602] … call target 'pick$Bool' not registered in this module
    [E620] 'parent$Int' … dropped
    [E620] 'main' … dropped
    Error: No exported functions

The same helper under a NON-generic parent compiles, so the trigger is the
generic ancestor: without one the helper is instantiated by the ordinary
worklist, whose every clone IS rescanned.

Two proving checks, and the second is the one that makes the fix a pair.
Locally: a differential between the clone symbols codegen REGISTERS and
the clone symbols the WASM call-rewrite RESOLVES — captured at the
consultor level, because a desync skips the calling function and elides
the dangling `call` from the WAT along with it.  Globally: the same
shapes join `tests/test_monomorphize_differential.py`'s `_INLINE_CORPUS`,
whose #732 check asserts the verifier discovers everything codegen emits
— so the codegen half alone turns that suite red, and the two halves have
to land together.
"""

from __future__ import annotations

import pytest

from tests import pipeline
from tests.checker_helpers import _check_ok
from tests.codegen_helpers import _compile, _run
from tests.verifier_helpers import _verify_ok

# `pick` returns its SECOND parameter (`@W.0` is the most recent binding),
# and the helper hands it `(@U.1, @U.0)` — its first and second parameters
# in that order.  So `helper(true, false)` is `false` and the branch value
# is 3; swapping either argument pair gives 7, so the oracle distinguishes
# the wiring rather than just the compile.
_USER_GENERIC = """
private forall<W> fn pick(@W, @W -> @W)
  requires(true)
  ensures(true)
  effects(pure)
{
  @W.0
}

private forall<T> fn parent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if helper(true, false) then { 7 } else { 3 }
}
where {
  forall<U> fn helper(@U, @U -> @U)
    requires(true)
    ensures(true)
    effects(pure)
  {
    pick(@U.1, @U.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(1)
}
"""

# The prelude twin: the helper's callee is `option_unwrap_or`, whose clone
# `option_unwrap_or$Bool` is equally undiscovered.
_PRELUDE_GENERIC = """
private forall<T> fn parent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if helper(Some(false), true) then { 7 } else { 3 }
}
where {
  forall<U> fn helper(@Option<U>, @U -> @U)
    requires(true)
    ensures(true)
    effects(pure)
  {
    option_unwrap_or(@Option<U>.0, @U.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(1)
}
"""

# Two levels of generic nesting: the inner helper is generic under a
# generic helper under a generic parent, and IT is the one calling `pick`.
# The instantiation has to survive both hoisting rounds.
_DEPTH_TWO = """
private forall<W> fn pick(@W, @W -> @W)
  requires(true)
  ensures(true)
  effects(pure)
{
  @W.0
}

private forall<T> fn parent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if outer(true, false) then { 7 } else { 3 }
}
where {
  forall<U> fn outer(@U, @U -> @U)
    requires(true)
    ensures(true)
    effects(pure)
  {
    inner(@U.1, @U.0)
  }
  forall<V> fn inner(@V, @V -> @V)
    requires(true)
    ensures(true)
    effects(pure)
  {
    pick(@V.1, @V.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(1)
}
"""

# The NON-generic-parent control.  This compiled before the fix and must
# keep compiling: it is what proves the trigger is the generic ancestor
# rather than the nested helper, so a "fix" that only made the reported
# program work without touching the ancestor case would leave it green
# either way and prove nothing.
_NONGENERIC_PARENT = """
private forall<W> fn pick(@W, @W -> @W)
  requires(true)
  ensures(true)
  effects(pure)
{
  @W.0
}

private fn parent(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if helper(true, false) then { 7 } else { 3 }
}
where {
  forall<U> fn helper(@U, @U -> @U)
    requires(true)
    ensures(true)
    effects(pure)
  {
    pick(@U.1, @U.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(1)
}
"""

_CASES = [
    ("user_generic", _USER_GENERIC, 3),
    ("prelude_generic", _PRELUDE_GENERIC, 3),
    ("depth_two", _DEPTH_TWO, 3),
    ("nongeneric_parent_control", _NONGENERIC_PARENT, 3),
]


def _registered_and_resolved(source: str) -> tuple[set[str], set[str]]:
    """(clone symbols codegen REGISTERS, clone symbols the rewrite RESOLVES).

    The registered set is the emitted mono-decl NAMES — not
    ``_emitted_instances``, whose generic-under-generic entries are keyed by
    the concrete-FREE lexical chain (``parent$where$helper``) rather than by
    the per-clone emission name (``parent$Int$where$helper$Bool``) that the
    rewrite actually calls.  The resolved set is captured on
    ``_resolve_generic_call`` rather than scraped from the WAT, because a
    desync skips the CALLING function and takes the dangling ``call``
    instruction out of the WAT with it.
    """
    from vera.codegen.monomorphize import MonomorphizationMixin
    from vera.wasm.calls import CallsMixin

    registered: set[str] = set()
    resolved: set[str] = set()
    orig_mono = MonomorphizationMixin._monomorphize
    orig_resolve = CallsMixin._resolve_generic_call

    def _mono_spy(self: object, program: object) -> object:
        out = orig_mono(self, program)  # type: ignore[arg-type]
        registered.update(d.name for d in out)  # type: ignore[attr-defined]
        return out

    def _resolve_spy(self: object, call: object) -> object:
        target = orig_resolve(self, call)  # type: ignore[arg-type]
        if target is not None:
            resolved.add(target)
        return target

    MonomorphizationMixin._monomorphize = _mono_spy  # type: ignore[assignment,method-assign]
    CallsMixin._resolve_generic_call = _resolve_spy  # type: ignore[assignment]
    try:
        _ = pipeline.compile(source, file="fixture.vera", checked=False).result
    finally:
        MonomorphizationMixin._monomorphize = orig_mono  # type: ignore[assignment,method-assign]
        CallsMixin._resolve_generic_call = orig_resolve  # type: ignore[assignment]
    return registered, resolved


@pytest.mark.parametrize(
    ("source", "expected"),
    [pytest.param(s, e, id=i) for i, s, e in _CASES],
)
def test_generic_under_generic_helper_callees_are_emitted(
    source: str, expected: int,
) -> None:
    """No skip, no drop, and the checker's value out of the compiled program."""
    _check_ok(source)
    _verify_ok(source)
    result = _compile(source)
    codes = [d.error_code for d in result.diagnostics]
    assert "E602" not in codes, (
        f"clone never registered: {[d.description for d in result.diagnostics]}"
    )
    assert "E620" not in codes, (
        f"caller dropped: {[d.description for d in result.diagnostics]}"
    )
    assert _run(source) == expected


@pytest.mark.parametrize(
    "source", [pytest.param(s, id=i) for i, s, _ in _CASES],
)
def test_registered_clones_cover_every_resolved_target(source: str) -> None:
    """Differential: every clone the rewrite calls is a clone codegen emitted."""
    registered, resolved = _registered_and_resolved(source)
    assert resolved, (
        "no generic call was rewritten — the shape no longer exercises "
        "monomorphization and the check would pass vacuously"
    )
    dangling = sorted(resolved - registered)
    assert not dangling, (
        f"call-rewrite resolves clone(s) codegen never emitted: {dangling}\n"
        f"  registered = {sorted(registered)}"
    )
