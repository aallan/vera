"""The `@Nat` -> `@Int` widening guard names itself (#1438).

The guard has always worked: a `@Nat` above `i64.MAX` reinterprets to a
negative `@Int` under the shared machine representation, and code
generation traps rather than let the value through.  What it could not do
was say so.  Its trap was a bare `unreachable`, which earns the generic
paragraph naming three causes — a non-exhaustive `match`, a
compiler-generated assertion, GC shadow-stack overflow — none of which can
produce it, and never the remedy the user needs (`requires(... <= i64.MAX)`).

Its narrowing twin was given a dedicated kind in #754 by calling a host
import immediately before the `unreachable`, so the runtime classifies on
which guard fired rather than on the instruction they share.  This is the
same mechanism at the other boundary, and the cost is the same fan-in: a
`_needs_widen_trap` flag merged at every per-scope seam, an import declared
and bound in each runtime, and a WASI dispatch slot.  A missed seam is not
a wrong message — it is a module that calls an undeclared import and fails
to instantiate, and only on the shape that reaches that scope.

So there is a cell per runtime: wasmtime here, the browser bundle in
`test_browser.py::test_widen_trap_parity`, and the WASI component below.
"""

from __future__ import annotations


from tests.codegen_helpers import _compile_ok
from vera.codegen.api import execute
from vera.runtime.traps import WasmTrapError

#: `u64.MAX`'s bit pattern — what a `@Nat` above `i64.MAX` IS at the
#: boundary the guard watches, and what reinterprets to `-1` without it.
_ABOVE_I64_MAX = -1

_WIDEN = """\
public fn widen(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = @Nat.0;
  @Int.0
}
"""

_WIDEN_IN_CLOSURE = """\
type Widener = fn(Nat -> Int) effects(pure);

public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Widener = fn(@Nat -> @Int) effects(pure) { let @Int = @Nat.0; @Int.0 };
  apply_fn(@Widener.0, @Nat.0)
}
"""

_WIDEN_MAIN = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = string_length("abc");
  let @Int = @Nat.0;
  @Int.0
}
"""


class TestTheWideningGuardNamesItself:
    def test_the_native_runtime_reports_the_dedicated_kind(self) -> None:
        result = _compile_ok(_WIDEN)
        try:
            out = execute(result, fn_name="widen", args=[_ABOVE_I64_MAX])
        except WasmTrapError as exc:
            assert exc.kind == "widen_guard", exc.kind
            assert "i64.MAX" in str(exc), str(exc)
            return
        raise AssertionError(
            f"the widening guard did not fire, so this cell measured "
            f"nothing: returned {out.value!r}"
        )

    def test_and_the_fix_names_the_remedy_that_discharges_it(self) -> None:
        """The half that makes the kind worth having.

        A kind nobody reads is a label; what a user needs is the sentence
        telling them which precondition removes the check.  The old
        paragraph named `requires(... >= 0)` at best — the NARROWING
        remedy — which is the wrong bound in the wrong direction.
        """
        result = _compile_ok(_WIDEN)
        try:
            execute(result, fn_name="widen", args=[_ABOVE_I64_MAX])
        except WasmTrapError as exc:
            fix = exc.fix or ""
            assert "i64.MAX" in fix, fix
            assert "requires" in fix, fix
            assert "non-exhaustive" not in fix, (
                f"the widening trap still shows the generic `unreachable` "
                f"paragraph, whose causes cannot produce it:\n{fix}"
            )
            return
        raise AssertionError("the widening guard did not fire")

    def test_a_widening_inside_a_closure_body_still_links(self) -> None:
        """The per-scope seam, pinned where dropping it actually shows.

        A closure body is compiled in its own translation context, so its
        `_needs_widen_trap` has to be merged back into the generator that
        assembles the module.  Miss that merge and the module CALLS
        `$vera.widen_trap` without declaring it: measured, the failure is
        `WAT compilation failed: unknown func: failed to find name
        `$vera.widen_trap``, and it takes down every program whose widening
        happens inside a closure while leaving the same widening at top
        level working.  That asymmetry is what makes it easy to ship — the
        obvious fixture passes.

        The value is deliberately IN range: the property is that the module
        links and runs, not that the guard fires.
        """
        result = _compile_ok(_WIDEN_IN_CLOSURE)
        assert "$vera.widen_trap" in result.wat, (
            "no widening guard inside the closure, so the seam this cell "
            "pins is not exercised"
        )
        out = execute(result, fn_name="f", args=[7])
        assert out.value == 7, out

    def test_the_wasi_component_wires_the_shim_and_still_instantiates(
        self,
    ) -> None:
        """The third runtime, where the channel is the backtrace.

        A component has no host-side sentinel list to write into, so the
        classification reads the SHIM NAME out of the trap's backtrace —
        which means the shim has to exist and be reachable at its own
        dispatch slot, not colliding with the `Map` ops the server world
        composes into the same index space.

        The property is read from a program that WIDENS and does not trap:
        the guard is emitted, so the import is declared, so the component
        must still instantiate and return.  That is the fan-in failure this
        cell exists to catch — a missed seam is not a wrong message but a
        module that will not load, and it would take down every program
        containing a widening rather than only the ones that trip the
        guard.  The trap's own kind is asserted on the two runtimes above,
        where a value can be handed in.
        """
        from tests.test_wasi_target import _run_component

        result = _compile_ok(_WIDEN_MAIN)
        assert "$vera.widen_trap" in result.wat, (
            "the widening guard emitted no signal, so this cell would "
            "instantiate a component with nothing to wire"
        )
        value, _, _ = _run_component(result)
        assert value == 3, value
