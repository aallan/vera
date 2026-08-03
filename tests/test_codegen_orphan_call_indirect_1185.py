"""Tests for #1185 — an orphan ``call_indirect`` never reaches the output.

The unclosed half of the #1100 class.  When an ``[E602]`` skip swallows a
program's *only* closure, the closure lift is rolled back — so module
assembly suppresses the ``(table)``/``(elem)`` sections (``_closure_table``
is empty) — but every surviving function that reaches a closure through
``call_indirect`` still carries that instruction.  The result was an
**uninstantiable** module emitted with ZERO error diagnostics: running any
unrelated surviving export raised a raw
``WasmtimeError: … unknown table 0: table index out of bounds``.

Two independent emission sites produce a ``call_indirect`` in a function
that holds no closure of its own, so both reproduce the class:

* the ``apply_fn`` special form (``vera/wasm/closures.py``), which lowers
  to ``call_indirect`` unconditionally for any closure-typed parameter;
* a monomorphized clone of a prelude combinator (``option_map``), whose
  clone body applies the passed-in closure the same way.

The fix propagates the drop to the ``call_indirect`` carriers exactly as
#1100 propagates it to ordinary ``call $f`` callers: with no function
table in the module, a carrier's indirect call can only have targeted a
dropped closure, so the carrier is itself dropped with an [E620] naming
the [E602] root — a loud, located refusal rather than an opaque wasmtime
error at call time (DESIGN.md: fail loud).

The invariant this pins, asserted as a differential over the emitted WAT:
**a module containing ``call_indirect`` declares a table.**
``tests/codegen_helpers.py::_compile`` enforces this universal one-way
invariant on every compile.  These fixtures additionally call
``_assert_call_indirect_iff_table`` where both directions are under
test — the converse is legitimately false in general (a table with no
surviving indirect call is inert and valid).
"""
from __future__ import annotations

import pytest

from vera.codegen import CompileResult, execute
from vera.errors import Diagnostic

from tests.codegen_helpers import _assert_call_indirect_iff_table, _compile
from tests.codegen_helpers import _assert_no_raw_wat_error

# The E602-skippable construct used throughout: an Array-valued Map is an
# unsupported host-import shape.  Any E602-skippable construct reproduces
# the class; this one matches the #1100 fixtures so the two files fail for
# the same root cause.
_BAD_BODY = """\
    let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
    map_size(@Map<String, Array<Int>>.0) + @Int.0\
"""

# Repro A — the `apply_fn` carrier.  `make_bad`'s closure is the module's
# ONLY closure and is swallowed by [E602], so `make_bad` and its caller
# `main` drop (#636 + #1100) and the function table is suppressed.
# `use_it` survives with a `call_indirect` to a table that no longer
# exists.  `ok` is the victim: an unrelated export that must still run.
_APPLY_FN_ORPHAN = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn make_bad(-> @IntToInt) requires(true) ensures(true) effects(pure) {
  fn(@Int -> @Int) effects(pure) {
""" + _BAD_BODY + """
  }
}

private fn use_it(@IntToInt, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  apply_fn(@IntToInt.0, @Int.0)
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @IntToInt = make_bad();
  use_it(@IntToInt.0, 1)
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""

# Repro B — the carrier is a monomorphized clone of a prelude combinator
# (`option_map$Int_JInt`), not a user-written function.  The clone's body
# applies its closure argument through the same table.
_MONO_CLONE_ORPHAN = """\
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Option<Int> = Some(1);
  let @Option<Int> = option_map(@Option<Int>.0, fn(@Int -> @Int) effects(pure) {
""" + _BAD_BODY + """
  });
  option_unwrap_or(@Option<Int>.0, 0)
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""

# Repro C — no closure is skipped because the program never writes one.
# A closure-typed parameter alone emits `call_indirect`, so the module was
# uninstantiable with NO diagnostic of any kind — not even the [E602] the
# other two carry.  Surfaced by hardening `_assert_no_raw_wat_error`.
_NO_CLOSURE_AT_ALL = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn use_it(@IntToInt, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  apply_fn(@IntToInt.0, @Int.0)
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""


def _e620s(result: CompileResult) -> list[Diagnostic]:
    return [d for d in result.diagnostics if d.error_code == "E620"]


class TestOrphanCallIndirect1185:
    """A `call_indirect` whose table was suppressed drops its carrier."""

    def test_apply_fn_carrier_drops_with_e620_naming_root(self) -> None:
        """Repro A: `use_it` survives the closure skip today and takes the
        whole module down with it.

        Pre-fix: `ok` — an export with nothing to do with closures —
        raised a raw ``WasmtimeError: unknown table 0`` and the compile
        reported no error at all.  Post-fix `use_it` is dropped with an
        [E620] naming the [E602] root, and `ok` runs.
        """
        result = _compile(_APPLY_FN_ORPHAN)
        _assert_no_raw_wat_error(result)
        _assert_call_indirect_iff_table(result.wat)
        # The victim: an unrelated export must execute cleanly.
        assert execute(result, fn_name="ok").value == 41
        e620 = _e620s(result)
        carrier = [
            d for d in e620 if d.description.startswith("Function 'use_it' ")
        ]
        assert len(carrier) == 1, (
            f"the call_indirect carrier must carry exactly one E620, got "
            f"{[d.description for d in e620]}"
        )
        # The chain must name the [E602] ROOT — the skip that emptied the
        # table — not merely "some closure went missing".
        assert "'make_bad'" in carrier[0].description
        assert "[E602]" in carrier[0].description
        root = next(
            d for d in result.diagnostics
            if d.error_code == "E602" and "'make_bad'" in d.description
        )
        assert f"line {root.location.line}" in carrier[0].description
        assert carrier[0].severity == "warning"
        assert carrier[0].rationale, "E620 must carry a rationale"

    def test_mono_clone_carrier_drops(self) -> None:
        """Repro B: the carrier is a prelude combinator's mono clone.

        `option_map$…` is emitted by monomorphization, not written by the
        user, so a fix that only walks user declarations misses it.  Its
        drop must be attributed to the clone itself (position, not mere
        presence — `main`'s own E620 also mentions the closure).
        """
        result = _compile(_MONO_CLONE_ORPHAN)
        _assert_no_raw_wat_error(result)
        _assert_call_indirect_iff_table(result.wat)
        assert execute(result, fn_name="ok").value == 41
        assert "main" not in result.exports
        e620 = _e620s(result)
        clone = [
            d for d in e620
            if d.description.startswith("Function 'option_map$")
        ]
        assert clone, (
            "the monomorphized clone must carry its OWN E620, got: "
            f"{[d.description for d in e620]}"
        )
        # The clone is prelude code, so the drop must be reported against
        # `<prelude>` — not against whatever the user's file happens to
        # hold at the prelude declaration's line number.
        assert clone[0].location.file == "<prelude>", (
            f"clone drop mis-attributed to {clone[0].location.file}"
        )
        assert "'main'" in clone[0].description, (
            "the chain must name the skip that emptied the table"
        )

    def test_no_closure_literal_anywhere_still_instantiable(self) -> None:
        """Repro C: an `apply_fn` carrier in a program with no closure
        literal at all.

        There is no [E602] to chain to — the module simply never declares
        a table — so this compiled with ZERO diagnostics and produced an
        uninstantiable module.  The carrier is dropped with an [E620] that
        explains the absence on its own terms.
        """
        result = _compile(_NO_CLOSURE_AT_ALL)
        _assert_no_raw_wat_error(result)
        _assert_call_indirect_iff_table(result.wat)
        assert execute(result, fn_name="ok").value == 41
        e620 = _e620s(result)
        assert len(e620) == 1, f"got {[d.description for d in e620]}"
        assert e620[0].description.startswith("Function 'use_it' ")
        assert e620[0].rationale


class TestSurvivingClosureControl1185:
    """Over-correction guards: GREEN both before and after the fix.

    Nothing here exercises the orphan path — these pin that a module with
    a *surviving* closure keeps its table and both dispatch paths keep
    working, so a fix that dropped carriers unconditionally goes RED.
    """

    def test_surviving_closure_keeps_apply_fn_working(self) -> None:
        """One closure is swallowed, another survives: the table is
        emitted, so the `apply_fn` carrier must NOT be dropped and the
        application must still compute.

        The pin value is 107 (100 from the surviving closure's capture,
        7 from the argument) — no fallback, default, or trap path
        produces it.
        """
        source = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn make_bad(-> @IntToInt) requires(true) ensures(true) effects(pure) {
  fn(@Int -> @Int) effects(pure) {
""" + _BAD_BODY + """
  }
}

private fn make_good(@Int -> @IntToInt) requires(true) ensures(true) effects(pure) {
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}

private fn use_it(@IntToInt, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  apply_fn(@IntToInt.0, @Int.0)
}

public fn doomed(-> @Int) requires(true) ensures(true) effects(pure) {
  let @IntToInt = make_bad();
  use_it(@IntToInt.0, 1)
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @IntToInt = make_good(100);
  use_it(@IntToInt.0, 7)
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        _assert_call_indirect_iff_table(result.wat)
        assert "(table " in result.wat, (
            "a surviving closure must still emit the function table"
        )
        assert "main" in result.exports, (
            "the surviving closure's caller must not be dropped"
        )
        assert not any(
            d.description.startswith("Function 'use_it' ")
            for d in _e620s(result)
        ), "the carrier must survive while the table exists"
        assert execute(result, fn_name="main").value == 107

    def test_surviving_closure_keeps_array_map_working(self) -> None:
        """The other `call_indirect` emission site — the inline
        `array_map` loop — with a surviving closure alongside a swallowed
        one.  Pin value 63 = sum([21, 21, 21]); no default produces it."""
        source = """\
private fn make_bad(@Int -> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_map([1, 2], fn(@Int -> @Int) effects(pure) {
""" + _BAD_BODY + """
  });
  array_length(@Array<Int>.0)
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { 21 });
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        _assert_call_indirect_iff_table(result.wat)
        assert "(table " in result.wat
        assert execute(result, fn_name="main").value == 63

    def test_plain_program_has_neither(self) -> None:
        """The trivial direction of the iff: a closure-free program emits
        neither a `call_indirect` nor a table, and is untouched."""
        source = """\
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""
        result = _compile(source)
        _assert_call_indirect_iff_table(result.wat)
        assert "call_indirect" not in result.wat
        assert not _e620s(result)
        assert execute(result).value == 41

def test_orphaned_carrier_lands_in_dropped_fns() -> None:
    """The carrier's own drop is recorded for the #1183 contract (PR #1192
    review): `vera run --fn <carrier>` looks the explaining diagnostic up
    in `CompileResult.dropped_fns`, and an orphaned carrier absent from it
    would fall back to the very silent-substitution class the refusal
    machinery exists to close.
    """
    result = _compile(_APPLY_FN_ORPHAN)
    e620_names = {
        d.description.split("'")[1]
        for d in result.diagnostics
        if d.error_code == "E620"
    }
    assert e620_names, "expected at least one E620 drop"
    for name in e620_names:
        assert name in result.dropped_fns, (
            f"'{name}' has an [E620] but no dropped_fns entry — "
            f"the #1183 refusal cannot explain it"
        )
        assert result.dropped_fns[name] is not None
        assert result.dropped_fns[name].error_code == "E620"


# The exception-path fixture: identical carrier topology to
# `_APPLY_FN_ORPHAN`, but the closure body is VALID — the lift failure is
# forced by the test's stub instead.  See
# `test_exception_path_lift_skip_joins_blame_chain` for why.
_VALID_CLOSURE_APPLY = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn make_bad(-> @IntToInt) requires(true) ensures(true) effects(pure) {
  fn(@Int -> @Int) effects(pure) {
    @Int.0 + 1
  }
}

private fn use_it(@IntToInt, @Int -> @Int) requires(true) ensures(true) effects(pure) {
  apply_fn(@IntToInt.0, @Int.0)
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @IntToInt = make_bad();
  use_it(@IntToInt.0, 1)
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""


@pytest.mark.parametrize("route", ["codegen_skip", "invariant_error"])
def test_exception_path_lift_skip_joins_blame_chain(
    monkeypatch: pytest.MonkeyPatch, route: str,
) -> None:
    """An exception ESCAPING `_lift_pending_closures` records the lift
    skip too (PR #1192 review round 4 + the outside-diff finding).

    `_compile_fn` has three lift-failure routes: the normal path (the
    lift returns ``closure_failed=True``), the degradation path (the lift
    raises `AdtEqNotDerivableError`/`CodegenSkip` — caught and degraded
    to a clean [E602]), and the compiler-bug path (the lift raises
    `CodegenInvariantError` — caught and surfaced as an [E699] error,
    with the module still assembled).  All three empty `_closure_table`,
    so all three must feed `_closure_lift_skips` for the #1185
    orphan-carrier blame chain; before the fix only the normal path did,
    and a carrier orphaned via either exception route drew the fallback
    [E620] wording — "this program creates no closure for it to hold" —
    a false claim about a program whose closure very much exists.

    No check-green surface program reaches either exception route today:
    a closure-BODY skip is caught inside `_compile_lifted_closure`
    (vera/codegen/closures.py) and returns through the normal path,
    non-Eq `==` is E243-gated at check time in both body and refinement
    position since #928, and `CodegenInvariantError` marks a compiler
    bug by definition.  The branches are backstops (#922's blanket
    sweep, #657's invariant surfacing), so this test exercises them
    directly: the fixture's closure is VALID, and the stub forces the
    raise for any function that has pending closures while delegating
    every closure-less function to the real lift.
    """
    from vera.codegen.core import CodeGenerator
    from vera.skip import CodegenInvariantError, CodegenSkip
    from vera.wasm import WasmContext

    real_lift = CodeGenerator._lift_pending_closures

    def raising_lift(self: CodeGenerator, ctx: WasmContext) -> bool:
        if ctx._pending_closures:
            if route == "codegen_skip":
                raise CodegenSkip(
                    ctx._pending_closures[0][0], "forced lift failure (test)"
                )
            raise CodegenInvariantError(
                "forced lift invariant failure (test)",
                ctx._pending_closures[0][0],
            )
        return real_lift(self, ctx)

    monkeypatch.setattr(CodeGenerator, "_lift_pending_closures", raising_lift)
    result = _compile(_VALID_CLOSURE_APPLY)

    # make_bad degrades to [E602] (or surfaces [E699]) through the
    # exception path; use_it's call_indirect is orphaned and must blame
    # make_bad as its root either way.
    _assert_call_indirect_iff_table(result.wat)
    assert "use_it" in result.dropped_fns
    use_it_e620 = next(
        d for d in result.diagnostics
        if d.error_code == "E620" and "'use_it'" in d.description
    )
    assert "make_bad" in use_it_e620.description, (
        "the orphaned carrier's [E620] must name the exception-path lift "
        "skip as its root, not claim the program creates no closure: "
        f"{use_it_e620.description}"
    )
    if route == "codegen_skip":
        # The [E602] degradation is warning-only: the surviving module
        # must still instantiate and the untouched export must run.
        _assert_no_raw_wat_error(result)
        assert execute(result, fn_name="ok").value == 41
    else:
        # The [E699] route emits an ERROR (a compiler-bug report), so
        # the warning-only helper does not apply — pin instead that the
        # carrier's [E620] cites the root's severity honestly.
        assert "[E699] diagnostic at" in use_it_e620.description
        assert any(
            d.error_code == "E699" and d.severity == "error"
            for d in result.diagnostics
        )
