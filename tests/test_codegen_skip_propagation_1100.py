"""Tests for #1100 — a codegen skip propagates to (transitive) callers.

When ``_compile_fn`` drops a function (an ``[E602]``-class skip), every
caller's ``call $f`` / ``return_call $f`` used to survive into the assembled
module, so a check- and verify-clean program whose skipped construct sits in
a *called* helper failed at ``compile``/``run`` with a raw wasmtime ``WAT
compilation failed: unknown func`` error instead of a source-located
diagnostic.  Loud, never a wrong answer — but the user saw WAT internals,
not Vera diagnostics.

The fix propagates the skip to the whole unreachable caller subgraph before
module assembly: each transitively-dropped caller gets its own [E620]
warning naming the ROOT skipped function and its skip location, the doomed
WAT is pruned (closure bodies are stubbed to keep function-table indices
stable), and every export OUTSIDE the subgraph is untouched.

Every fixture uses a ``Map<String, Array<Int>>`` value to trigger the root
[E602] skip (an Array-valued Map is an unsupported host-import shape); any
E602-skippable construct reproduces the class.  The sibling ``ok()``
returns 41 — a value no fallback path produces — so a green run proves the
sibling's own body executed.
"""
from __future__ import annotations


from vera.codegen import CompileResult, execute
from tests.codegen_helpers import _assert_no_raw_wat_error
from vera.errors import Diagnostic

from tests.codegen_helpers import _compile

# The root-cause fixture: an E602-skippable construct inside a PRIVATE
# helper, called by main.  `vera check` and `vera verify` are clean; the
# failure class is codegen-only.
_SKIPPED_HELPER = """\
private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0)
}
"""


def _e620s(result: CompileResult) -> list[Diagnostic]:
    return [d for d in result.diagnostics if d.error_code == "E620"]


class TestSkipPropagation1100:
    """Direct and transitive caller drops for an E602-skipped callee."""

    def test_helper_skip_caller_gets_clean_diagnostic(self) -> None:
        """The #1100 repro: helper skipped, `main` calls it.

        Pre-fix this failed WAT assembly with ``unknown func: failed to
        find name $tally``; post-fix the module assembles, `main` is
        dropped from the exports, and a [E620] warning names the caller.
        """
        source = _SKIPPED_HELPER + """
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  tally()
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        assert "main" not in result.exports, (
            "a caller of a skipped function cannot be emitted"
        )
        # The ROOT skip warning survives untouched alongside the drop.
        assert any(
            d.error_code == "E602" and "'tally'" in d.description
            for d in result.diagnostics
        ), "the root [E602] skip warning must not be suppressed"
        e620 = _e620s(result)
        assert len(e620) == 1, f"expected exactly one caller drop, got {e620}"
        assert e620[0].severity == "warning"
        assert e620[0].description.startswith("Function 'main' ")
        assert "'tally'" in e620[0].description

    def test_depth_two_transitive_drop(self) -> None:
        """main -> mid -> sunk (skipped): BOTH callers drop, each E620
        naming the ROOT (`sunk`), not merely the next hop.

        Pre-fix: raw ``unknown func: $sunk``.  Both declaration
        PERMUTATIONS are compiled: callee-first resolves in one sweep of
        the emission-ordered node list, but caller-first (`main` declared
        before `mid`) needs a second fixed-point round — a propagation
        that stops after one sweep leaves main's ``call $mid`` dangling
        and goes RED on that permutation.
        """
        decls = {
            "sunk": """\
private fn sunk(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0)
}
""",
            "mid": """\
private fn mid(-> @Int) requires(true) ensures(true) effects(pure) {
  sunk() + 1
}
""",
            "main": """\
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  mid() + 1
}
""",
        }
        for order in (("sunk", "mid", "main"), ("main", "mid", "sunk")):
            source = "\n".join(decls[name] for name in order)
            result = _compile(source)
            _assert_no_raw_wat_error(result)
            assert "main" not in result.exports
            e620 = _e620s(result)
            # Count before set-projection: a duplicated E620 for the same
            # caller would vanish into the set (PR review).
            assert len(e620) == 2, (
                f"exactly one E620 per dropped caller in order {order}, "
                f"got {[d.description for d in e620]}"
            )
            dropped = {d.description.split("'")[1] for d in e620}
            assert dropped == {"mid", "main"}, (
                f"both transitive callers must drop in order {order}, "
                f"got {dropped}"
            )
            for d in e620:
                assert "'sunk'" in d.description, (
                    f"the E620 must name the ROOT skipped function: "
                    f"{d.description}"
                )

    def test_diagnostic_names_root_cause_and_location(self) -> None:
        """The E620 embeds the root skip's code and source location, so
        the user can jump from the dropped caller to the actual
        unsupported construct."""
        source = _SKIPPED_HELPER + """
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  tally()
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        (e620,) = _e620s(result)
        root = next(
            d for d in result.diagnostics
            if d.error_code == "E602" and "'tally'" in d.description
        )
        # The root E602 points at the unsupported construct (the Map let
        # on line 2); the E620 must carry that same location in its text.
        assert root.location.line == 2
        assert "[E602]" in e620.description
        assert f"line {root.location.line}" in e620.description
        assert e620.rationale, "E620 must carry a rationale"
        # The E620 itself points at the dropped CALLER's declaration.
        assert e620.location.line == 6

    def test_sibling_export_untouched_and_runs(self) -> None:
        """No over-skipping: a public sibling OUTSIDE the doomed subgraph
        keeps its export and still executes end-to-end."""
        source = _SKIPPED_HELPER + """
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  tally()
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        assert "ok" in result.exports
        assert "main" not in result.exports
        assert not any(
            "'ok'" in d.description for d in _e620s(result)
        ), "the sibling must not be named by any drop diagnostic"
        exec_result = execute(result, fn_name="ok")
        assert exec_result.value == 41

    def test_mutual_recursion_terminates_and_drops(self) -> None:
        """A mutually-recursive pair (ping <-> pong) where one member also
        calls the skipped helper: propagation must reach a fixed point
        (not loop on the cycle) and drop the pair plus `main`, while the
        sibling still runs."""
        source = """\
private fn sunk(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);
  map_size(@Map<String, Array<Int>>.0)
}

private fn ping(@Nat -> @Int) requires(true) ensures(true) decreases(@Nat.0) effects(pure) {
  if @Nat.0 == 0 then { sunk() } else { pong(@Nat.0 - 1) }
}

private fn pong(@Nat -> @Int) requires(true) ensures(true) decreases(@Nat.0) effects(pure) {
  if @Nat.0 == 0 then { 0 } else { ping(@Nat.0 - 1) }
}

public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  ping(3)
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        e620 = _e620s(result)
        # Count before set-projection (PR review): the cycle must produce
        # exactly one E620 per dropped caller, not re-emit on revisits.
        assert len(e620) == 3, (
            f"got {[d.description for d in e620]}"
        )
        dropped = {d.description.split("'")[1] for d in e620}
        assert dropped == {"ping", "pong", "main"}
        for d in e620:
            assert "'sunk'" in d.description
        assert result.exports == ["ok"]
        assert execute(result, fn_name="ok").value == 41

    def test_mono_mangled_caller_drops_with_e620(self) -> None:
        """A GENERIC caller instantiated at a concrete type: the
        mono-mangled clone is what actually calls the skipped helper in
        the emitted module, so the propagation's WAT-symbol matching
        must drop the CLONE (and its transitive callers) with an E620
        naming the skipped root — the mangled-name path, not just bare
        top-level names (PR review)."""
        source = _SKIPPED_HELPER + """\
private forall<T> fn relay(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  tally()
}

public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  relay("x")
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        assert "main" not in result.exports, (
            "main reaches tally through the relay clone and must drop"
        )
        e620 = _e620s(result)
        # Position, not presence: main's own E620 also contains both
        # 'relay$String' and 'tally' ("main calls relay$String, which was
        # dropped because tally was skipped"), so a substring test would
        # pass with the clone's OWN diagnostic missing.  Anchor on the
        # clone as the diagnostic's subject.
        assert any(
            d.description.startswith("Function 'relay$String' ")
            and "'tally'" in d.description
            for d in e620
        ), (
            "the mono-mangled clone must carry its OWN E620 naming the "
            f"skipped root, got: {[d.description for d in e620]}"
        )
        assert execute(result, fn_name="ok").value == 41

    def test_closure_calling_skipped_helper(self) -> None:
        """A lifted closure whose body calls the skipped helper: the
        dangling ``call`` lives in the CLOSURE's WAT (the parent only
        holds a table index), so the parent must drop via the
        closure-parent edge and the closure body must be stubbed — the
        function-table indices of later closures depend on its slot.

        Pre-fix: raw ``unknown func: $tally`` from the closure body.
        """
        source = _SKIPPED_HELPER + """
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { tally() + @Int.0 });
  array_length(@Array<Int>.0)
}

public fn ok(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}

public fn later(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Array<Int> = array_map([1, 2, 3], fn(@Int -> @Int) effects(pure) { @Int.0 + 10 });
  array_length(@Array<Int>.0) + 38
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        assert "main" not in result.exports
        e620 = _e620s(result)
        assert len(e620) == 1
        assert e620[0].description.startswith("Function 'main' ")
        assert "closure" in e620[0].description
        assert "'tally'" in e620[0].description
        assert execute(result, fn_name="ok").value == 41
        # PR review: the doomed closure is STUBBED, not removed, so a
        # LATER function's closure keeps its own table slot and still
        # dispatches through call_indirect.  With one closure in the
        # fixture, removal-instead-of-stubbing satisfied every earlier
        # assertion — this pins the index-preservation property the
        # stub exists for (kills the drop-the-stub mutant on position,
        # not just on the dangling-call property).
        assert execute(result, fn_name="later").value == 41

    def test_no_callers_no_propagation(self) -> None:
        """Control (green pre- and post-fix): a skipped function with NO
        callers keeps today's behaviour — one root [E602], no [E620], and
        the unrelated `main` compiles, exports, and runs.  Guards against
        over-skipping."""
        source = _SKIPPED_HELPER + """
public fn main(-> @Int) requires(true) ensures(true) effects(pure) {
  41
}
"""
        result = _compile(source)
        _assert_no_raw_wat_error(result)
        assert result.exports == ["main"]
        assert not _e620s(result)
        assert any(d.error_code == "E602" for d in result.diagnostics)
        assert execute(result).value == 41
