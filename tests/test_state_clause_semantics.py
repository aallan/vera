"""#976 option C: ``handle[State<T>]`` clause bodies EXECUTE with
intrinsic-hybrid semantics.

The pinned semantics (maintainer decision on #976):

1. ``put(x)`` stores ``x`` intrinsically; ``get`` reads intrinsically —
   independent of the clauses.
2. The matching clause body executes; its ``resume(v)`` value IS the op's
   result at the call site.
3. ``with @T = <expr>`` OVERRIDES the intrinsic store.
4. The clause's state slot ``@T.0`` is captured BEFORE the intrinsic store,
   so ``with @T = @T.0`` means *keep the old state* — a meaningful override,
   not a no-op.

Before this fix the clauses were type-checked but never lowered
(``_translate_handle_state`` read neither ``expr.clauses`` nor
``state_update``): every op compiled to the bare host-cell call, so a
transforming clause was silently discarded.  Slot reminder (DE_BRUIJN):
in a ``put(@Int)`` clause the state is ``@Int.0`` (bound last) and the put
ARGUMENT is ``@Int.1``.
"""

from __future__ import annotations

from tests.codegen_helpers import _compile, _run


class TestClauseTransformsResume:
    def test_get_clause_transforms_resume_argument(self) -> None:
        # Intrinsic read gives 5; the clause resumes 5 + 100 -> the op's
        # result is 105.  (Pre-fix: clause dropped, get returned 5.)
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0 + 100) },
    put(@Int) -> { resume(()) }
  } in {
    put(5);
    get(())
  }
}
"""
        assert _run(src, "test") == 105

    def test_get_clause_transform_of_initial_value(self) -> None:
        # No put: intrinsic read gives the init 10, clause resumes 30.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 10) {
    get(@Unit) -> { resume(@Int.0 * 3) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        assert _run(src, "test") == 30


class TestWithOverride:
    def test_with_overrides_the_intrinsic_store(self) -> None:
        # put(5): intrinsic store 5, then the override stores @Int.1 * 2 = 10
        # (@Int.1 is the put ARGUMENT; @Int.0 is the pre-store state).
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.1 * 2
  } in {
    put(5);
    get(())
  }
}
"""
        assert _run(src, "test") == 10

    def test_with_keep_old_state(self) -> None:
        # THE CANARY: @Int.0 is captured pre-store, so `with @Int = @Int.0`
        # reverts the put — state stays at the init 7.  This is exactly why
        # the corpus's redundant `with @Int = @Int.0` clauses are migrated to
        # the canonical no-`with` form in this PR.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 7) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    put(99);
    get(())
  }
}
"""
        assert _run(src, "test") == 7


class TestCompositeState:
    """Heap-typed state: the captured pre-store pointer and allocating
    clause bodies compose (probed green under VERA_EAGER_GC too)."""

    def test_transform_and_override_on_composite(self) -> None:
        # put(MkBox(10)): intrinsic store, then override to MkBox(41);
        # get: intrinsic read MkBox(41), clause resumes MkBox(82).
        src = """\
private data Box { MkBox(Int) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Box>](@Box = MkBox(3)) {
    get(@Unit) -> {
      match @Box.0 {
        MkBox(@Int) -> resume(MkBox(@Int.0 * 2))
      }
    },
    put(@Box) -> { resume(()) } with @Box = MkBox(41)
  } in {
    put(MkBox(10));
    match get(()) {
      MkBox(@Int) -> @Int.0
    }
  }
}
"""
        assert _run(src, "test") == 82

    def test_captured_pointer_read_after_alloc(self) -> None:
        # The override reads the CAPTURED pre-store box (@Box.0) AFTER an
        # allocation (MkBox(100) evaluates first) — the pre-store box is no
        # longer reachable from the host cell at that point, so this pins
        # the capture local staying valid across clause-body allocation.
        src = """\
private data Box { MkBox(Int) }
private fn unwrap(@Box -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Box.0 {
    MkBox(@Int) -> @Int.0
  }
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Box>](@Box = MkBox(7)) {
    get(@Unit) -> { resume(@Box.0) },
    put(@Box) -> { resume(()) } with @Box = MkBox(unwrap(MkBox(100)) + unwrap(@Box.0))
  } in {
    put(MkBox(50));
    match get(()) {
      MkBox(@Int) -> @Int.0
    }
  }
}
"""
        assert _run(src, "test") == 107


class TestNonTailResumeRejected:
    def test_non_tail_resume_skips_loudly(self) -> None:
        # A resume followed by more statements is not lowerable single-shot:
        # the function is skipped with a diagnostic (loud), never compiled
        # with silently-wrong semantics.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0); 5 },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile(src)
        assert "test" not in result.exports, (
            "a non-tail resume must skip the function, not compile it with "
            "wrong single-shot semantics"
        )
        assert any(
            "resume" in d.description for d in result.diagnostics
        ), f"expected a resume diagnostic: {[d.description for d in result.diagnostics]}"


class TestCanonicalUnchanged:
    """The canonical clauses are identity transforms under option C — these
    pin that the new lowering changes nothing for the corpus idiom."""

    def test_canonical_put_get(self) -> None:
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(99);
    get(())
  }
}
"""
        assert _run(src, "test") == 99

    def test_spec_753_anchor(self) -> None:
        # The spec §7.5.3 example: init 0, three increments -> 10 after
        # put(10) sequence semantics... the anchor pins the spec's stated
        # result for the canonical counter.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 4);
    put(get(()) + 6);
    get(())
  }
}
"""
        assert _run(src, "test") == 10
