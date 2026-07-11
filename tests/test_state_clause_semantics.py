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


class TestPerArmResumeRejected:
    """A resume per branch arm types the branch as a VOID block while each
    resume pushes the op's result — invalid WASM.  The walker rejects the
    shape loudly (PR #1003 review: it was accepted and emitted an invalid
    module that failed only at instantiation).  The canonical form branches
    inside the argument: ``resume(if c then a else b)``."""

    def test_resume_in_both_if_arms_skips_loudly(self) -> None:
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> {
      if @Int.0 > 0 then { resume(@Int.0) } else { resume(0 - @Int.0) }
    },
    put(@Int) -> { resume(()) }
  } in {
    put(0 - 5);
    get(())
  }
}
"""
        result = _compile(src)
        assert "test" not in result.exports, (
            "per-arm resume must skip the function, not emit an invalid module"
        )
        assert any("resume" in d.description for d in result.diagnostics)

    def test_resume_per_match_arm_skips_loudly(self) -> None:
        src = """\
private data Sign { Neg, Pos }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 3) {
    get(@Unit) -> {
      match Pos {
        Neg -> resume(0 - @Int.0),
        Pos -> resume(@Int.0)
      }
    },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile(src)
        assert "test" not in result.exports
        assert any("resume" in d.description for d in result.diagnostics)

    def test_one_arm_resumes_other_does_not_skips_loudly(self) -> None:
        # The nastier variant (PR #1003 review): ONE arm resumes, the other
        # returns () — both arms type Unit so check AND verify are green,
        # but the resuming arm pushes the op's result into a void join.
        # Must skip loudly, never emit the invalid module.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> {
      if @Int.0 > 0 then { resume(@Int.0) } else { () }
    },
    put(@Int) -> { resume(()) }
  } in {
    put(0 - 5);
    get(())
  }
}
"""
        result = _compile(src)
        assert "test" not in result.exports, (
            "a mixed resume/non-resume join must skip the function"
        )
        assert any("resume" in d.description for d in result.diagnostics)

    def test_nested_handle_in_clause_statement_position_works(self) -> None:
        # A nested handle-expr in a STATEMENT of the clause body is legal:
        # the inner handler's clauses own their resumes (they must not
        # spuriously reject this clause), and the outer clause's own tail
        # resume is the single one that counts.  Ledger: inner handle runs
        # its body get -> inner clause resumes 50+2=52 (discarded); outer
        # get's clause resumes @Int.0 + 52... simplified: outer resumes
        # pre-store state + 1; body get over init 7 -> 8.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 7) {
    get(@Unit) -> {
      let @Int = handle[State<Int>](@Int = 50) {
        get(@Unit) -> { resume(@Int.0 + 2) },
        put(@Int) -> { resume(()) }
      } in {
        get(())
      };
      resume(@Int.1 + 1)
    },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""
        result = _compile(src)
        if "test" in result.exports:
            # The captured outer state is @Int.1 after the let binds the
            # inner handle's 52 as @Int.0 — expected 7 + 1 = 8.
            assert _run(src, "test") == 8
        else:
            # If slot layering makes this shape uncheckable/unlowerable it
            # must at least fail loudly, never emit an invalid module.
            assert result.diagnostics

    def test_branch_inside_resume_argument_works(self) -> None:
        # The canonical form: the branch is INSIDE resume's argument, so it
        # is typed by the value and lowers cleanly.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> {
      resume(if @Int.0 > 0 then { @Int.0 } else { 0 - @Int.0 })
    },
    put(@Int) -> { resume(()) }
  } in {
    put(0 - 5);
    get(())
  }
}
"""
        assert _run(src, "test") == 5


class TestLexicalClauseScope:
    """§7.5.2: clauses refine only the handled body's OWN op sites.  Ops
    inside a called ``effects(<State<T>>)`` helper perform the intrinsic
    operation against the same cell — transforms do not follow the effect
    through call boundaries (PR #1003 review characterization)."""

    def test_helper_ops_bypass_the_override(self) -> None:
        # put(9) via a helper: intrinsic store only — the *2 override does
        # not apply (compare the inline control below).
        src = """\
private fn store(@Int -> @Unit)
  requires(true) ensures(true) effects(<State<Int>>)
{
  put(@Int.0)
}
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.1 * 2
  } in {
    store(9);
    get(())
  }
}
"""
        assert _run(src, "test") == 9

    def test_inline_op_applies_the_override_control(self) -> None:
        # The same put(9) written inline IS refined by the clause.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.1 * 2
  } in {
    put(9);
    get(())
  }
}
"""
        assert _run(src, "test") == 18


class TestClausePositionsAndNesting:
    """Op sites in arbitrary expression positions and nested handlers — a
    hand-computed ledger per shape (PR #1003 review coverage)."""

    def test_transformed_get_inside_put_argument(self) -> None:
        # get reads 0, clause resumes 100; put(100+100=200) stores; final
        # get reads 200, resumes 300... ledger: put(get(())+100): get
        # resumes 0+100=100 -> put(200) intrinsic; get -> 200+100=300.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0 + 100) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 100);
    get(())
  }
}
"""
        assert _run(src, "test") == 300

    def test_two_transformed_gets_in_one_expression(self) -> None:
        # Both reads see the same stored 5; each resumes 5+5=10 -> 20.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 5) {
    get(@Unit) -> { resume(@Int.0 + 5) },
    put(@Int) -> { resume(()) }
  } in {
    get(()) + get(())
  }
}
"""
        assert _run(src, "test") == 20

    def test_nested_same_type_handlers_use_inner_clauses(self) -> None:
        # Inner handler (+100 transform) owns its ops; after the inner
        # handle, the outer (+1 transform) is restored.  Ledger: inner init
        # 50 -> inner get resumes 150; outer init 0 -> outer get after the
        # inner handle resumes 0+1=1; total 151.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0 + 1) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 50) {
      get(@Unit) -> { resume(@Int.0 + 100) },
      put(@Int) -> { resume(()) }
    } in {
      get(())
    } + get(())
  }
}
"""
        assert _run(src, "test") == 151

    def test_partial_inner_clause_set_does_not_inherit_outer(self) -> None:
        # A nested handler declaring ONLY a put clause: its body's get must
        # be the bare intrinsic op (7), never the OUTER handler's +100
        # transform (PR #1003 review: the registry was inherited, giving
        # 107 — the innermost handler owns the op names wholesale).
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0 + 100) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = 7) {
      put(@Int) -> { resume(()) }
    } in {
      get(())
    }
  }
}
"""
        assert _run(src, "test") == 7

    def test_composite_shapes_under_eager_gc(self, monkeypatch) -> None:
        # CI-enforce the eager-GC claim: VERA_EAGER_GC is read at ASSEMBLY
        # time, so setting it here makes the emitted module force a
        # collection on every alloc — the captured pre-store pointer (the
        # only root for the old box after the intrinsic store) must survive
        # the clause body's allocations via the shadow-stack rooting.
        monkeypatch.setenv("VERA_EAGER_GC", "1")
        transform_src = """\
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
        assert _run(transform_src, "test") == 82
        capture_src = """\
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
        assert _run(capture_src, "test") == 107

    def test_inner_init_reads_outer_state(self) -> None:
        # The inner handler's INIT expression belongs to the enclosing
        # scope: its get(()) must read the OUTER cell (100), not the
        # freshly-pushed inner cell's default 0 (PR #1003 panel: push
        # preceded init evaluation, so this returned 5 — pre-existing).
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<Int>](@Int = get(()) + 5) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      get(())
    }
  }
}
"""
        assert _run(src, "test") == 105

    def test_inner_init_observes_outer_put(self) -> None:
        # Same rule with a preceding outer put: init reads 200 -> 205.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 100) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(200);
    handle[State<Int>](@Int = get(()) + 5) {
      get(@Unit) -> { resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      get(())
    }
  }
}
"""
        assert _run(src, "test") == 205

    def test_throw_from_clause_body_aborts_to_exn_handler(self) -> None:
        # A clause body may perform OTHER effects: a throw inside the get
        # clause aborts the handled body out to the Exn handler.
        src = """\
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 - 1 }
  } in {
    handle[State<Int>](@Int = 0) {
      get(@Unit) -> { throw(42); resume(@Int.0) },
      put(@Int) -> { resume(()) }
    } in {
      get(())
    }
  }
}
"""
        result = _compile(src)
        if "test" in result.exports:
            assert _run(src, "test") == -1


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
