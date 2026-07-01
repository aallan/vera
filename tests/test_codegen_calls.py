"""Tests for vera.codegen — calls (statement-position unit calls, tail-call optimization, pair-typed closure params and captures).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re


from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile_ok,
    _run,
    _run_io,
)


class TestUserUnitFnInStatementPosition556:
    """#556 — calling a user-defined ``@Unit``-returning function in
    statement position (followed by ``;`` and a separate final
    expression) used to fail WASM validation with ``type mismatch:
    expected a type but nothing on stack``.

    The user-visible bug class was actually closed by #584's fix in
    v0.0.135 (``_is_void_expr`` in ``vera/wasm/context.py`` now
    recognises user-defined ``@Unit`` fns via the ``_fn_ret_types``
    registry).  But the specific repro shape from #556 — a *pure*
    helper (no IO effect) followed by a unit-literal final expression,
    rather than another effectful statement — wasn't pinned by the
    existing conformance test ``ch07_unit_fn_nontail.vera`` (which
    covers IO-effect variants).  This class adds the missing
    coverage so the exact #556 repro can't silently regress.
    """

    def test_pure_unit_helper_then_unit_literal(self) -> None:
        """The exact repro from issue #556: a pure ``@Unit``-returning
        helper called in statement position, followed by a trailing
        ``()`` as the block's final expression.  Both ``check`` and
        ``compile`` must succeed; the resulting WAT must call the
        helper and not emit a stray ``drop``.
        """
        source = """\
private fn pure_helper(@Nat -> @Unit)
  requires(true) ensures(true) effects(pure)
{
  ()
}

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  pure_helper(1);
  ()
}
"""
        result = _compile_ok(source)
        # The helper must be called.
        assert "call $pure_helper" in result.wat, (
            f"Expected `call $pure_helper` in WAT; got:\n{result.wat}"
        )
        # No stray drop on the Unit-returning call — that's what
        # tripped the validator pre-#584.
        main_func = result.wat.split('(func $main')[1].split('(func ')[0]
        assert "drop" not in main_func, (
            f"Expected no `drop` in `$main` (Unit-returning user fn "
            f"in statement position must not leave a stack value "
            f"that needs dropping).  $main body:\n{main_func}"
        )

    def test_pure_unit_helper_in_where_block(self) -> None:
        """The where-block variant reported in the #556 follow-up
        comment: helper lives in a ``where { ... }`` block, called in
        statement position, followed by a unit-literal.  Same shape,
        same fix.
        """
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  helper(1);
  ()
}
where {
  fn helper(@Nat -> @Unit)
    requires(true) ensures(true) effects(<IO>)
  {
    IO.print(nat_to_string(@Nat.0))
  }
}
"""
        # Runs end-to-end — exercises the full pipeline including
        # where-block hoisting, so a regression in either layer
        # (Unit-fn detection or where-block name resolution) is
        # caught.
        assert _run_io(source, fn="main") == "1"


class TestTailCallOptimization517:
    """#517 — WASM `return_call` emission for tail-position calls.

    Pre-fix, every Vera ``call`` site emitted plain WASM ``call``
    regardless of tail-position status, so a tail-recursive function
    pushed one WASM frame per iteration and trapped with "call stack
    exhausted" at ~tens of thousands of frames.  The documented
    "iteration is tail recursion" idiom from `SKILL.md` thus
    silently failed past ~5-10K iterations.

    The fix is a per-fn analyzer (`vera/codegen/tail_position.py`)
    that marks `id(FnCall)` AST nodes in syntactic tail position;
    `_translate_call` emits ``return_call $foo`` instead of
    ``call $foo`` when the call's id is in the marked set AND the
    callee's WASM return type matches the caller's (required for
    WASM `return_call` semantics — the signature must match).

    Initially, allocating functions reverted ``return_call`` →
    ``call`` in a post-process step because `return_call` discards
    the current frame and skips the GC epilogue, leaking shadow-
    stack slots.  #549 replaces that fallback with a GC-aware
    variant: the post-process now PREPENDS
    ``local.get $gc_sp_save; global.set $gc_sp`` before each
    ``return_call``, restoring the shadow-stack pointer to the
    caller's entry baseline so the callee's prologue saves a clean
    new baseline.  Args are already on the WASM operand stack at
    the return_call site; the restore only touches the
    ``$gc_sp`` global, so args transfer atomically to the callee.

    Functions with a non-trivial runtime postcondition STILL revert
    ``return_call`` → ``call`` (the postcondition check runs after
    the call returns; ``return_call`` would skip it).
    """

    def test_tail_recursive_iteration_succeeds_at_50k(self) -> None:
        """The canonical 50K-iteration loop runs to completion."""
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(50000))
}
"""
        # Pre-fix this trapped at ~30K iterations on the WASM stack.
        # Post-fix, return_call keeps the stack flat and the function
        # returns 0 cleanly.
        assert _run(source, fn="f") == 0

    def test_tail_recursive_iteration_succeeds_at_1m(self) -> None:
        """Stress test: 1M iterations also runs to completion.

        The pre-fix bug was at ~30K WASM frames (default wasmtime
        stack size).  Post-fix, the only constraint is wall-clock
        time — 1M iterations of a single arithmetic op completes in
        well under a second.  This test exists to pin "iteration in
        constant stack space" rather than just "iteration deeper
        than the broken limit", so a future regression that
        reintroduced linear stack growth would fail here even if it
        happened to push the limit higher than 50K.
        """
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(1000000))
}
"""
        assert _run(source, fn="f") == 0

    def test_return_call_emitted_for_tail_position_call(self) -> None:
        """Structural: tail-recursive call site emits `return_call`."""
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(10))
}
"""
        result = _compile_ok(source)
        # The recursive call inside the else branch is in tail
        # position (it's the trailing expression of the else-block,
        # which is the trailing expression of the if, which is the
        # trailing expression of the function body).  The non-
        # tail call to nat_to_int below is also in tail position
        # in `f`, but nat_to_int is a host-translator builtin
        # without a WAT $-prefixed name, so it doesn't get the
        # return_call treatment.  count_down's recursive call
        # does — assert at least one return_call emission.
        assert "return_call $count_down" in result.wat, (
            f"Expected return_call $count_down in WAT.  WAT excerpt:\n"
            f"{result.wat[:2000]}"
        )

    def test_no_return_call_for_non_tail_position(self) -> None:
        """Structural: a call bound by `let` is NOT in tail position.

        Sibling regression to the `return_call` emission test
        above.  The analyzer must NOT mark calls in non-tail
        positions; otherwise WASM `return_call` would discard the
        caller's frame and the let-binding would lose access to
        the result it needs to bind.
        """
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true) ensures(true) decreases(@Nat.0) effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn caller(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Nat = count_down(10);
  @Nat.0 + 1
}
"""
        result = _compile_ok(source)
        # In `caller`, the call to `count_down(10)` is the value of
        # a let binding — NOT tail position.  The trailing
        # `@Nat.0 + 1` consumes the bound value.  Assert that the
        # WAT contains a plain `call $count_down` from `caller`
        # AND a `return_call $count_down` from the recursive call
        # inside count_down's else-branch.  Both must coexist.
        assert "call $count_down" in result.wat
        # Look for the let-bound call: it should be plain `call`,
        # not `return_call`.  Find the function body of `caller`
        # and inspect.
        f_body_start = result.wat.find("(func $caller")
        assert f_body_start >= 0, "caller function not found in WAT"
        f_body_end = result.wat.find("(func ", f_body_start + 1)
        if f_body_end < 0:
            f_body_end = len(result.wat)
        caller_body = result.wat[f_body_start:f_body_end]
        # Inside caller's body, the count_down call must be plain
        # `call`, never `return_call`.  Pre-fix safety: a buggy
        # analyzer that marked non-tail calls would emit
        # `return_call $count_down` here and the let-binding
        # would lose its value.
        assert "return_call $count_down" not in caller_body, (
            f"caller's count_down call should NOT be return_call "
            f"(it's bound by `let`, NOT tail position).  Body:\n"
            f"{caller_body}"
        )
        # Positive sibling assertion — `count_down`'s recursive call
        # IS in tail position (the trailing expression of the
        # else-branch, transitively the trailing expression of the
        # function body via `if`-transparency), so the optimization
        # must fire there even though it doesn't fire in `caller`.
        # Without this check, a buggy analyzer that marked NOTHING
        # would silently pass `assert "return_call $count_down" not
        # in caller_body` while regressing the actual TCO behaviour.
        cd_body_start = result.wat.find("(func $count_down")
        assert cd_body_start >= 0, "count_down function not found"
        cd_body_end = result.wat.find("(func ", cd_body_start + 1)
        if cd_body_end < 0:
            cd_body_end = len(result.wat)
        count_down_body = result.wat[cd_body_start:cd_body_end]
        assert "return_call $count_down" in count_down_body, (
            f"count_down's recursive call should be return_call "
            f"(tail position via if-else transparency).  Body:\n"
            f"{count_down_body}"
        )

    def test_postcondition_function_falls_back_to_plain_call(self) -> None:
        """A function with a non-trivial `ensures` reverts return_call.

        Postcondition checks emit instructions AFTER the function
        body in the WAT assembly (`local.set $ret`, condition
        check, trap on failure, `local.get $ret` to push back).
        WASM `return_call` discards the current frame and skips
        all of those — silently violating the contract.

        The fallback in `_compile_fn` reverts every `return_call`
        → `call` when `post_instrs` is non-empty (CodeRabbit
        finding on PR #550 round 2).  Pre-fix this would have
        shipped as a soundness hole: a tail-recursive function
        with a runtime postcondition would skip the postcondition
        check on every iteration and the contract would silently
        fail.  Trivial postconditions like `ensures(true)` are
        elided by `_compile_postconditions` and don't trigger the
        fallback (no instructions are emitted, so nothing is
        skipped).
        """
        # A function with a non-trivial postcondition.  The
        # ensures clause (`@Nat.result >= 0`) is trivially true
        # for `@Nat` (refinement-typed non-negative), but the
        # codegen treats any non-`true` ensures as non-trivial
        # and emits the runtime check.
        source = """\
private fn count_down(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 } else { count_down(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(count_down(10))
}
"""
        result = _compile_ok(source)
        cd_body_start = result.wat.find("(func $count_down")
        assert cd_body_start >= 0
        cd_body_end = result.wat.find("(func ", cd_body_start + 1)
        if cd_body_end < 0:
            cd_body_end = len(result.wat)
        count_down_body = result.wat[cd_body_start:cd_body_end]
        # The recursive call is in syntactic tail position, so the
        # analyzer MARKS it.  But the postcondition check needs to
        # run after every recursive call's return — `return_call`
        # would skip it.  Post-process must have reverted the
        # emission to plain `call`.
        assert "call $count_down" in count_down_body
        assert "return_call $count_down" not in count_down_body, (
            f"count_down has a non-trivial postcondition (ensures "
            f"@Nat.result >= 0); return_call would skip the runtime "
            f"check.  Post-process should have reverted to plain "
            f"call.  Body:\n{count_down_body}"
        )

    def test_allocating_function_uses_gc_aware_tco_549(self) -> None:
        """#549: allocating fns emit `return_call` + $gc_sp restore.

        WASM `return_call` discards the current frame, which means
        the GC epilogue (restore `$gc_sp`, unwind shadow stack)
        never runs.  For an allocating function with tail calls,
        that would leak shadow-stack slots once per iteration and
        trap on the next `$alloc` once gc_sp passes the worklist
        boundary.

        Pre-#549: the post-process reverted every `return_call` →
        `call` when `ctx.needs_alloc` was True, sacrificing WASM
        call-stack depth (tail recursion eventually trapped with
        `call stack exhausted`) so the GC epilogue could run and
        bound shadow-stack usage.

        Post-#549: the post-process instead PREPENDS a `$gc_sp`
        restore (`local.get $gc_sp_save; global.set $gc_sp`)
        immediately before each `return_call`, so the callee's
        prologue saves a clean new baseline and the shadow stack
        stays bounded across iterations.  Args are already on the
        WASM operand stack at the return_call site; the restore
        only touches the `$gc_sp` global, so args transfer
        atomically to the callee.

        This test pins the new contract: an allocating function
        with a tail call must emit `return_call $foo` PRECEDED by
        the `$gc_sp` restore sequence.
        """
        # Function that allocates (constructor call) AND has a
        # tail-recursive call shape.  The analyzer marks the
        # recursive call as tail-position; the post-process
        # patches the emission because needs_alloc is True.
        source = """\
private data Box { MkBox(Int) }

private fn build(@Int -> @Box)
  requires(true) ensures(true) decreases(@Int.0) effects(pure)
{
  if @Int.0 == 0 then { MkBox(0) } else { build(@Int.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match build(3) { MkBox(@Int) -> @Int.0 }
}
"""
        result = _compile_ok(source)
        # build allocates (the MkBox constructor) AND has a tail-
        # recursive call.  Post-process must have KEPT the
        # `return_call $build` (TCO preserved) but prepended the
        # $gc_sp restore (shadow-stack invariant preserved).
        #
        # Use boundary-safe regex (\b after `$build`) so a future
        # symbol like `$build_helper` couldn't false-match these
        # checks.  WAT symbol chars are `[A-Za-z0-9_]` plus `$`;
        # `\b` correctly excludes `$build_x` while still matching
        # `$build ` or `$build(`.
        build_match = re.search(r"\(func \$build\b", result.wat)
        assert build_match is not None, (
            "Could not locate `(func $build` in WAT"
        )
        build_start = build_match.start()
        next_fn = re.search(r"\(func \$", result.wat[build_start + 1:])
        build_end = (
            build_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        build_body = result.wat[build_start:build_end]
        assert re.search(r"return_call \$build\b", build_body), (
            f"Allocating function `build` did not emit return_call. "
            f"#549's GC-aware TCO should preserve return_call for "
            f"allocating fns. Body:\n{build_body}"
        )
        # Parse the GC prologue to capture the exact local index
        # that holds $gc_sp_save.  The prologue is the two
        # instructions that open every allocating function:
        #     global.get $gc_sp
        #     local.set <N>
        # The preamble at each return_call site must reload from
        # this SAME local — anything else (a typo, a wrong index
        # picked up from an unrelated local-alloc) would leave the
        # callee's prologue saving an inconsistent baseline.
        lines = build_body.splitlines()
        prologue_get_idx = next(
            (i for i, ln in enumerate(lines)
             if ln.strip() == "global.get $gc_sp"),
            None,
        )
        assert prologue_get_idx is not None, (
            f"no `global.get $gc_sp` prologue found in build body. "
            f"Body:\n{build_body}"
        )
        prologue_set = lines[prologue_get_idx + 1].strip()
        assert prologue_set.startswith("local.set "), (
            f"expected `local.set <N>` immediately after the "
            f"prologue's `global.get $gc_sp`, got: {prologue_set!r}. "
            f"Body:\n{build_body}"
        )
        gc_sp_save_local = prologue_set[len("local.set "):]
        expected_preamble_get = f"local.get {gc_sp_save_local}"
        # Find every `return_call $build` site and verify the two
        # instructions immediately before it are the exact preamble:
        #     local.get <gc_sp_save_local>
        #     global.set $gc_sp
        return_call_indices = [
            i for i, line in enumerate(lines)
            if re.search(r"return_call \$build\b", line)
        ]
        assert return_call_indices, "no return_call $build site found"
        for idx in return_call_indices:
            assert idx >= 2, (
                f"return_call at line {idx} has no room for the "
                f"$gc_sp restore preamble. Body:\n{build_body}"
            )
            prev1 = lines[idx - 1].strip()
            prev2 = lines[idx - 2].strip()
            assert prev1 == "global.set $gc_sp", (
                f"Expected 'global.set $gc_sp' immediately before "
                f"return_call at line {idx}, got: {prev1!r}. "
                f"Body:\n{build_body}"
            )
            assert prev2 == expected_preamble_get, (
                f"Expected exact preamble '{expected_preamble_get}' "
                f"(matching the GC prologue's saved local) two lines "
                f"before return_call at line {idx}, got: {prev2!r}. "
                f"Body:\n{build_body}"
            )

    def test_allocating_function_gc_aware_tco_patches_both_branches(
        self,
    ) -> None:
        """#549: every tail-position `return_call` gets the preamble.

        The single-branch test above pins that the patch fires at
        a single tail-recursive call site.  This test pins that
        the patch loop fires at MULTIPLE sites in the same
        function — a buggy implementation that bails after the
        first match (e.g. `break` inside the patch loop) or that
        only handles top-level emissions but not if/else-nested
        ones would still pass the single-branch test.

        The function below uses a `match` with two ADT arms, each
        ending in a tail-recursive `build` call.  The analyzer
        marks both arms as tail position (see
        `test_analyzer_marks_match_arm_bodies`), so the codegen
        emits two `return_call $build` sites with DIFFERENT
        leading-whitespace prefixes (one for each match arm).
        Both must have the `local.get N; global.set $gc_sp`
        preamble; the local index N must be the same one captured
        by the GC prologue.
        """
        source = """\
private data Choice { Left, Right }

private fn build(@Int, @Choice -> @Array<Int>)
  requires(@Int.0 >= 0) ensures(true) decreases(@Int.0) effects(pure)
{
  if @Int.0 == 0 then { [0] }
  else {
    match @Choice.0 {
      Left -> build(@Int.0 - 1, Left),
      Right -> build(@Int.0 - 1, Right)
    }
  }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  array_length(build(3, Left))
}
"""
        result = _compile_ok(source)
        build_match = re.search(r"\(func \$build\b", result.wat)
        assert build_match is not None, (
            "Could not locate `(func $build` in WAT"
        )
        build_start = build_match.start()
        next_fn = re.search(r"\(func \$", result.wat[build_start + 1:])
        build_end = (
            build_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        build_body = result.wat[build_start:build_end]
        # Capture the exact $gc_sp_save local from the prologue.
        lines = build_body.splitlines()
        prologue_get_idx = next(
            (i for i, ln in enumerate(lines)
             if ln.strip() == "global.get $gc_sp"),
            None,
        )
        assert prologue_get_idx is not None, (
            f"no `global.get $gc_sp` prologue.  Body:\n{build_body}"
        )
        prologue_set = lines[prologue_get_idx + 1].strip()
        assert prologue_set.startswith("local.set ")
        gc_sp_save_local = prologue_set[len("local.set "):]
        expected_preamble_get = f"local.get {gc_sp_save_local}"
        # Find every return_call site and require the same
        # preamble at each.  This catches a regression where the
        # patch only fires on the first site (e.g. accidental
        # `break`) or where only a subset of nested positions get
        # the restore.
        return_call_indices = [
            i for i, line in enumerate(lines)
            if re.search(r"return_call \$build\b", line)
        ]
        assert len(return_call_indices) >= 2, (
            f"Expected at least 2 return_call sites (one per "
            f"match arm), got {len(return_call_indices)}.  "
            f"Body:\n{build_body}"
        )
        for idx in return_call_indices:
            assert idx >= 2, (
                f"return_call at line {idx} has no room for "
                f"preamble.  Body:\n{build_body}"
            )
            prev1 = lines[idx - 1].strip()
            prev2 = lines[idx - 2].strip()
            assert prev1 == "global.set $gc_sp", (
                f"site {idx} missing `global.set $gc_sp`; got "
                f"{prev1!r}.  Body:\n{build_body}"
            )
            assert prev2 == expected_preamble_get, (
                f"site {idx} preamble mismatch: expected "
                f"{expected_preamble_get!r}, got {prev2!r}.  "
                f"Both return_call sites must reload the SAME "
                f"local that the prologue saved.  Body:\n"
                f"{build_body}"
            )

    def test_allocating_function_with_postcondition_still_reverts(
        self,
    ) -> None:
        """Postcondition-bearing allocating fns still revert to call.

        The GC-aware TCO patch from #549 covers the
        ``needs_alloc and not post_instrs`` case.  When the
        function carries a non-trivial runtime postcondition
        check, the post-process still reverts ``return_call`` →
        ``call`` because the postcondition check needs to run
        after the call returns — ``return_call`` would skip it.

        This pins the precedence: post_instrs revert takes priority
        over the GC-aware patch.  The function below both allocates
        (the array literal in the base case sets needs_alloc) AND
        carries a runtime postcondition (`@Int.result >= 0`).  The
        post-process must therefore revert to plain ``call``, even
        though #549's path would otherwise patch in a GC restore.
        """
        source = """\
private fn build(@Nat -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  -- Base case allocates an array literal (sets needs_alloc on
  -- the codegen context); recursive case is in tail position.
  if @Nat.0 == 0 then { array_length([0, 0, 0]) }
  else { build(@Nat.0 - 1) }
}

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  build(3)
}
"""
        result = _compile_ok(source)
        # Boundary-safe extraction (\b after `$build`) — see the
        # rationale in test_allocating_function_uses_gc_aware_tco_549
        # above.
        build_match = re.search(r"\(func \$build\b", result.wat)
        assert build_match is not None, (
            "Could not locate `(func $build` in WAT"
        )
        build_start = build_match.start()
        next_fn = re.search(r"\(func \$", result.wat[build_start + 1:])
        build_end = (
            build_start + 1 + next_fn.start()
            if next_fn is not None
            else len(result.wat)
        )
        build_body = result.wat[build_start:build_end]
        # post_instrs are present, so return_call must revert to
        # plain call (so the postcondition check actually runs).
        # `\bcall \$build\b` rules out both `return_call` (leading
        # `\b` requires non-word char before `c`) AND `$build_x`
        # (trailing `\b` requires non-word char after `d`).
        assert re.search(r"\bcall \$build\b", build_body), (
            f"Expected plain `call $build` in post-revert body. "
            f"Body:\n{build_body}"
        )
        assert not re.search(r"return_call \$build\b", build_body), (
            f"build has a runtime postcondition; return_call would "
            f"skip it. Post-process should have reverted to plain "
            f"call. Body:\n{build_body}"
        )
        # Tighten: the GC-restore preamble (`local.get <N>;
        # global.set $gc_sp`) must NOT precede the reverted
        # `call $build`.  The preamble belongs to #549's GC-aware
        # TCO path; once we've taken the postcondition-revert path
        # the preamble has no purpose (we're keeping the frame, not
        # discarding it via return_call), and injecting it anyway
        # would corrupt the shadow-stack invariant for the
        # remainder of the function.  This pins the dispatch
        # precedence: post_instrs revert > GC-aware patch (the
        # branches are mutually exclusive, not additive).
        #
        # Note: `local.get ...; global.set $gc_sp` legitimately
        # appears in the GC EPILOGUE at the end of every allocating
        # function (it restores $gc_sp before returning).  We can't
        # forbid the sequence outright; we can only forbid it
        # immediately preceding a `call $build` site.
        lines = build_body.splitlines()
        # Boundary-safe regex distinguishes plain `call $build`
        # from `return_call $build` AND excludes `$build_anything`.
        call_indices = [
            i for i, line in enumerate(lines)
            if re.search(r"\bcall \$build\b", line)
        ]
        assert call_indices, "no plain call $build site found"
        for idx in call_indices:
            if idx < 2:
                continue
            prev1 = lines[idx - 1].strip()
            prev2 = lines[idx - 2].strip()
            assert not (
                prev1 == "global.set $gc_sp"
                and prev2.startswith("local.get ")
            ), (
                f"Postcondition-revert path mistakenly injected the "
                f"#549 GC-restore preamble before `call $build` at "
                f"line {idx}.  Preamble lines: {prev2!r}, {prev1!r}. "
                f"Dispatch precedence violated: post_instrs revert "
                f"and GC-aware patch should be mutually exclusive. "
                f"Body:\n{build_body}"
            )

    def test_analyzer_marks_block_trailing_expression(self) -> None:
        """Unit test: analyzer marks Block.expr as tail position."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  f()
}
""")
        decl = program.declarations[0].decl
        sites = compute_tail_call_sites(decl)
        # The single FnCall in the body is the trailing expression
        # of the block — analyzer marks it.
        assert len(sites) == 1

    def test_analyzer_marks_both_branches_of_tail_if(self) -> None:
        """Unit test: both then/else branches of a tail-position if."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
public fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{
  if @Bool.0 then { f(false) } else { f(true) }
}
""")
        decl = program.declarations[0].decl
        sites = compute_tail_call_sites(decl)
        # Two FnCalls (one per branch) — both should be marked.
        assert len(sites) == 2

    def test_analyzer_marks_match_arm_bodies(self) -> None:
        """Unit test: every arm body of a tail-position match is tail position.

        ``MatchExpr`` is tail-transparent in the same way ``IfExpr``
        is — if the match expression itself is in tail position
        (i.e. it's the trailing expression of the function body),
        every arm body is in tail position.  The scrutinee is NOT,
        and call arguments inside an arm body are NOT — those are
        non-transparent in the same way.

        Pre-this-test, MatchExpr handling in the analyzer
        (``visit_tail`` in ``vera/codegen/tail_position.py``)
        existed but had no explicit test pinning the behaviour;
        a regression that dropped or mis-handled the MatchExpr
        case would have slipped past CI silently.  This test
        constructs a function whose body is a match with two arms
        — one arm wraps its tail call around a non-tail argument
        call — and asserts the analyzer marks the two arm bodies
        but NOT the inner argument call.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn arg_producer(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

private fn arm_handler(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn f(@Option<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    None -> arm_handler(arg_producer(())),
    Some(@Int) -> arm_handler(@Int.0)
  }
}
""")
        f_decl = program.declarations[2].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the specific call ids by walking the AST so the
        # assertion below pins WHICH calls got marked, not just how
        # many — same exhaustiveness pattern as
        # ``test_analyzer_does_not_mark_call_args``.  Body shape:
        #
        #   Block(statements=[], expr=MatchExpr(
        #     scrutinee=SlotRef,
        #     arms=[
        #       Arm(pattern=None, body=FnCall("arm_handler",
        #             [FnCall("arg_producer", [UnitLit])])),
        #       Arm(pattern=Some(@Int), body=FnCall("arm_handler",
        #             [SlotRef])),
        #     ]))
        match_expr = f_decl.body.expr
        assert isinstance(match_expr, ast.MatchExpr)
        assert len(match_expr.arms) == 2

        none_arm_call = match_expr.arms[0].body
        some_arm_call = match_expr.arms[1].body
        assert isinstance(none_arm_call, ast.FnCall)
        assert isinstance(some_arm_call, ast.FnCall)
        assert none_arm_call.name == "arm_handler"
        assert some_arm_call.name == "arm_handler"

        nested_arg_call = none_arm_call.args[0]
        assert isinstance(nested_arg_call, ast.FnCall)
        assert nested_arg_call.name == "arg_producer"

        # Both arm bodies (the outer ``arm_handler(...)`` calls)
        # are in tail position via match-transparency.  The nested
        # ``arg_producer(())`` call inside the None arm is an
        # argument — non-transparent, NOT tail.  An exhaustive
        # ``sites == {...}`` check pins both the inclusion AND the
        # exclusion in one assertion.
        assert id(none_arm_call) in sites, (
            f"None-arm body call should be tail position; "
            f"sites={sites!r}, expected id={id(none_arm_call)}"
        )
        assert id(some_arm_call) in sites, (
            f"Some-arm body call should be tail position; "
            f"sites={sites!r}, expected id={id(some_arm_call)}"
        )
        assert id(nested_arg_call) not in sites, (
            f"Nested argument call inside None arm should NOT be "
            f"tail position; sites={sites!r}, "
            f"unexpected id={id(nested_arg_call)}"
        )
        assert sites == {id(none_arm_call), id(some_arm_call)}, (
            f"Expected exactly the two arm-body calls in sites; "
            f"got {sites!r}"
        )

    def test_analyzer_does_not_mark_let_value_calls(self) -> None:
        """Unit test: a call as a let value is NOT tail position."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn helper(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = helper();
  @Int.0 + 1
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)
        # The let value is NOT tail; the trailing `@Int.0 + 1` is
        # an addition (BinaryExpr), not a call.  No FnCalls in tail
        # position.
        assert sites == set()

    def test_analyzer_does_not_mark_call_args(self) -> None:
        """Unit test: args to a tail-position call are NOT themselves tail."""
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn inner(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private fn arg_producer(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  inner(arg_producer())
}
""")
        from vera import ast
        f_decl = program.declarations[2].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the two call ids explicitly so the assertion below
        # checks WHICH call got marked, not just how many.  The
        # body is `Block(statements=[], expr=FnCall("inner", [FnCall("arg_producer", [])]))`
        # so the outer call is `f_decl.body.expr`, and the inner
        # arg-producer call is its first argument.
        outer_call = f_decl.body.expr
        assert isinstance(outer_call, ast.FnCall)
        assert outer_call.name == "inner"
        inner_arg_call = outer_call.args[0]
        assert isinstance(inner_arg_call, ast.FnCall)
        assert inner_arg_call.name == "arg_producer"

        # The outer call IS in tail position (trailing expression of
        # the function body).  The argument call is NOT — its result
        # is consumed by `inner`'s parameter binding.  A buggy
        # analyzer that marked argument calls would emit
        # `return_call $arg_producer` and the discarded frame would
        # mean `inner` never receives its argument.
        assert id(outer_call) in sites, (
            f"Outer call `inner(...)` should be marked tail position; "
            f"sites={sites!r}, outer call id={id(outer_call)}"
        )
        assert id(inner_arg_call) not in sites, (
            f"Argument call `arg_producer()` should NOT be marked "
            f"tail position; sites={sites!r}, "
            f"arg call id={id(inner_arg_call)}"
        )
        # And nothing else either — both ids accounted for.
        assert sites == {id(outer_call)}

    def test_analyzer_does_not_mark_call_in_block_statement(self) -> None:
        """Unit test: a call inside a Block statement is NOT tail position.

        ``Block`` is tail-transparent for its trailing expression
        ONLY — calls inside ``LetStmt.value`` / ``ExprStmt.expr`` /
        ``LetDestruct.value`` are NOT in tail position, even when
        the block itself is.  The analyzer's Block handler only
        recurses into ``block.expr``; statements are skipped.

        This test pins the ExprStmt case specifically (the
        ``LetStmt.value`` case is covered by
        ``test_analyzer_does_not_mark_let_value_calls``).  A
        regression that started visiting statements would mark the
        side-effect call below in tail position, which would mean
        WASM ``return_call`` discards the current frame and the
        block's trailing expression (``42``) never executes.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn side_effect(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  side_effect(());
  42
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)

        # The block has one ExprStmt (the side_effect call) and a
        # trailing IntLit.  Locate the ExprStmt's call to assert it
        # is NOT marked.  AST shape:
        #
        #   Block(statements=[ExprStmt(expr=FnCall("side_effect", [UnitLit]))],
        #         expr=IntLit(42))
        block = f_decl.body
        assert isinstance(block, ast.Block)
        assert len(block.statements) == 1
        side_effect_stmt = block.statements[0]
        assert isinstance(side_effect_stmt, ast.ExprStmt)
        side_effect_call = side_effect_stmt.expr
        assert isinstance(side_effect_call, ast.FnCall)
        assert side_effect_call.name == "side_effect"

        # Trailing expression is IntLit(42), not a call — so the
        # analyzer should mark NOTHING.  The ExprStmt's call must
        # NOT be in sites (it's a statement, not the trailing
        # expression).
        assert id(side_effect_call) not in sites, (
            f"ExprStmt-position call should NOT be tail position; "
            f"sites={sites!r}, unexpected id={id(side_effect_call)}"
        )
        assert sites == set(), (
            f"Expected empty sites (only statement call, no tail "
            f"calls); got {sites!r}"
        )

    def test_analyzer_does_not_mark_call_in_if_condition(self) -> None:
        """Unit test: a call inside an IfExpr condition is NOT tail position.

        ``IfExpr`` is tail-transparent for its branches only —
        the condition is evaluated first, its result is consumed
        by the if-dispatch, and only THEN one of the branches
        runs.  A call in the condition is therefore non-tail.
        The analyzer's IfExpr handler only recurses into
        ``then_branch`` and ``else_branch``; the condition is
        skipped.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn predicate(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ true }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  if predicate(()) then { 1 } else { 2 }
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the predicate() call in the if condition.  Body
        # shape: Block(statements=[], expr=IfExpr(condition=FnCall(...),
        # then_branch=Block(...), else_branch=Block(...))).
        if_expr = f_decl.body.expr
        assert isinstance(if_expr, ast.IfExpr)
        cond_call = if_expr.condition
        assert isinstance(cond_call, ast.FnCall)
        assert cond_call.name == "predicate"

        # Both branches return literals (no calls), so the analyzer
        # should mark NOTHING.  The condition call must NOT be in
        # sites — a regression that recursed into the condition with
        # the parent's tail status would mark it and ``return_call``
        # would discard the frame before the if-dispatch ran.
        assert id(cond_call) not in sites, (
            f"IfExpr-condition call should NOT be tail position; "
            f"sites={sites!r}, unexpected id={id(cond_call)}"
        )
        assert sites == set(), (
            f"Expected empty sites (no tail calls — both branches "
            f"are literals); got {sites!r}"
        )

    def test_analyzer_does_not_mark_call_in_match_scrutinee(self) -> None:
        """Unit test: a call inside a MatchExpr scrutinee is NOT tail position.

        ``MatchExpr`` is tail-transparent for its arm bodies only —
        the scrutinee is evaluated first, its result is consumed
        by the match-dispatch (constructor tag check + field
        binding), and only THEN one of the arms runs.  A call in
        the scrutinee is therefore non-tail.  The analyzer's
        MatchExpr handler only recurses into each arm's body;
        the scrutinee is skipped.
        """
        from vera import ast
        from vera.codegen.tail_position import compute_tail_call_sites
        from vera.parser import parse_to_ast
        program = parse_to_ast("""\
private fn make_option(@Unit -> @Option<Int>)
  requires(true) ensures(true) effects(pure)
{ None }

public fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  match make_option(()) {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
""")
        f_decl = program.declarations[1].decl
        sites = compute_tail_call_sites(f_decl)

        # Locate the make_option() call in the match scrutinee.
        # Body shape: Block(statements=[], expr=MatchExpr(
        #   scrutinee=FnCall(...), arms=[...])).
        match_expr = f_decl.body.expr
        assert isinstance(match_expr, ast.MatchExpr)
        scrutinee_call = match_expr.scrutinee
        assert isinstance(scrutinee_call, ast.FnCall)
        assert scrutinee_call.name == "make_option"

        # Both arms return literals/slot ref (no calls), so the
        # analyzer should mark NOTHING.  The scrutinee call must
        # NOT be in sites — a regression that recursed into the
        # scrutinee with the parent's tail status would mark it
        # and ``return_call`` would discard the frame before the
        # match-dispatch ran (the constructor tag check would have
        # nothing to inspect).
        assert id(scrutinee_call) not in sites, (
            f"MatchExpr-scrutinee call should NOT be tail position; "
            f"sites={sites!r}, unexpected id={id(scrutinee_call)}"
        )
        assert sites == set(), (
            f"Expected empty sites (no tail calls — both arms are "
            f"literals/slot ref); got {sites!r}"
        )


class TestClosureI32PairParams:
    """Closures whose parameters or return types are i32_pair (String, Array).

    Regression tests for #359: closure lifting and call_indirect type
    descriptors must emit two consecutive i32 slots for i32_pair types,
    not an unsupported/missing param.
    """

    def test_closure_string_param_compiles(self) -> None:
        """Closure with a String parameter emits valid (param i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  apply_fn(fn(@String -> @Int) effects(pure) { string_length(@String.0) }, "hello")
}
"""
        assert _run(src) == 5

    def test_closure_string_return_compiles(self) -> None:
        """Closure with a String return type emits valid (result i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = apply_fn(fn(@Int -> @String) effects(pure) { "ok" }, 0);
  string_length(@String.0)
}
"""
        assert _run(src) == 2

    def test_closure_array_param_compiles(self) -> None:
        """Closure with an Array<Int> parameter emits valid (param i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = [10, 20, 30];
  apply_fn(fn(@Array<Int> -> @Int) effects(pure) { array_length(@Array<Int>.0) }, @Array<Int>.0)
}
"""
        assert _run(src) == 3

    def test_closure_array_return_compiles(self) -> None:
        """Closure with an Array<Int> return type emits valid (result i32 i32) WAT."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = apply_fn(fn(@Int -> @Array<Int>) effects(pure) { [1, 2] }, 0);
  array_length(@Array<Int>.0)
}
"""
        assert _run(src) == 2

    def test_array_fold_with_map_accumulator(self) -> None:
        """array_fold over String array with Map<String, Int> accumulator.

        Exercises: (1) i32_pair closure param in the lifted fold fn,
        (2) apply_fn return-type inference with a parameterized accumulator
        so _resolve_generic_call produces array_fold_go$String_Map_String_Int.
        Also exercises the zero-iteration path (empty array).
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<String> = ["a", "b", "c"];
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(
    @Array<String>.0,
    @Map<String, Int>.0,
    fn(@Map<String, Int>, @String -> @Map<String, Int>) effects(pure) {
      map_insert(@Map<String, Int>.0, @String.0, 1)
    }
  );
  let @Int = map_size(@Map<String, Int>.0);
  let @Array<String> = [];
  let @Map<String, Int> = map_new();
  let @Map<String, Int> = array_fold(
    @Array<String>.0,
    @Map<String, Int>.0,
    fn(@Map<String, Int>, @String -> @Map<String, Int>) effects(pure) {
      map_insert(@Map<String, Int>.0, @String.0, 1)
    }
  );
  let @Int = map_size(@Map<String, Int>.0);
  @Int.1 + @Int.0
}
"""
        assert _run(src) == 3  # 3 + 0


# =====================================================================
# Pair-type closure capture (#535 — residual of #514)
# =====================================================================


class TestPairCapture535:
    """`#535`: closures capturing `String` / `Array<T>` outer bindings.

    Pre-fix, `vera/wasm/closures.py::_walk_free_vars` resolved the
    capture's wasm type via `_type_name_to_wasm`, which collapses every
    composite type to a single `"i32"`.  `_translate_anon_fn` then
    serialised only the ptr half of the pair into the closure struct;
    `_compile_lifted_closure` read back only the ptr and the body got
    the len from adjacent struct memory (typically zero).  So
    `array_length` / `string_length` of a captured `Array<T>` /
    `String` always returned 0.

    Post-fix all three sites carry an `"i32_pair"` tag for these
    captures: 8 bytes per field (two consecutive i32 stores at
    offset / offset+4); the lifted body allocates two consecutive
    i32 locals (ptr, len) and pushes only the ptr into the slot env,
    matching the let-binding and parameter conventions.
    """

    def test_array_capture_length_in_closure(self) -> None:
        """Reproducer from #535: captured `Array<Int>` length is correct.

        Three iterations × captured length 7 = 21.  Pre-fix the inner
        closure read the captured `@Array<Int>.0` length as 0, so
        `array_fold(...)` summed three zeroes = 0.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 7);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(array_length(@Array<Int>.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        assert _run(src) == 21

    def test_string_capture_length_in_closure(self) -> None:
        """Captured `@String.0` length is correct (5 × 3 iterations = 15)."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = "hello";
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(string_length(@String.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        assert _run(src) == 15

    def test_adt_capture_still_works(self) -> None:
        """ADT capture (single i32 ptr) still works — proof the pair fix
        is scoped and doesn't disturb the i32 path."""
        src = """
private data Box<T> { Box(T) }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Box<Int> = Box(42);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      match @Box<Int>.0 { Box(@Int) -> @Int.0 }
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 42 × 3 = 126
        assert _run(src) == 126

    def test_primitive_capture_still_works(self) -> None:
        """Primitive (Int) capture still works — same scope-pin as ADT."""
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 7;
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      @Int.1
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 7 × 3 = 21
        assert _run(src) == 21

    def test_mixed_pair_and_primitive_capture(self) -> None:
        """Closure captures both an Int (primitive) and an Array (pair).

        Layout exercise: `_translate_anon_fn` must pack the i64 (Int)
        capture at one offset and the i32_pair at another, in the
        order they appear in the free-var walk.
        `_compile_lifted_closure` must mirror that layout on read.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 100;
  let @Array<Int> = array_range(0, 4);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      @Int.1 + nat_to_int(array_length(@Array<Int>.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # (100 + 4) × 3 = 312
        assert _run(src) == 312

    def test_empty_string_capture_in_closure(self) -> None:
        """Captured empty `String` reads as length 0 (not garbage).

        Edge case for the pair-capture fix: an empty string has
        len = 0, the same value the pre-fix bug *also* produced
        (because it always returned 0).  The post-fix property we
        pin here is that the len is *correctly* preserved as 0
        (rather than reading garbage from an unallocated len slot
        in the closure struct).
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = "";
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(string_length(@String.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 0 × 3 = 0 (empty string captured)
        assert _run(src) == 0

    def test_empty_array_capture_in_closure(self) -> None:
        """Captured empty `Array<Int>` reads as length 0 (not garbage).

        Same edge-case shape as the empty-string test: pins that the
        post-fix path correctly preserves a zero-length pair capture
        (vs. happening to print 0 because the bug always read len as 0).
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 0);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      nat_to_int(array_length(@Array<Int>.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # 0 × 3 = 0 (empty array captured)
        assert _run(src) == 0

    def test_gc_pressure_pair_capture(self) -> None:
        """Pair capture survives heavy in-closure allocation (GC pressure).

        Exercises the round-1 GC-ordering fix (`gc_capture_pushes`
        runs after `load_instrs`): the closure body allocates several
        large temporary arrays *before* reading the captured array's
        length.  If the capture root were pushed in the prologue
        (pre-fix, before loads), the shadow stack would carry zero —
        and a `$gc_collect` triggered by these in-body allocations
        could mark the captured array unreachable and sweep it,
        leaving the subsequent `array_length(@Array<Int>.0)` reading
        from freed memory.

        Post-fix: the capture root sits on the shadow stack with the
        loaded ptr value (after the env-loads emit), so the captured
        array stays marked through every allocation.

        Three iterations of the outer `array_map`, each allocating
        ~12 KB of temporary arrays inside the body, then reading the
        captured array's length (7) — folded sum is 21.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Int> = array_range(0, 7);
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      nat_to_int(array_length(@Array<Int>.3))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # @Array<Int>.3 is the outer captured array (skip the three inner
        # let-bindings at indices 0, 1, 2); length 7, three iterations,
        # folded sum 21.
        assert _run(src) == 21

    def test_gc_pressure_string_capture(self) -> None:
        """Same shape as test_gc_pressure_pair_capture but for `String`.

        Captured String must survive heavy in-closure allocation.
        Three iterations × `string_length("hello")` = 5 × 3 = 15.
        """
        src = """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = "hello";
  let @Array<Int> = array_map(
    array_range(0, 3),
    fn(@Int -> @Int) effects(pure) {
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      let @Array<Int> = array_range(0, 500);
      nat_to_int(string_length(@String.0))
    }
  );
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.0 + @Int.1 })
}
"""
        # Captured "hello" is length 5; three iterations × 5 = 15
        assert _run(src) == 15
