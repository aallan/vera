# `ch09_nested_builtin_index` under `VERA_EAGER_GC=1` — reproducer + bisection

Branch `fix/runtime-gc-root-lifetime`, WIP commit `50be0b97`+ (D1b: general GC
root scoping).  Base for every "base" row below is `fdda84a8`
(`release/v0.2.0` with #1370 merged).

Everything here needs `VERA_EAGER_GC=1` — a collection at every `$alloc`.  The
normal gate is green at head: suite 12,152, conformance 244/244, examples
43/43 (also clean under eager GC).

## The failure

    cd /Users/aa/Code/vera-d1
    VERA_EAGER_GC=1 PYTHONPATH=$PWD ./.venv/bin/python scripts/check_conformance.py

At head: 2 failures.  At base: 1 failure.

* `ch09_generic_infer_user_fn_return` — **pre-existing at base**, not D1b's.
* `ch09_nested_builtin_index` — **head only**, this is the regression:

      Postcondition violation in reverse_of_map_values( -> @Int)
        ensures(@Int.result == 77) failed

Also pre-existing at base under eager GC (so, missing-root soundness bugs on
main by definition):

    VERA_EAGER_GC=1 PYTHONPATH=$PWD ./.venv/bin/python -m pytest \
      "tests/test_codegen_monomorphize.py::TestUserFnReturnTypeInArgPosition878::test_user_fn_return_in_arg_position_runs_and_prints" -q

## Minimal shape

`tests/conformance/ch09_nested_builtin_index.vera`.  The failing helper is

    public fn reverse_of_map_values(-> @Int)
      requires(true)
      ensures(@Int.result == 77)
      effects(pure)
    {
      let @Map<String, Int> = map_insert(map_new(), "k", 77);
      array_reverse(map_values(@Map<String, Int>.0))[0]
    }

It fails only when called from `main` alongside **at least the first four**
helpers (prefix bisection: 1 → 10 ok, 2 → 20 ok, 3 → 97 ok, 4 → FAIL,
5 → FAIL).  The 4th helper (`sort_by_of_map_values`) is the second Map user,
so the trigger correlates with wrap-table pressure.  Called on its own,
`reverse_of_map_values` returns 77 at head.

## Bisection results (all at head unless stated)

| switch | result |
|---|---|
| statement scoping only (`_scope_statement_roots` live, `_scope_shadow_roots` a no-op) | **137, correct** |
| expression scoping only (`_scope_shadow_roots` live, statement scoping a no-op) | FAIL |
| skip the expression wrapper for `FnCall` only | **137, correct** |
| skip it for `array_reverse` calls only | **137, correct** |
| skip it for any other single kind or callee name | FAIL |
| wrapper emits save + restore, **no** re-root | **137, correct** |
| wrapper emits save + re-root, **no** restore | **137, correct** |
| wrapper emits save + restore + re-root (current) | FAIL |
| same, but the re-root pushes a **zero** instead of the pointer | **137, correct** |
| BASE + one extra `gc_shadow_push` of `array_reverse`'s result (no restore) | 137, correct |

So: the shadow-stack mechanics are fine (a zero at the same slot is
harmless).  What changes the outcome is rooting **that live pointer** at that
slot, and only in combination with the restore.

## The computation is CORRECT; only the check fails

| postcondition on `reverse_of_map_values` | `main` |
|---|---|
| `ensures(@Int.result == 77)` (original) | FAIL |
| `ensures(@Int.result >= 0)` (still non-trivial, same TCO path) | **137** |
| `ensures(true)` (trivial — different path, no `post_instrs`) | **137** |

`array_length(map_values(m))` is 1 at head, so the Map and its values array
are intact.  An extra **live** root cannot change a computed value under a
correct collector and a correct lowering, so one of the two is wrong.

## Driver scripts

Under `/private/tmp/claude-501/-Users-aa-Code-vera/a6cf47ac-2938-4fd3-bc7f-542382e55555/scratchpad/streamD/`:

* `bisect_half.py` — statement vs expression scoping, single function.
* `bisect_full.py` — the same over every helper in the conformance program.
* `bisect_kind.py` — disable the wrapper per `ast` expression class.
* `bisect_name.py` — disable it per callee name.
* `positions.py` — roots-per-frame by syntactic position (the K axis).

Each takes a checkout root as `argv[1]` where relevant and prints a canary
line naming the `vera` package it imported.

## Swapping `vera/` to base inside this worktree

    git checkout fdda84a8 -- vera/     # measure at base
    git checkout HEAD -- vera/         # back to head

The worktree has its own venv (`.venv`) whose editable install points at the
worktree, so `import vera` resolves here either way; `PYTHONPATH=$PWD` is set
on gate runs regardless (S13).

---

# ROOT FOUND (01:35) — pre-existing on `main`, layout-dependent

**D1b is not the cause.**  The defect is latent on `main` (`6dc41d40`) and on
this PR's base (`fdda84a8`), and is selected by the **heap base address**, not
by anything D1b does.  D1b's scoping changes the emitted code size, which
moves the data section, which moves `gc_heap_start` — landing on a failing
layout.

## The layout knob

Adding an unused function whose only content is one string literal is pure
data-section padding: no extra allocation on any path, no extra root.
Sweeping the pad length over `ch09_nested_builtin_index`:

| checkout | failing pads in 0..159 |
|---|---|
| `main` 6dc41d40 | **{32}** |
| base `fdda84a8` (release/v0.2.0 + #1370) | **{32}** |

Identical failure text to D1b's, at the same pad:

    Postcondition violation in reverse_of_map_values( -> @Int)
      ensures(@Int.result == 77) failed

Adding *dead allocations* instead does NOT reproduce (25 variants, all 137) —
the knob is the heap BASE, not the allocation sequence.  That is why the
first layout test came back clean.

## Minimal reproducer (fails on `main`)

```vera
public fn rev_map(-> @Int)
  requires(true)
  ensures(@Int.result == 77)
  effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 77);
  array_reverse(map_values(@Map<String, Int>.0))[0]
}

public fn main(-> @Int)
  requires(true)
  ensures(@Int.result == 154)
  effects(pure)
{
  rev_map() + rev_map()
}
```

plus 232 characters of data-section padding, under `VERA_EAGER_GC=1`.
Driver: `scratchpad/streamD/minimize.py`.

## Ingredient discrimination (pads 0..299, on `main`)

| program | failing pads |
|---|---|
| `array_reverse(map_values(m))[0]` | **{232}** |
| `array_sort_by(map_values(m), cmp)[0]` | **{216}** |
| `array_length(array_reverse(map_values(m)))` | none |
| `array_reverse(map_keys(m))[0]` (String elements) | none |
| `map_values(m)[0]` (no array builtin) | none |
| `array_reverse([10,20,30])[2]` (no Map) | none |
| one call instead of two | none |

So all of these are required: a **Map-produced `Array<Int>`**, passed through
an array builtin that **allocates a new backing array** (`array_reverse` or
`array_sort_by`), then an **element read** — reading only the LENGTH is
clean, and `map_keys` (pair-represented `String` elements) is clean.  Two
calls are needed, so it takes a second collection to surface.

That shape says the destination array's CONTENTS are wrong — the copy reads
a source that has been reclaimed or reused — rather than the array handle
being lost, which is what a length read would also have caught.

Runtime side from here (`$gc_collect`, the wrap table's Phase 2c eviction,
`map_values`' host-side `_ShadowGuard` rooting, `array_reverse`'s copy loop).

## Driver added

* `layout_datasec.py` / `layout_wide.py` — the data-section pad sweep.
* `minimize.py` — the four-way minimization.
* `discriminate.py` — the ingredient table above.

## Filed

[#1382](https://github.com/aallan/vera/issues/1382) — "Element read of an
allocating array builtin over a Map-produced Array<Int> returns wrong contents
under VERA_EAGER_GC=1 (heap-base-selected)", labelled `bug`, with the minimal
232-pad `main` reproducer, both pad tables, the ingredient discrimination and
the candidate sites.  Cross-referenced #1379 as a possible sibling (same
"intermediate result does not survive a collection between production and use"
shape).

D1b (#1371) merges only AFTER #1382's fix lands on `release/v0.2.0`; its gate
battery then includes `VERA_EAGER_GC=1 python scripts/check_conformance.py`
and examples-run under the same knob, green at the rebased head.
