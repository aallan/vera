"""The class instrument: every binder position, every refinement kind.

`vera/binders.py` says which positions the grammar binds a slot in.  This file
is the generator that holds the COMPILER to that list: for each registered
position, crossed with each kind of narrowing a binder can declare, it emits a
minimal program that routes a violating value into that position and asserts
the property every issue in this family broke —

    **a violating value is never silently accepted.**

Read precisely, in three parts, because the three are what the four issues
each broke a different one of:

1. *Never silent.*  The obligation stream records the narrowing.  #1448 and
   #1455 broke this: nothing at all, so `vera verify` reported a clean
   program.
2. *Never unbacked.*  Unless the record DISCLOSES that the site is unguarded
   (`tier3_unguarded`), the program is refused — statically, or by the
   artifact at run time.  #1445 broke this: an honest `tier3_unguarded`
   disclosure would have been acceptable, but the record said `tier3`, which
   claims a runtime check, and no check existed.
3. *Not by refusing everything.*  The satisfying twin verifies clean and runs
   to completion, so a cell cannot be green because the compiler rejects the
   shape.

The positions come from `binders.BINDER_FIELDS`, never from a list written
here: a position registered without a template fails
`test_every_registered_position_is_templated_or_excused` rather than being
silently unmeasured, which is the same hole one level up.

Red at `origin/release/v0.2.0` 8eca11c0, before the fixes in this PR:

| cell | base reading |
|---|---|
| handler clause binder x `@Nat` | silent, no guard: `ok: true`, no obligation, `-7` flows through |
| handler clause binder x refined `@Int` | silent, no guard |
| handler clause binder x refined `@String` | silent, no guard |
| call argument (`where` helper) x all four | silent (#1455; fixed in the first commit of this PR) |

Three defects the generator finds are RECORDED rather than trimmed away.  Two
of them this PR closes; the third is `_KNOWN_RED` below, whose products are
skipped in the matrix and pinned by a cell of their own at the end of the
file, asserting what the compiler does today.  Nothing here is `xfail`ed: no
test in this suite is, and `scripts/check_doc_counts.py` gates TESTING.md's
breakdown as `passed + stress-deselected + skipped == collected`, which has no
term for one.  A pinning assertion has the property that matters — it fails
the day the defect is fixed — without making every future PR write a fourth
number.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from vera import binders, carriers, narrowing

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

_NARROWING_KINDS = ("refine_bind", "nat_bind", "int_widen")


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=300,
    )


def _write(tmp_path: Path, source: str, name: str) -> Path:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return p


# =====================================================================
# The two axes
# =====================================================================

#: (prelude, slot spelling, a violating value, a satisfying value, base name).
#:
#: Four kinds rather than one, because the halves of a guard are lowered
#: separately and a fix can reach one and not another: `@Nat` is the SIGN
#: direction, a refined `@Int` the §2.6.5 predicate over a scalar base, a
#: refined `@String` the same predicate over a base a construction store
#: cannot tee into a scalar local (`REFINED_CONSTRUCTION_SCALAR_BASES`), and
#: a refined element type the case where the narrowing is written INSIDE the
#: slot's type rather than on it.
_KINDS: dict[str, tuple[str, str, str, str, str]] = {
    "nat": ("", "@Nat", "0 - 5", "5", "Int"),
    "refined_int": (
        "type Pos = { @Int | @Int.0 > 0 };\n\n",
        "@Pos", "0 - 5", "5", "Int",
    ),
    "refined_string": (
        "type NonEmpty = { @String | string_length(@String.0) > 0 };\n\n",
        "@NonEmpty", '""', '"x"', "String",
    ),
    "refined_array": (
        "type Pos = { @Int | @Int.0 > 0 };\n\n",
        "@Array<Pos>", "[0 - 5]", "[5]", "Array<Pos>",
    ),
}

#: A value that satisfies every kind's predicate, keyed by base.  Used only to
#: fill a DIFFERENT binder position in the same program that must stay valid
#: so the position under test carries the value alone.
_SAFE: dict[str, str] = {"Int": "5", "String": '"x"', "Array<Pos>": "[5]"}


def _bare(slot: str) -> str:
    """"@Array<Pos>" -> "Array<Pos>"."""
    return slot[1:]


# =====================================================================
# One template per position
# =====================================================================
#
# Each takes (pre, slot, value, base) and returns a complete program routing
# `value` into the named position.  Where a position needs a second binder
# filled to be well-formed, that one takes `_SAFE[base]` so the value under
# test is in one place only.

def _t_call_argument(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""private fn h({slot} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  h({value})
}}
"""


def _t_call_argument_where(pre: str, slot: str, value: str, base: str) -> str:
    """#1455's own spelling: the callee is a `where` helper."""
    return pre + f"""public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  h({value})
}}
where {{
  fn h({slot} -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{
    1
  }}
}}
"""


def _t_return_type(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""private fn h(@Unit -> {slot})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {value}
}}

public fn f(@Unit -> {slot})
  requires(true)
  ensures(true)
  effects(pure)
{{
  h(())
}}
"""


def _t_let_binding(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let {slot} = {value};
  1
}}
"""


def _t_match_binding(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {value} {{
    {slot} -> {slot}.0
  }}
}}
"""


def _t_adt_subpattern(pre: str, slot: str, value: str, base: str) -> str:
    """A `let`-bound scrutinee rather than an inline `Some(<value>)`.

    The inline spelling is a position of its own and is pinned separately at
    the end of this file: there the checker types the constructor argument
    against a pattern-derived expected type and records no instantiated
    target, so the narrowing is invisible.  Binding the scrutinee first types
    the construction against the `let`'s own annotation, which is the route
    this cell is about.
    """
    safe = _SAFE[base]
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Option<{base}> = Some({value});
  match @Option<{base}>.0 {{
    Some({slot}) -> {slot}.0,
    None -> {safe}
  }}
}}
"""


def _t_tuple_destructure(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  let Tuple<@Int, {slot}> = Tuple(1, {value});
  {slot}.0
}}
"""


def _t_constructor_field(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""private data Box {{
  MkBox({_bare(slot)})
}}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{{
  MkBox({value})
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match build(()) {{
    MkBox({slot}) -> 1
  }}
}}
"""


def _t_tuple_component(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""private fn take(@Tuple<{_bare(slot)}, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  take(Tuple({value}, 1))
}}
"""


def _t_array_element(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""private fn take(@Array<{_bare(slot)}> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  take([{value}])
}}
"""


def _t_map_value(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Map<String, {_bare(slot)}> = map_insert(map_new(), "a", {value});
  1
}}
"""


#: The payload a clause binder must be NARROWER than, per refinement kind's
#: base.  `refined_array`'s slot and its base are both `Array<Pos>`, so using
#: the base as the payload made the binder equal to what it receives — no
#: narrowing, and a program identical to the `effect-operation argument`
#: cell's.  A cell that cannot fail reads as coverage, which is the one thing
#: TESTING.md § Class Instruments says is worse than an absent cell
#: (CodeRabbit on PR #1465).
_CLAUSE_PAYLOAD = {"Array<Pos>": "Array<Int>"}


def _t_handler_clause_binder(pre: str, slot: str, value: str, base: str) -> str:
    """#1445 / #1448's own spelling: the clause binds the thrown payload."""
    payload = _CLAUSE_PAYLOAD.get(base, base)
    return pre + f"""public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{payload}>] {{
    throw({slot}) -> {{ 1 }}
  }} in {{
    throw({value})
  }}
}}
"""


def _t_handler_state_init(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<{_bare(slot)}>]({slot} = {value}) {{
    put({slot}) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}
"""


def _t_handler_state_update(pre: str, slot: str, value: str, base: str) -> str:
    """The `with @T = …` override.  The cell's INIT takes a safe value, so
    the position under test is the override alone rather than the init."""
    safe = _SAFE[base]
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<{_bare(slot)}>]({slot} = {safe}) {{
    put({slot}) -> {{ resume(()) }} with {slot} = {value}
  }} in {{
    put({safe});
    get(())
  }}
}}
"""


def _t_closure_argument(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(fn({slot} -> @Int) effects(pure) {{ 1 }}, {value})
}}
"""


def _t_closure_return(pre: str, slot: str, value: str, base: str) -> str:
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(fn(@Unit -> {slot}) effects(pure) {{ {value} }}, ())
}}
"""


def _t_effect_operation_argument(
    pre: str, slot: str, value: str, base: str,
) -> str:
    """The op-call's own argument, against the effect's declared payload."""
    return pre + f"""public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{_bare(slot)}>] {{
    throw({slot}) -> {{ 1 }}
  }} in {{
    throw({value})
  }}
}}
"""


def _t_state_op_resume(pre: str, slot: str, value: str, base: str) -> str:
    """A `get` clause's tail `resume(v)` delivers the cell-typed result."""
    safe = _SAFE[base]
    return pre + f"""public fn f(@Unit -> @{base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<{_bare(slot)}>]({slot} = {safe}) {{
    get(@Unit) -> {{ resume({value}) }},
    put({slot}) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}
"""


# =====================================================================
# The registry: one or more templates per registered site
# =====================================================================

#: Site name -> the spellings that reach it.  A site with two entries has two
#: syntactic routes worth separating: `call argument` is reached by a call to
#: a top-level function and by a call to a `where` helper, and #1455 was the
#: second answering differently from the first.
_TEMPLATES: dict[str, tuple[object, ...]] = {
    "call argument": (_t_call_argument, _t_call_argument_where),
    "return type": (_t_return_type,),
    "closure argument": (_t_closure_argument,),
    "closure return": (_t_closure_return,),
    "let binding": (_t_let_binding,),
    "match binding": (_t_match_binding,),
    "tuple destructure": (_t_tuple_destructure,),
    "ADT sub-pattern bind": (_t_adt_subpattern,),
    "constructor field": (_t_constructor_field,),
    "tuple component": (_t_tuple_component,),
    "array element": (_t_array_element,),
    "map value": (_t_map_value,),
    "handler clause binder": (_t_handler_clause_binder,),
    "handler state init": (_t_handler_state_init,),
    "handler state update": (_t_handler_state_update,),
    "effect-operation argument": (_t_effect_operation_argument,),
    "State-op resume": (_t_state_op_resume,),
}

#: Registered positions with no template, and why.  A position here is a
#: DECISION, not an omission: the reason is what a later reader has to
#: disagree with before adding one.
_NO_TEMPLATE: dict[str, str] = {
    "quantifier binder":
        "`forall(@T, domain, pred)` binds its variable inside a contract, "
        "which is translated to a Z3 bound variable and never reaches a run. "
        "There is no value to narrow and no guard to look for, so a cell "
        "here would assert nothing",
    "pattern binder":
        "a `BindingPattern` is the declared TYPE of a binder whose position "
        "is its owner's — a `match binding` under an arm, an "
        "`ADT sub-pattern bind` under a constructor pattern — and both "
        "owners have templates.  A cell of its own would run one of them "
        "twice under another name",
}


def _sites_and_kinds() -> set[str]:
    """Every position the registry declares, by the label a cell needs.

    A registered position's SITE where it has one, and its KIND where the
    site is inherited — so a position with no site of its own still has to
    appear in one of the two tables above rather than being unreachable from
    here.
    """
    labels: set[str] = set()
    for entries in binders.BINDER_FIELDS.values():
        for binder in entries:
            labels.add(binder.site if binder.site is not None else binder.kind)
    for sites in binders.CONSTRUCTION_SITES.values():
        labels.update(sites)
    return labels


def test_every_registered_position_is_templated_or_excused() -> None:
    """The generator's own completeness, against `binders.BINDER_FIELDS`.

    This is what makes the matrix a class instrument rather than a list: a
    position added to the registry with no program that reaches it fails
    HERE, instead of being a row nobody noticed was missing.  That is the
    hole the registry closes one level down, closed again one level up.
    """
    labels = _sites_and_kinds()
    covered = set(_TEMPLATES) | set(_NO_TEMPLATE)
    missing = sorted(labels - covered)
    assert not missing, (
        f"{missing} are registered binder positions with neither a template "
        f"nor an entry in _NO_TEMPLATE saying why one would assert nothing"
    )
    stale = sorted(covered - labels)
    assert not stale, (
        f"{stale} are templated but no longer registered positions"
    )


def test_no_excuse_is_empty() -> None:
    assert all(r.strip() for r in _NO_TEMPLATE.values()), _NO_TEMPLATE


# =====================================================================
# The matrix
# =====================================================================

#: (site, kind) -> the compiler message that says the SHAPE is unsupported.
#:
#: Not a cell.  A product the backend refuses outright exercises that refusal,
#: not the narrowing, and TESTING.md § Class Instruments is explicit that such
#: a cell is worse than an absent one because it reads as coverage.  Each entry
#: carries the message verbatim, so the day the shape becomes supported the
#: entry is what tells a reader a cell is now owed.
_UNSUPPORTED_SHAPES: dict[tuple[str, str], str] = {
    ("handler state init", "refined_string"):
        "Function 'f' uses State with unsupported type — skipped",
    ("handler state init", "refined_array"):
        "Function 'f' uses State with unsupported type — skipped",
    ("handler state update", "refined_string"):
        "Function 'f' uses State with unsupported type — skipped",
    ("handler state update", "refined_array"):
        "Function 'f' uses State with unsupported type — skipped",
    ("State-op resume", "refined_string"):
        "Function 'f' uses State with unsupported type — skipped",
    ("State-op resume", "refined_array"):
        "Function 'f' uses State with unsupported type — skipped",
    ("map value", "refined_array"):
        "Map/Set with an Array-typed or zero-size key, value, or element is "
        "not supported — function skipped",
}

#: (site, kind) -> a defect the generator finds that this PR does not fix,
#: with the measurement.  Marked rather than removed: a class instrument
#: trimmed until it is green measures the trimming.
_KNOWN_RED: dict[tuple[str, str], str] = {
    ("tuple component", "refined_string"):
        "#1466, pre-existing on main 6dc41d40 and release/v0.2.0 8eca11c0: "
        "the "
        "BOUNDARY guard's tuple decomposition tees a component into a scalar "
        "local, which is right for Int/Nat/Bool/Byte/Float64 and wrong for a "
        "String's (ptr, len) pair — so `take(Tuple(\"x\", 1))` against "
        "`@Tuple<NonEmpty, Int>` verifies at Tier 1 and TRAPS, though "
        "string_length(\"x\") is 1.  Two controls bound it: a bare "
        "`{ @String | … }` parameter runs, and the same tuple shape over an "
        "Int-based refinement runs.  The opposite failure from this PR's "
        "class — a guard emitted and wrong, rather than a position "
        "unrecorded — so it is filed rather than folded in",
}

_CELLS = [
    (site, index, kind)
    for site, fns in sorted(_TEMPLATES.items())
    for index in range(len(fns))
    for kind in _KINDS
]


def _skip_or_xfail(site: str, kind: str) -> None:
    """Apply this product's disposition, if it has one.

    A shape the backend refuses is SKIPPED, because the cell would exercise
    that refusal rather than the narrowing.  A shape it ACCEPTS and gets
    wrong is skipped here and pinned by a cell of its own at the end of this
    file, which asserts what the compiler does today rather than what it
    should: the generator keeps finding it, and the day it is fixed that cell
    fails and someone has to come back here and delete both entries.

    Pinned rather than `xfail`ed because no test in this suite uses `xfail`
    and `scripts/check_doc_counts.py` gates TESTING.md's breakdown as
    `passed + stress-deselected + skipped == collected`, which has no term
    for an xfailed test.  A pinning assertion has the property that matters —
    it fails when the defect is fixed — without making every future PR write
    a fourth number.
    """
    unsupported = _UNSUPPORTED_SHAPES.get((site, kind))
    if unsupported is not None:
        pytest.skip(f"the backend refuses the shape: {unsupported}")
    known_red = _KNOWN_RED.get((site, kind))
    if known_red is not None:
        pytest.skip(
            f"pinned by its own cell at the end of this file: {known_red}")


def test_every_unsupported_shape_says_so_in_the_compilers_words(
    tmp_path: Path,
) -> None:
    """An excluded product is excluded for a reason the COMPILER still gives.

    Without this, an entry outlives the refusal it names and the cell stays
    skipped after the shape becomes supported — an absent cell wearing a
    reason, which is the failure mode the exclusion list is meant to avoid.
    """
    for (site, kind), message in sorted(_UNSUPPORTED_SHAPES.items()):
        pre, slot, bad, _good, base = _KINDS[kind]
        source = _TEMPLATES[site][0](pre, slot, bad, base)
        ran = _cli("run", str(_write(tmp_path, source, "u.vera")))
        assert message in (ran.stdout + ran.stderr), (
            f"{site}/{kind} is excluded as unsupported, but the compiler no "
            f"longer says so:\n{(ran.stdout + ran.stderr)[-500:]}"
        )


def _ids(cell: tuple[str, int, str]) -> str:
    site, index, kind = cell
    return f"{site.replace(' ', '-')}[{index}]-{kind}"


def _read(tmp_path: Path, source: str, name: str) -> dict:
    """Verify and run *source*, as the obligation stream plus two verdicts."""
    path = _write(tmp_path, source, name)
    verified = _cli("verify", "--json", str(path))
    envelope = json.loads(verified.stdout)
    ran = _cli("run", str(path))
    return {
        "obligations": [
            (o["kind"], o["status"]) for o in envelope["obligations"]
            if o["kind"] in _NARROWING_KINDS
        ],
        "errors": [d.get("error_code") for d in envelope["diagnostics"]
                   if d.get("severity") == "error"],
        "refused": ran.returncode != 0,
        "run_output": (ran.stdout + ran.stderr)[-400:],
    }


@pytest.mark.parametrize("cell", _CELLS, ids=_ids)
def test_a_satisfying_value_passes(cell: tuple[str, int, str],
                                   tmp_path: Path) -> None:
    """The premise every other reading rests on.

    A cell whose program the compiler refuses outright would satisfy "never
    silently accepted" by refusing everything, which is coverage of nothing.
    """
    site, index, kind = cell
    _skip_or_xfail(site, kind)
    pre, slot, _bad, good, base = _KINDS[kind]
    r = _read(tmp_path, _TEMPLATES[site][index](pre, slot, good, base),
              "good.vera")
    assert not r["errors"], (
        f"{site}/{kind}: the SATISFYING value is refused "
        f"({r['errors']}), so the violating cell proves nothing"
    )
    assert not r["refused"], (
        f"{site}/{kind}: the satisfying value traps at run time:\n"
        f"{r['run_output']}"
    )


#: Sites the §2.6.5 predicate lowering has no scalar to tee a value into.
#:
#: Stated as a RULE over the cell rather than read from `GUARD_SITES`,
#: deliberately: the point of the reading below is that dropping a registry
#: entry must RED a generator cell, and a reading that consulted the registry
#: to decide what to expect would skip instead (R-1465 review, Finding 3).
def _lowerable(site: str, kind: str) -> tuple[bool, str]:
    """Can a guard be emitted for this cell's base at this position?"""
    if kind == "refined_array":
        # #1430: the element walk is a lowering of its own, wired at the two
        # function boundaries and the two closure ones, and NOT at the other
        # positions — so the answer is per position, read from the element
        # guard's own roster rather than from the slot-predicate one.  Before
        # that walk existed no position could emit anything for an element
        # refinement, which is what this arm used to say.
        if site in carriers.ELEMENT_GUARD_SITES:
            return (True, "")
        return (False, "the refinement is on the array ELEMENT, and the "
                       "element walk is not wired at this position "
                       "(`carriers.ELEMENT_GUARD_SITES`), so the slot's own "
                       "lowering has no predicate to emit")
    base = _KINDS[kind][4]
    construction = {
        s for sites in binders.CONSTRUCTION_SITES.values() for s in sites
    }
    if (site in construction
            and base not in narrowing.REFINED_CONSTRUCTION_SCALAR_BASES):
        return (False, "a construction store tees the value into one scalar "
                       "local, and this base has no scalar representation "
                       "(`narrowing.REFINED_CONSTRUCTION_SCALAR_BASES`)")
    return (True, "")


#: Positions whose guard is not a property of the position, so a cell cannot
#: expect one.  Hand-stated with the reason, NOT derived from `GUARD_SITES`.
_NOT_GUARDED_POSITIONS: dict[str, str] = {
    "effect-operation argument":
        "guarded for a BUILT-IN effect's operation and not for a "
        "user-declared one, so the answer belongs to the effect rather than "
        "to the position (#754, #1268) — this template happens to use `Exn`, "
        "and pinning a refusal here would pin the effect it chose",
    "State-op resume":
        "codegen wraps a `get` clause's net value, so the answer belongs to "
        "the clause's dispatch path rather than to the position (#1203)",
}


@pytest.mark.parametrize("cell", _CELLS, ids=_ids)
def test_a_site_that_can_be_guarded_refuses_rather_than_disclosing(
    cell: tuple[str, int, str], tmp_path: Path,
) -> None:
    """The third reading: a guard is PRESENT where one can be emitted.

    "Never silently accepted" is satisfied by an honest `tier3_unguarded`
    disclosure, which is right — but it means the matrix cannot tell a guard
    from its absence: dropping the `handler clause binder` entry from
    `GUARD_SITES` flips every affected status to `tier3_unguarded` and every
    cell above stays green (R-1465 review, measured: 0 of 133 executed cells
    red under that mutation).  This reading is what makes the drop visible.

    Its expectation is a RULE over the cell — a lowerable base at a position
    whose guard is a property of the position — and not a lookup in the
    registry, because a reading that asked the registry what to expect would
    agree with a registry that had just lost the entry.
    """
    site, index, kind = cell
    _skip_or_xfail(site, kind)
    not_guarded = _NOT_GUARDED_POSITIONS.get(site)
    if not_guarded is not None:
        pytest.skip(f"the position does not decide its guard: {not_guarded}")
    can_lower, why = _lowerable(site, kind)
    if not can_lower:
        pytest.skip(f"no guard can be emitted for this base: {why}")
    pre, slot, bad, _good, base = _KINDS[kind]
    r = _read(tmp_path, _TEMPLATES[site][index](pre, slot, bad, base),
              "bad.vera")
    assert r["errors"] or r["refused"], (
        f"{site}/{kind}: the value is refused by nothing — not by "
        f"verification, and not by the artifact — though a guard can be "
        f"emitted for this base at this position.  The stream says "
        f"{r['obligations']}:\n{r['run_output']}"
    )


@pytest.mark.parametrize("cell", _CELLS, ids=_ids)
def test_a_violating_value_is_never_silently_accepted(
    cell: tuple[str, int, str], tmp_path: Path,
) -> None:
    """The property, over the whole product.

    Two readings, in the order they failed: the narrowing is ON THE RECORD
    (#1448, #1455 recorded nothing), and unless the record DISCLOSES that the
    site is unguarded, the program does not run to completion with the bad
    value (#1445 recorded `tier3`, which claims a check, and had none).
    """
    site, index, kind = cell
    _skip_or_xfail(site, kind)
    pre, slot, bad, _good, base = _KINDS[kind]
    r = _read(tmp_path, _TEMPLATES[site][index](pre, slot, bad, base),
              "bad.vera")

    assert r["obligations"], (
        f"{site}/{kind}: a value the binder's declared type forbids reaches "
        f"it with NOTHING in the obligation stream — not violated, not "
        f"tier3, not tier3_unguarded.  `vera verify` reports a clean program"
    )
    disclosed_unguarded = any(
        status == "tier3_unguarded" for _k, status in r["obligations"]
    )
    assert r["errors"] or r["refused"] or disclosed_unguarded, (
        f"{site}/{kind}: the stream says {r['obligations']}, which claims a "
        f"check, and the program neither fails verification nor is refused "
        f"at run time:\n{r['run_output']}"
    )


# =====================================================================
# One position the matrix reaches only through a typed scrutinee
# =====================================================================

#: An ADT sub-pattern binder whose scrutinee is written INLINE as a
#: constructor call, rather than produced by a call or a `let`.
#:
#: Measured at `main` 6dc41d40 AND at `origin/release/v0.2.0` 8eca11c0 —
#: identical on both, so nothing in this release introduces or changes it.
#: The checker types `Some(0 - 5)` as `Option<Nat>` from the pattern and the
#: argument `0 - 5` as `Nat`, recording NO instantiated target for it, so
#: neither the constructor field nor the sub-pattern reads as a narrowing and
#: neither is obligated.  Code generation does plant the bind guard, so the
#: direction is an UNDER-COUNT of the Tier-3 runtime checks rather than a
#: false Tier 1: the run refuses `-5` with "Negative value bound into a @Nat
#: slot".  The matrix's own `ADT sub-pattern bind` cell routes the value
#: through a typed `src()` instead, where the narrowing is recorded
#: correctly, so this shape is pinned here on its own.
_INLINE_CTOR_SCRUTINEE = """public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Some(0 - 5) {
    Some(@Nat) -> @Nat.0,
    None -> 0 - 5
  }
}
"""


def test_the_inline_constructor_scrutinee_is_guarded(tmp_path: Path) -> None:
    """What DOES hold today: the artifact refuses the value."""
    r = _read(tmp_path, _INLINE_CTOR_SCRUTINEE, "inline.vera")
    assert r["refused"], r["run_output"]
    assert "@Nat" in r["run_output"], r["run_output"]


def test_the_inline_constructor_scrutinee_is_on_the_record(
    tmp_path: Path,
) -> None:
    """And that the guard above is counted.

    Silent at `main` 6dc41d40 and at `release/v0.2.0` 8eca11c0: the checker
    typed the constructor's argument against a pattern-derived expected type
    and recorded no instantiated target, so the narrowing was invisible to
    the walk while code generation guarded it — an under-count of the Tier-3
    checks.  Closed by recording the argument's field type at the
    constructor door; `tests/test_constructor_field_target.py` ranges over
    the position.
    """
    r = _read(tmp_path, _INLINE_CTOR_SCRUTINEE, "inline.vera")
    assert r["obligations"], r
    assert all(status != "verified" for _k, status in r["obligations"]), r


# =====================================================================
# The two defects the generator finds that this PR does not fix
# =====================================================================
#
# Pinned as what the compiler DOES, not as what it should: each assertion
# fails the day the defect is fixed, which is when the `_KNOWN_RED` entry
# above and the cell here are both meant to be deleted.

def test_1466_a_pair_represented_tuple_component_traps_on_a_value_it_admits(
    tmp_path: Path,
) -> None:
    """#1466, pinned. This asserts the DEFECT; see the issue for the class.

    A `@String`-based refinement as a tuple component at a boundary is
    guarded by a check that tees the component into one scalar local, so the
    predicate is evaluated against the `(ptr, len)` pair's pointer.
    `vera verify` proves it at Tier 1 and the artifact refuses `"x"`, whose
    `string_length` is 1.

    Measured identical at `main` 6dc41d40 and `release/v0.2.0` 8eca11c0.
    When #1466 lands this cell fails: replace it with the assertion that the
    satisfying value RUNS, and delete the `_KNOWN_RED` entry so the matrix
    covers the product again.
    """
    pre, slot, _bad, good, base = _KINDS["refined_string"]
    r = _read(tmp_path, _t_tuple_component(pre, slot, good, base), "b.vera")
    assert not r["errors"], r["errors"]
    assert r["refused"], (
        "#1466 appears to be FIXED — the satisfying value now runs.  Remove "
        "this cell, remove the ('tuple component', 'refined_string') entry "
        f"from _KNOWN_RED, and close the issue:\n{r['run_output']}"
    )
    assert "Refinement violation" in r["run_output"], r["run_output"]


def test_a_refined_element_type_at_a_clause_binder_is_recorded(
    tmp_path: Path,
) -> None:
    """#1430's clause-binder instance: RECORDED, and honestly unguarded.

    Measured on `release/v0.2.0` and on `main`: `handle[Exn<Array<Int>>] {
    throw(@Array<Pos>) -> … }` over `throw([0 - 5])` verified clean with NO
    obligation at all, compiled to no guard, and ran — the refinement is on
    the array ELEMENT, so the slot itself carries no predicate and the
    narrowing test saw nothing to obligate.  The element question is now
    asked at this position too, so the site is on the record.

    It is `tier3_unguarded` rather than `tier3` deliberately: the element
    walk is wired at the function and closure boundaries and not here, so
    claiming a check would promise one nothing emits.  The cell asserts BOTH
    — the record and the absence of a guard — because either alone is
    satisfied by the state this replaces.
    """
    pre, slot, bad, _good, base = _KINDS["refined_array"]
    r = _read(tmp_path, _TEMPLATES["handler clause binder"][0](
        pre, slot, bad, base), "bad.vera")
    assert r["obligations"], (
        f"the clause binder raises nothing for an element refinement: {r}"
    )
    assert any(status == "tier3_unguarded"
               for _k, status in r["obligations"]), r["obligations"]
