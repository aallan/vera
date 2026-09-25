"""The class instrument: every guarded position, every WASM representation.

`vera/binders.py` says which positions code generation plants a §2.6.5
refinement guard at.  The sibling generator
(`test_binder_position_generator.py`) asks whether a VIOLATING value is ever
silently accepted there.  This file asks the opposite question, the one #1466
found nothing asking:

    **does the guard accept the values it admits?**

A guard materialises the guarded value by binding `@<base>.0` to a WASM local,
and a base's representation is not one local for every base: `@String` and
`@Array<T>` are `(ptr, len)` pairs, and the slot environment reads the length
from the local AFTER the pointer.  A guard that binds one local for a pair base
evaluates its predicate against the pointer and whatever local happens to
follow it — so the artifact refuses a value that SATISFIES the refinement, on a
program `vera verify` reports clean.  That is the class: a guard whose value
binding is CONVENTION rather than a property of the type.

It has a second face, which this matrix found and #1439 names.  Where the
convention was a roster rather than an offset — the `State` write guard asked
which bases a CONSTRUCTION store can tee into a scalar local — a base whose
value is exactly the one local the store tees was declined anyway, while the
verifier went on recording the write `tier3`.  Same disease, opposite
symptom: there the artifact refuses what it admits, here it admits what it
should refuse, and both end at a value binding that was not derived from the
representation.

The axes are the POSITIONS — from `binders.GUARD_SITES`, never a list written
here — crossed with the REPRESENTATIONS (`_REPRS`: five scalar bases, the two
pair bases, four heap/handle bases).  Each cell reads three things that must
agree:

1. *The record.*  What the obligation stream says about the position: a
   `tier3` guarded claim, a `tier3_unguarded` disclosure, or a `verified`
   static discharge.  Expected from a RULE over the cell
   (:func:`_expected_record`) rather than from a lookup in the registry, so
   dropping a registry entry reds a cell instead of moving the expectation
   with it.
2. *The satisfying value runs.*  #1466's own reading, and the one no
   instrument in this family had: a guard may not refuse a value its
   refinement admits.
3. *The violating value is refused* — statically where the value is
   refutable, by the artifact otherwise, and then under the ROLE this
   position prints, so a guard cannot pass by trapping in another position's
   name.

Red at `origin/release/v0.2.0` 1cf5c6a9, before the fix in this PR.  Every red
cell is a pair base at the one position whose guard binds a single local:

| cell | reading at the base tip |
|---|---|
| tuple component [parameter] x `@String` | traps on `"x"`, whose `string_length` is 1 |
| tuple component [parameter] x `@Array<Int>` | traps on `[1]` |
| tuple component [return] x `@String` | traps on `"x"` |
| tuple component [return] x `@Array<Int>` | traps on `[1]` |
| tuple component [nested] x `@String` | traps on `"x"` |
| tuple component [nested] x `@Array<Int>` | traps on `[1]` |

and, for the #1439 half, at `7f9a9d85` with the `State write boundary
[opaque]` route in place and the fix not yet applied — every one a HANDLE
base, admitted by a write the record calls `tier3`:

| cell | reading at the base tip |
|---|---|
| State write boundary [opaque] x `@Map<String, Int>` | violating value stored, module carries no check |
| State write boundary [opaque] x `@Set<Int>` | as above |
| State write boundary [opaque] x `@Tuple<Int, Int>` | as above |
| State write boundary [opaque] x `@Option<Int>` | as above |

The first four are the instances #1466 enumerates; the two depth-2 rows are
the same decomposition one level down, found by this matrix.  Every other
position binds a pair correctly — a bare parameter through its two consecutive
WASM params, a pair return and a closure's through two consecutive spill
locals — which is what makes the decomposition's single local the mechanism at
fault rather than the convention it departs from.

The `@Byte` row's value comes from a `@Byte`-returning helper rather than a
literal, because the checker coerces an int literal to `@Byte` at some
positions and not others.  Measured across every route of this file rather
than remembered — and recomputed by
`test_the_byte_literal_tally_is_what_the_routes_measure`, since a tally
written out by hand stops being a measurement the moment the axis grows
(CodeRabbit on PR #1478 caught this one two routes stale): THIRTEEN of the
twenty-seven refuse the literal.  Seven E202 (an array element, and six of
the seven tuple-component routes), one E121 (the seventh, the return),
three E213 (a declared constructor field and both ADT sub-pattern routes),
one E170 (a `Map` value) and one E314 (a match binding).  A literal would
have excluded all thirteen for a reason that has nothing to do with the
guard.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from tests import guard_emitter_scan
from vera import binders, carriers, narrowing

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

#: The obligation kind a refinement narrowing is recorded under.
_NARROWING_KINDS = ("refine_bind",)


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, cwd=_PKG_PARENT, timeout=300,
    )


def test_the_cli_under_test_is_this_checkout() -> None:
    """The premise under every measurement below.

    ``python -m`` puts the working directory AHEAD of ``PYTHONPATH``, so a
    subprocess launched from another checkout measures that checkout's
    compiler while reporting about this one.  No cell would notice, which is
    why the canary is a test of its own.
    """
    env = dict(os.environ)
    env["PYTHONPATH"] = _PKG_PARENT
    got = subprocess.run(
        [sys.executable, "-c", "import vera; print(vera.__file__)"],
        capture_output=True, text=True, encoding="utf-8", check=True,
        env=env, cwd=_PKG_PARENT, timeout=300,
    ).stdout.strip()
    assert got == str(Path(vera.__file__).resolve()), (
        f"the CLI subprocess imports {got}, not the checkout under test "
        f"({Path(vera.__file__).resolve()})"
    )


# =====================================================================
# Axis 1: the representations
# =====================================================================


class _Instance:
    """One representation at one value: the declarations, and the expression
    under test."""

    def __init__(self, pre: str, value: str, base: str, safe: str) -> None:
        self.pre = pre
        self.value = value
        self.base = base
        self.safe = safe


class _Repr:
    """One representation row of the matrix."""

    def __init__(
        self, *, decls: str, base: str, good: str, bad: str,
        repr_class: str, safe: str, witness: str,
        producer: str | None = None,
    ) -> None:
        #: Declarations every program of this row needs: the `type R = { … }`
        #: and any helper its predicate calls.
        self.decls = decls
        #: The base's spelling, for a position that needs the UNREFINED type
        #: (the payload a clause binder narrows, an enclosing `Option<…>`).
        self.base = base
        #: A value satisfying the refinement, and one violating it — either
        #: written directly at the position, or fed to *producer*.
        self.good = good
        self.bad = bad
        #: "scalar" (one local of the base's width), "pair" ((ptr, len) in two
        #: consecutive locals), "handle" (one i32 that points at or indexes
        #: the value).
        self.repr_class = repr_class
        #: A satisfying value of the BASE type, for a second binder a program
        #: needs to be well-formed, so the value under test is in one place.
        self.safe = safe
        #: The predicate as a trap message RENDERS it, so a refusal can be
        #: attributed to this refinement rather than to something incidental
        #: the program also does.  A `@Nat` / `@Byte` base conjoins its
        #: implicit range in front, so the witness is the written conjunct.
        self.witness = witness
        #: A declaration template producing the value from a call, for a base
        #: whose literal the checker will not coerce at every position.
        self.producer = producer

    def instance(self, which: str) -> _Instance:
        value = self.good if which == "good" else self.bad
        if self.producer is None:
            return _Instance(self.decls, value, self.base, self.safe)
        return _Instance(
            self.decls + self.producer.format(value=value), "produce(())",
            self.base, self.safe,
        )


_R = "type R = { @%s | %s };\n"

_BYTE_PRODUCER = """
private fn produce(@Unit -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {value}
}}
"""

_REPRS: dict[str, _Repr] = {
    "int": _Repr(
        decls=_R % ("Int", "@Int.0 > 0"), base="Int",
        good="5", bad="0 - 5", repr_class="scalar", safe="5",
        witness="@Int.0 > 0",
    ),
    "nat": _Repr(
        decls=_R % ("Nat", "@Nat.0 > 0"), base="Nat",
        good="5", bad="0", repr_class="scalar", safe="5",
        witness="@Nat.0 > 0",
    ),
    "float64": _Repr(
        decls=_R % ("Float64", "@Float64.0 > 0.0"), base="Float64",
        good="1.0", bad="0.0", repr_class="scalar", safe="1.0",
        witness="@Float64.0 > 0.0",
    ),
    "bool": _Repr(
        decls=_R % ("Bool", "@Bool.0 == true"), base="Bool",
        good="true", bad="false", repr_class="scalar", safe="true",
        witness="@Bool.0 == true",
    ),
    "byte": _Repr(
        decls=_R % ("Byte", "@Byte.0 < 10"), base="Byte",
        good="3", bad="200", repr_class="scalar", safe="3",
        witness="@Byte.0 < 10", producer=_BYTE_PRODUCER,
    ),
    "string": _Repr(
        decls=_R % ("String", "string_length(@String.0) > 0"), base="String",
        good='"x"', bad='""', repr_class="pair", safe='"x"',
        witness="string_length(@String.0) > 0",
    ),
    "array": _Repr(
        decls=_R % ("Array<Int>", "array_length(@Array<Int>.0) > 0"),
        base="Array<Int>", good="[1]", bad="[]", repr_class="pair",
        safe="[1]", witness="array_length(@Array<@Int>.0) > 0",
    ),
    "map": _Repr(
        decls=_R % ("Map<String, Int>", "map_size(@Map<String, Int>.0) > 0"),
        base="Map<String, Int>", good='map_insert(map_new(), "a", 1)',
        bad="map_new()", repr_class="handle",
        safe='map_insert(map_new(), "a", 1)',
        witness="map_size(@Map<@String, @Int>.0) > 0",
    ),
    "set": _Repr(
        decls=_R % ("Set<Int>", "set_size(@Set<Int>.0) > 0"),
        base="Set<Int>", good="set_add(set_new(), 1)", bad="set_new()",
        repr_class="handle", safe="set_add(set_new(), 1)",
        witness="set_size(@Set<@Int>.0) > 0",
    ),
    # A `Tuple` value is not Eq-comparable (E243 at the base tip), so the
    # predicate reads a component through a helper.  A vacuous `| true` would
    # read as coverage, which TESTING.md § Class Instruments calls worse than
    # an absent row.
    "tuple": _Repr(
        decls=(
            "type R = { @Tuple<Int, Int> | fst(@Tuple<Int, Int>.0) > 0 };\n\n"
            "private fn fst(@Tuple<Int, Int> -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  let Tuple<@Int, @Int> = @Tuple<Int, Int>.0;\n  @Int.1\n}\n"
        ),
        base="Tuple<Int, Int>", good="Tuple(1, 1)", bad="Tuple(0 - 1, 1)",
        repr_class="handle", safe="Tuple(1, 1)",
        witness="fst(@Tuple<@Int, @Int>.0) > 0",
    ),
    # The trap renders a constructor call in a predicate as `<expr>`, so the
    # witness stops at the comparison rather than claiming text the message
    # does not carry.
    "option": _Repr(
        decls=_R % ("Option<Int>", "@Option<Int>.0 == Some(1)"),
        base="Option<Int>", good="Some(1)", bad="None",
        repr_class="handle", safe="Some(1)",
        witness="@Option<@Int>.0 == ",
    ),
}


def test_every_representation_class_is_present() -> None:
    """The axis covers all three shapes a guard has to bind.

    A matrix that lost its pair rows would be green for exactly the defect
    #1466 reports, so the axis asserts its own shape rather than trusting the
    table above to keep them.
    """
    classes = {r.repr_class for r in _REPRS.values()}
    assert classes == {"scalar", "pair", "handle"}, classes
    for wanted in ("scalar", "pair", "handle"):
        rows = [n for n, r in _REPRS.items() if r.repr_class == wanted]
        assert len(rows) >= 2, (wanted, rows)


# =====================================================================
# Axis 2: the positions
# =====================================================================
#
# Each template takes one representation at one value and returns a complete
# program routing that value into the named position.  Where a position needs
# a second binder filled to be well-formed, that one takes `x.safe`.

def _t_call_argument(x: _Instance) -> str:
    return x.pre + f"""
private fn take(@R -> @Int)
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
  take({x.value})
}}
"""


def _t_call_argument_where(x: _Instance) -> str:
    """The callee is a `where` helper — #1455's own spelling."""
    return x.pre + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  h({x.value})
}}
where {{
  fn h(@R -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{
    1
  }}
}}
"""


def _t_return_type(x: _Instance) -> str:
    return x.pre + f"""
private fn h(@Unit -> @R)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {x.value}
}}

public fn f(@Unit -> @R)
  requires(true)
  ensures(true)
  effects(pure)
{{
  h(())
}}
"""


def _t_let_binding(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @R = {x.value};
  1
}}
"""


def _t_match_binding(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {x.value} {{
    @R -> @R.0
  }}
}}
"""


def _t_adt_subpattern(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Option<{x.base}> = Some({x.value});
  match @Option<{x.base}>.0 {{
    Some(@R) -> @R.0,
    None -> {x.safe}
  }}
}}
"""


def _t_tuple_destructure(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  let Tuple<@Int, @R> = Tuple(1, {x.value});
  @R.0
}}
"""


def _t_constructor_field(x: _Instance) -> str:
    return x.pre + f"""
private data Box {{
  MkBox(R)
}}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{{
  MkBox({x.value})
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match build(()) {{
    MkBox(@R) -> 1
  }}
}}
"""


def _t_tuple_component_param(x: _Instance) -> str:
    """#1466's own spelling: the component crosses a PARAMETER boundary."""
    return x.pre + f"""
private fn take(@Tuple<R, Int> -> @Int)
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
  take(Tuple({x.value}, 1))
}}
"""


def _t_tuple_component_return(x: _Instance) -> str:
    """The same decomposition, from the RETURN epilogue."""
    return x.pre + f"""
private fn mk(@Unit -> @Tuple<R, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  Tuple({x.value}, 1)
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Tuple<R, Int> = mk(());
  1
}}
"""


def _t_tuple_component_nested(x: _Instance) -> str:
    """One level deeper — the decomposition's own recursion rather than the
    call into it."""
    return x.pre + f"""
private fn take(@Tuple<Tuple<R, Int>, Int> -> @Int)
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
  take(Tuple(Tuple({x.value}, 1), 1))
}}
"""


def _t_tuple_component_after_pair(x: _Instance) -> str:
    """The guarded component is NOT the first one, and the component before it
    is a PAIR.

    Every other tuple route puts the refined component first, where its
    offset is 4 whatever the layout rule says, so no cell of theirs can see a
    disagreement about how wide a pair is.  Here the guarded component sits
    BEHIND one, so its offset IS the pair's size and the decomposition has to
    reach it where the constructor put it.

    Measured, with the emitter advancing by a rule of its own (`offset -= 4`
    for a pair, the shape this position had before the layout became one
    table): the three HANDLE rows of this route red — `map`, `set`, `option`,
    whose i32 component is read four bytes early — and the other three tuple
    routes stay green.  The scalar rows stay green too, and for a reason
    worth knowing: an i64 component re-aligns to 8 from either 8 or 12, so
    alignment masks the shift for exactly the bases whose width exceeds it.

    Mutating the shared `helpers.FIELD_SIZES` is a DIFFERENT experiment and
    an earlier draft of this docstring got it wrong, so the correction is
    worth keeping: it does not "move the constructor and every reader
    together".  It moves everything that reads the table and leaves behind
    anything that states the widths itself, which is why widening it broke
    `match MkBox("hello", 77) { MkBox(@String, @Int) -> … }` into printing
    77000 rather than 5077 (PR #1478 review).  Those copies are gone now,
    and `tests/test_field_layout_one_source_1466.py` is the cell that holds
    them gone — behaviourally, by widening the one table in a scratch copy
    of the compiler and asserting every round trip still agrees.  This
    matrix stays about the BINDING; that file is about the LAYOUT.
    """
    return x.pre + f"""
private fn take(@Tuple<String, R> -> @Int)
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
  take(Tuple("a", {x.value}))
}}
"""


def _t_tuple_component_after_two_pairs(x: _Instance) -> str:
    """The guarded component sits behind TWO pair components.

    One pair in front already makes the guarded component's offset the
    pair's size; two make it twice that, so a decomposition that advanced by
    a rule of its own would be wrong by eight rather than four — and a
    four-byte error is the one an i64 component's alignment can absorb.
    """
    return x.pre + f"""
private fn take(@Tuple<String, Array<Int>, R> -> @Int)
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
  take(Tuple("a", [1], {x.value}))
}}
"""


def _t_tuple_component_third_of_three(x: _Instance) -> str:
    """A scalar, then a pair, then the guarded component.

    The offsets before it are of two different widths, so an advance that is
    right for one and wrong for the other lands here.
    """
    return x.pre + f"""
private fn take(@Tuple<Int, String, R> -> @Int)
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
  take(Tuple(1, "a", {x.value}))
}}
"""


def _t_tuple_component_depth_three(x: _Instance) -> str:
    """Three levels of nesting rather than two — the recursion, twice."""
    return x.pre + f"""
private fn take(@Tuple<Tuple<Tuple<R, Int>, Int>, Int> -> @Int)
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
  take(Tuple(Tuple(Tuple({x.value}, 1), 1), 1))
}}
"""


def _t_adt_field_after_pair(x: _Instance) -> str:
    """A user ADT whose guarded field sits behind a pair one, bound by a
    constructor sub-pattern — the extraction walk rather than the tuple
    decomposition."""
    return x.pre + f"""
private data Box {{
  MkBox(String, R)
}}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{{
  MkBox("a", {x.value})
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match build(()) {{
    MkBox(@String, @R) -> 1
  }}
}}
"""


def _t_adt_field_after_pair_destructured(x: _Instance) -> str:
    """The same ADT, bound by a `let`-destructure instead of a match arm."""
    return x.pre + f"""
private data Box {{
  MkBox(String, R)
}}

private fn build(@Unit -> @Box)
  requires(true)
  ensures(true)
  effects(pure)
{{
  MkBox("a", {x.value})
}}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let MkBox<@String, @R> = build(());
  1
}}
"""


def _t_array_element(x: _Instance) -> str:
    return x.pre + f"""
private fn take(@Array<R> -> @Int)
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
  take([{x.value}])
}}
"""


def _t_map_value(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @Map<String, R> = map_insert(map_new(), "a", {x.value});
  1
}}
"""


def _t_closure_argument(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(fn(@R -> @Int) effects(pure) {{ 1 }}, {x.value})
}}
"""


def _t_closure_return(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  apply_fn(fn(@Unit -> @R) effects(pure) {{ {x.value} }}, ())
}}
"""


def _t_state_write(x: _Instance) -> str:
    return x.pre + f"""
public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<R>](@R = {x.value}) {{
    put(@R) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}
"""


def _t_state_write_opaque(x: _Instance) -> str:
    """The same write, with the value produced by a CALL.

    The literal route above is refused by the CHECKER for four of the bases
    — `map_new()` where a `{ @Map<…> | … }` is expected is not a subtype —
    so its violating twin never reaches the artifact and the cell cannot
    tell a guard from its absence.  Routing the value through a producer
    leaves the checker nothing to refuse and the guard everything: this is
    the route that measured #1439's remaining half, where the write was
    recorded `tier3` and the module carried no check at all.
    """
    return x.pre + f"""
private fn produce_state(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {x.value}
}}

public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<R>](@R = produce_state(())) {{
    put(@R) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}
"""


def _t_state_write_put(x: _Instance) -> str:
    """The `put` argument — the second of the three writes the position
    covers, and one the matrix did not route until the PR #1478 reviewer
    measured its handle rows `tier3` with no guard."""
    return x.pre + f"""
private fn produce_state(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {x.value}
}}

public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<R>](@R = {x.safe}) {{
    put(@R) -> {{ resume(()) }}
  }} in {{
    put(produce_state(()));
    get(())
  }}
}}
"""


def _t_state_write_with(x: _Instance) -> str:
    """A clause's `with @R = …` override — the third write."""
    return x.pre + f"""
private fn produce_state(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {x.value}
}}

public fn f(@Unit -> @{x.base})
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<R>](@R = {x.safe}) {{
    put(@R) -> {{ resume(()) }} with @R = produce_state(())
  }} in {{
    put({x.safe});
    get(())
  }}
}}
"""


def _t_handler_clause_binder(x: _Instance) -> str:
    """The clause binds the thrown payload at its own, narrower type."""
    return x.pre + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<{x.base}>] {{
    throw(@R) -> {{ 1 }}
  }} in {{
    throw({x.value})
  }}
}}
"""


def _t_throw_payload(x: _Instance) -> str:
    """#1268's position: the op-call argument, guarded by the emitter the
    translation context is HANDED rather than by a code-generation method
    holding both halves."""
    return x.pre + f"""
public fn f(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[Exn<R>] {{
    throw(@R) -> {{ 1 }}
  }} in {{
    throw({x.value})
  }}
}}
"""


class _Route:
    """One syntactic route to one position, and the role its trap prints."""

    def __init__(
        self, name: str, build: object, role: str, *,
        constructs: bool = False, store_reaches: bool = True,
    ) -> None:
        self.name = name
        self.build = build
        #: Whether the route STORES the value into a declared refined slot on
        #: its way to the position under test.  A construction store is
        #: obligated in its own right and discloses for a base it cannot tee,
        #: so a route that passes through one has the STORE's record, not the
        #: position's — measured on the ADT routes, whose `MkBox(String, R)`
        #: field is a declared refinement where `Some(v)`'s is a type
        #: parameter and records nothing.
        self.constructs = constructs
        #: Whether that store's guard REACHES this component.  Measured
        #: False for the depth-three route: the checker threads a
        #: construction's target type through one nested literal (#1412 F3)
        #: and not through two, so the store emits nothing at that depth and
        #: the BOUNDARY is what refuses the value — under its own role.
        self.store_reaches = store_reaches
        #: The ROLE word this position's refinement-violation message
        #: carries, so a guard cannot pass by trapping under another
        #: position's name.  The pattern-bind and construction sites all
        #: print `<type> binding` under a `where` naming the site ("let
        #: binding", "State cell init", "Tuple(…) construction", …); the two
        #: boundaries print "parameter" / "return value"; the tuple
        #: decomposition adds "(tuple component)" to those; the #1268 payload
        #: prints "payload".
        self.role = role


#: Position -> the routes that reach it.  A position with several entries has
#: several EMITTER call sites worth separating: the tuple decomposition is
#: reached from the parameter prologue, from the return epilogue and from its
#: own recursion, and #1466 was all three.
_TEMPLATES: dict[str, tuple[_Route, ...]] = {
    "call argument": (
        _Route("top-level", _t_call_argument, "parameter"),
        _Route("where-helper", _t_call_argument_where, "parameter"),
    ),
    "return type": (_Route("", _t_return_type, "return value"),),
    "closure argument": (_Route("", _t_closure_argument, "parameter"),),
    "closure return": (_Route("", _t_closure_return, "return value"),),
    "let binding": (_Route("", _t_let_binding, "binding"),),
    "match binding": (_Route("", _t_match_binding, "binding"),),
    "tuple destructure": (_Route("", _t_tuple_destructure, "binding"),),
    "constructor field": (_Route("", _t_constructor_field, "binding"),),
    "tuple component": (
        _Route("parameter", _t_tuple_component_param, "tuple component"),
        _Route("return", _t_tuple_component_return, "tuple component"),
        _Route("nested", _t_tuple_component_nested, "tuple component"),
        _Route("after-pair", _t_tuple_component_after_pair, "tuple component"),
        _Route("after-two-pairs", _t_tuple_component_after_two_pairs,
               "tuple component"),
        _Route("third-of-three", _t_tuple_component_third_of_three,
               "tuple component"),
        _Route("depth-three", _t_tuple_component_depth_three,
               "tuple component", store_reaches=False),
    ),
    "ADT sub-pattern bind": (
        _Route("", _t_adt_subpattern, "binding"),
        _Route("after-pair", _t_adt_field_after_pair, "binding",
               constructs=True),
        _Route("destructured-after-pair", _t_adt_field_after_pair_destructured,
               "binding", constructs=True),
    ),
    "array element": (_Route("", _t_array_element, "binding"),),
    "map value": (_Route("", _t_map_value, "binding"),),
    "State write boundary": (
        _Route("literal", _t_state_write, "binding"),
        _Route("opaque", _t_state_write_opaque, "binding"),
        _Route("put", _t_state_write_put, "binding"),
        _Route("with", _t_state_write_with, "binding"),
    ),
    "handler clause binder": (
        _Route("", _t_handler_clause_binder, "binding"),
    ),
}

#: Positions the class reaches that `GUARD_SITES` cannot answer for, with the
#: reason.  The registry deliberately holds no entry for an effect operation's
#: argument — the answer is a property of the EFFECT, not of the position
#: (#754, #1268) — and the #1268 emitter is nonetheless one of the emitters
#: that binds a slot, so the class reaches it and the matrix measures it.
_EXTRA_POSITIONS: dict[str, tuple[str, tuple[_Route, ...]]] = {
    "throw payload": (
        "the `throw` payload's guard is emitted through the bound emitter the "
        "translation context is handed (#1268), whose answer is a property of "
        "the effect rather than of the position — so `GUARD_SITES` holds no "
        "entry for it while the class still reaches its binding",
        (_Route("", _t_throw_payload, "payload"),),
    ),
}

_ALL_ROUTES: dict[str, tuple[_Route, ...]] = {
    **_TEMPLATES,
    **{name: routes for name, (_why, routes) in _EXTRA_POSITIONS.items()},
}


def test_every_guarded_position_is_templated() -> None:
    """The matrix's own completeness, against `binders.GUARD_SITES`.

    A position registered as taking a refinement-predicate guard with no
    program that reaches it fails HERE, rather than being a row nobody
    noticed was missing — the hole the registry closes one level down,
    closed again one level up.
    """
    registered = binders.guarded_sites("refinement_predicate")
    missing = sorted(registered - set(_TEMPLATES))
    assert not missing, (
        f"{missing} take a refinement-predicate guard per "
        f"`binders.GUARD_SITES`, and no template reaches them"
    )
    stale = sorted(set(_TEMPLATES) - registered)
    assert not stale, (
        f"{stale} are templated but no longer registered as guarded positions"
    )


def test_every_element_guard_boundary_is_templated() -> None:
    """The element-guard roster's boundaries are measured here too.

    `carriers.ELEMENT_GUARD_SITES` names the four boundaries an element loop
    is planted at.  Their ELEMENT property is #1430's instrument
    (`test_element_facts_statable_1430.py`) and is not repeated here — but a
    boundary absent from this matrix would leave its SLOT guard unmeasured,
    so the two rosters are held to cover each other rather than each
    assuming the other does.
    """
    missing = sorted(set(carriers.ELEMENT_GUARD_SITES) - set(_TEMPLATES))
    assert not missing, (
        f"{missing} carry an element guard and are not templated here"
    )


def test_no_extra_position_is_unexplained() -> None:
    assert all(reason.strip() for reason, _ in _EXTRA_POSITIONS.values())


# =====================================================================
# The roster: where the decomposition's emitter is actually wired
# =====================================================================

#: The call sites of `_emit_component_refinement_guards`, as
#: `enclosing function/role`.  Held to the emitter by the shared scan, so a
#: fifth wiring site cannot appear without this roster — and the matrix routes
#: beside it — being updated.  `_emit_component_refinement_guards/?` is the
#: decomposition's own recursion, whose role is the caller's variable rather
#: than a literal; the `nested` route is its cell.
_COMPONENT_GUARD_SITES: dict[str, str] = {
    "tuple component [parameter]": "_compile_fn/parameter",
    "tuple component [return]": "_compile_postconditions/return value",
    "tuple component [closure parameter]": "_compile_lifted_closure/parameter",
    "tuple component [closure return]":
        "_compile_lifted_closure/return value",
    "tuple component [nested]": "_emit_component_refinement_guards/?",
}


def _component_emitter_sites() -> set[str]:
    return guard_emitter_scan.emitter_call_sites(
        "_emit_component_refinement_guards", drop_self=False)


def test_the_boundary_guard_roster_matches_where_it_is_wired() -> None:
    """Every roster entry names a call site, and every call site is named.

    The same shape #1430 gives its element roster, over the emitter this
    matrix is about, and through the same scan — so "where guards are
    emitted" is derived once for both.
    """
    assert _component_emitter_sites() == set(
        _COMPONENT_GUARD_SITES.values()), (
        f"the boundary-guard roster and the emitter's call sites disagree: "
        f"wired={sorted(_component_emitter_sites())} "
        f"named={sorted(set(_COMPONENT_GUARD_SITES.values()))}"
    )


def test_no_module_states_the_heap_field_layout_twice() -> None:
    """The layout is stated ONCE, and that stays true.

    Construction lays a constructed object out by one rule, and four walks
    read it back — the destructure, the match extraction, the nested tag
    walk, and this matrix's own tuple decomposition.  They were four hand
    copies of the same two dicts that happened to agree; a change to one
    would have moved construction and left a reader on the old widths, which
    is the defect class this file is about, one layer down.

    So the unification is worth what keeps it: this reads the modules rather
    than a comment, and a fifth copy under any name is a row.  The single
    permitted home is `vera/wasm/helpers.py`.
    """
    copies = guard_emitter_scan.local_layout_tables()
    assert not copies, (
        f"a heap-field size/alignment table is declared outside "
        f"`{guard_emitter_scan.LAYOUT_OWNER}`: "
        + "; ".join(f"{mod}: {lines}" for mod, lines in sorted(copies.items()))
    )


def test_the_layout_scan_would_see_a_hand_copy() -> None:
    """And the scan can FAIL, in every spelling of the same table.

    A source-pattern scan recognises one SPELLING, and a hand copy need not
    use it: single-quoted keys, `"unit"` written first, a `dict(...)` call
    (CodeRabbit on PR #1478).  Reading the AST makes the shape the test —
    WAT type names mapped to byte counts — so these are driven from strings
    rather than from a file, beside the forms that are NOT layout tables and
    must stay unreported.
    """
    import ast as _ast

    def sees(source: str) -> bool:
        return any(guard_emitter_scan._is_layout_table(node)
                   for node in _ast.walk(_ast.parse(source)))

    for spelling in (
        '_sizes = {"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8}',
        "_aligns = {'i32': 4, 'i64': 8, 'f64': 8, 'i32_pair': 4}",
        'SIZES = {"unit": 0, "i32": 4, "i64": 8}',
        'widths = dict(i32=4, i32_pair=8)',
        'X = {"i32_pair": 8}',
    ):
        assert sees(spelling), f"the scan misses {spelling!r}"
    for innocent in (
        'strides = {"Int": 8, "Nat": 8, "Bool": 1, "Byte": 1}',
        'loads = {"i32": "i32.load", "i64": "i64.load"}',
        'wt = self._type_expr_to_wasm_type(comp_te)',
        'flags = {"i32": True}',
    ):
        assert not sees(innocent), (
            f"the scan reports {innocent!r}, which is not a layout table"
        )


def test_no_guard_binds_a_pair_on_adjacency() -> None:
    """Every guarded value's local comes from the helper, a parameter, or a
    width that is one word — never from two `alloc_local` calls in a row.

    This is the completeness question the PR's own reviews kept answering
    better than the previous check did.  Reading the ARGUMENT at each
    emitter call site sees a plain name and stops there, so a pair allocated
    eighteen lines up inside an `if is_pair:` branch is invisible — which is
    how three sites survived two rounds (PR #1478 review, F9 and F10).  The
    scan traces each emitter's value argument back to the assignments that
    produce it within the enclosing FUNCTION, following a list an allocation
    is appended to and a comprehension that unpacks it, and classifies what
    it finds.

    Two classifications are findings.  `FROM_ADJACENT_PAIR` is a pair bound
    on the adjacency of two calls, which is the convention this PR replaces.
    `FROM_UNKNOWN` is a site the walk cannot account for — not a defect, but
    not a thing anyone has looked at either, and a scan that shrugs at what
    it cannot classify reports whatever it happens to understand.
    """
    provenance = guard_emitter_scan.slot_binding_provenance()
    assert provenance, "the scan found no guard emitter call sites at all"
    findings = {
        site: kind for site, kind in provenance.items()
        if kind in (guard_emitter_scan.FROM_ADJACENT_PAIR,
                    guard_emitter_scan.FROM_UNKNOWN)
    }
    assert not findings, (
        "a guarded value's local is bound by adjacency or by a route this "
        "scan cannot follow: "
        + "; ".join(f"{s} -> {k}" for s, k in sorted(findings.items()))
    )


def test_the_slot_binding_roster_matches_the_emitters() -> None:
    """Every rostered emitter exists and takes its value where the roster
    says, and every emitter that takes one is rostered.

    The family's other two rosters are held to the tree; this one was read
    by nothing, so `_emit_boundary_refinement_guard` could sit outside it
    with nobody the wiser (PR #1478 review, F11).  Held both ways here: each
    entry's function is found in `vera/` and its parameter at the recorded
    index carries the recorded name, and any method whose signature has a
    `value_local` parameter must be in the roster.
    """
    import ast as _ast

    found: dict[str, list[str]] = {}
    for path in guard_emitter_scan.codegen_sources():
        tree = _ast.parse(path.read_text(encoding="utf-8"))
        for node in _ast.walk(tree):
            if isinstance(node, _ast.FunctionDef):
                found[node.name] = [a.arg for a in node.args.args]

    for name, (index, keyword) in sorted(
            guard_emitter_scan.SLOT_BINDING_EMITTERS.items()):
        assert name in found, f"{name} is rostered and does not exist"
        args = found[name]
        # `self` is argument zero; the roster counts the CALL's arguments.
        position = index + 1
        assert position < len(args) and args[position] == keyword, (
            f"{name} takes {keyword!r} at call position {index}, and its "
            f"signature reads {args}"
        )

    unrostered = sorted(
        name for name, args in found.items()
        if "value_local" in args
        and name not in guard_emitter_scan.SLOT_BINDING_EMITTERS
        and not name.startswith("bind_slot_value")
    )
    assert not unrostered, (
        f"{unrostered} take a guarded value's local and are not in "
        f"`SLOT_BINDING_EMITTERS`, so the provenance scan does not read them"
    )


def test_the_provenance_scan_reaches_the_bound_emitter() -> None:
    """The #1268 position is INSTALLED rather than called by name, and it
    binds a pair.

    `emitter = self._refinement_guard_emitter` then `emitter(te, local, …)`
    is an `ast.Name` call, invisible to a scan matching attribute calls —
    so that one position contributed no provenance key at all and a hand
    spill there was green (PR #1478 review, F11).  The local's name is
    derived from the assignment rather than guessed, and the cell asserts
    the site is now classified.
    """
    provenance = guard_emitter_scan.slot_binding_provenance()
    payload_sites = [
        site for site in provenance
        if "_emit_exn_payload_refine_guard" in site
    ]
    assert payload_sites, (
        "the `throw` payload's bound emitter contributes no provenance, so "
        "the one position whose emitter is installed is unread"
    )
    # Both branches of that site are read: the pair takes the helper, the
    # scalar one local of its own width.  What matters is that neither is a
    # finding, which is what the site being invisible used to guarantee.
    assert all(
        provenance[s] in (guard_emitter_scan.FROM_HELPER,
                          guard_emitter_scan.FROM_ONE_LOCAL,
                          guard_emitter_scan.FROM_COMPUTED_WIDTH)
        for s in payload_sites
    ), {s: provenance[s] for s in payload_sites}


def test_the_adjacency_window_is_not_one_statement() -> None:
    """A statement between the two allocations does not separate them.

    What makes a pair a pair is that no OTHER allocation lands between its
    halves, not that the two lines touch — a window of exactly one statement
    hid a pair behind a `msg = head` (PR #1478 review, F11).  Driven from
    strings, over the shapes that must be found and the ones that must not.
    """
    import ast as _ast

    def names(*body: str) -> list[str]:
        src = ("def f(self):\n    if pair:\n"
               + "".join(f"        {line}\n" for line in body)
               + "    return 1\n")
        fn = next(n for n in _ast.walk(_ast.parse(src))
                  if isinstance(n, _ast.FunctionDef))
        return sorted(guard_emitter_scan._adjacent_pair_names(fn))

    touching = names('ptr = self.alloc_local("i32")',
                     'ln = self.alloc_local("i32")')
    assert touching == ["ln", "ptr"], touching
    spaced = names('ptr = self.alloc_local("i32")', "msg = head",
                   "other = 1", 'ln = self.alloc_local("i32")')
    assert spaced == ["ln", "ptr"], spaced
    assert not names('b = bind_slot_value_from_stack(self.alloc_local, "p")')
    assert not names('ptr = self.alloc_local("i32")', "msg = head")
    # An allocation of another width between them means the two i32s are not
    # consecutive locals at all, so they cannot be a working pair.
    assert not names('ptr = self.alloc_local("i32")',
                     'x = self.alloc_local("i64")',
                     'ln = self.alloc_local("i32")')


def test_the_provenance_scan_would_see_a_hand_bound_pair() -> None:
    """And it can FAIL, on the shape that got past two reviews.

    Driven through `slot_binding_provenance_for_tree`, the seam that runs
    the WHOLE classification on one parsed module: a cell that reached only
    `_adjacent_pair_names` would stay green if the emitter lookup or the
    reporting were deleted, which is coverage of a part rather than of the
    answer (CodeRabbit on PR #1478).  The fixtures are strings, so the cell
    says what the walk does rather than what today's source contains: an
    allocation in a branch handed to the emitter lines later — which is
    `_translate_handle_exn`'s shape (F10) — the same function written
    through the helper, and a call whose value argument the walk cannot
    read.
    """
    import ast as _ast
    import textwrap

    def classify(source: str) -> dict[str, str]:
        return guard_emitter_scan.slot_binding_provenance_for_tree(
            _ast.parse(textwrap.dedent(source)), "fixture.py")

    hand_bound = classify("""
        def translate(self, clause, env):
            if is_pair:
                thrown_local = self.alloc_local("i32")
                _len_local = self.alloc_local("i32")
            else:
                thrown_local = self.alloc_local(thrown_wt)
            more = "lines"
            return self._emit_clause_binder_guard(
                clause.params[0], thrown_local, base, te, where, clause, env)
    """)
    assert set(hand_bound.values()) == {
        guard_emitter_scan.FROM_ADJACENT_PAIR}, hand_bound

    through_helper = classify("""
        def translate(self, clause, env):
            thrown = bind_slot_value_from_stack(self.alloc_local, thrown_wt)
            more = "lines"
            return self._emit_clause_binder_guard(
                clause.params[0], thrown.slot_local, base, te, where,
                clause, env)
    """)
    assert set(through_helper.values()) == {
        guard_emitter_scan.FROM_HELPER}, through_helper

    unreadable = classify("""
        def translate(self, clause, env):
            thrown = bind_slot_value_from_stack(self.alloc_local, thrown_wt)
            return self._emit_bind_refine_guard(te, elsewhere=thrown)
    """)
    assert set(unreadable.values()) == {
        guard_emitter_scan.FROM_UNKNOWN}, unreadable

    # The same verdict by the OTHER road.  The shape above never reaches
    # `_classify` at all — the walk cannot find the argument, so the
    # fallback that turns an unrecognised expression into the scan's second
    # declared finding was pinned by nothing, and one line changing it to
    # `FROM_HELPER` left every cell green (PR #1478 review, F13).  Here the
    # argument IS found and is simply not a shape the classifier knows.
    unclassifiable = classify("""
        def translate(self, clause, env):
            return self._emit_bind_refine_guard(te, self._pick_ptr())
    """)
    assert set(unclassifiable.values()) == {
        guard_emitter_scan.FROM_UNKNOWN}, unclassifiable


#: The ways Python binds an `alloc_local` result to a name.  A scan that
#: reads only ONE of them is silent on a hand-bound pair written in any
#: other, which is the same blindness the call-site reading had — an
#: `ast.AnnAssign` keeps its binding in `target`, not `targets`, so an
#: annotated spill cleared the adjacency window instead of filling it
#: (CodeRabbit on PR #1478).
_PAIR_SPELLINGS: dict[str, str] = {
    "plain": """
        def translate(self, clause, env):
            thrown_local = self.alloc_local("i32")
            _len_local = self.alloc_local("i32")
            return self._emit_clause_binder_guard(
                clause.params[0], thrown_local, base, te, where, clause, env)
    """,
    "annotated": """
        def translate(self, clause, env):
            thrown_local: int = self.alloc_local("i32")
            _len_local: int = self.alloc_local("i32")
            return self._emit_clause_binder_guard(
                clause.params[0], thrown_local, base, te, where, clause, env)
    """,
    "one statement, tuple": """
        def translate(self, clause, env):
            thrown_local, _len_local = (
                self.alloc_local("i32"), self.alloc_local("i32"))
            return self._emit_clause_binder_guard(
                clause.params[0], thrown_local, base, te, where, clause, env)
    """,
    "walrus": """
        def translate(self, clause, env):
            self.emit_local(thrown_local := self.alloc_local("i32"))
            self.emit_local(_len_local := self.alloc_local("i32"))
            return self._emit_clause_binder_guard(
                clause.params[0], thrown_local, base, te, where, clause, env)
    """,
}


@pytest.mark.parametrize("spelling", sorted(_PAIR_SPELLINGS))
def test_the_adjacency_scan_reads_every_binding_form(spelling: str) -> None:
    """The same hand-bound pair, in each way Python can write it.

    The scan's job is that a pair bound on adjacency is a FINDING rather
    than a silence, so a spelling it cannot read is not a gap in coverage
    but a hole in the answer: the guard would be handed half a `(ptr, len)`
    value and nothing would say so.  Measured before the fix: `annotated`,
    `one statement, tuple` and `walrus` all classified as a single local.
    """
    import ast as _ast
    import textwrap

    found = guard_emitter_scan.slot_binding_provenance_for_tree(
        _ast.parse(textwrap.dedent(_PAIR_SPELLINGS[spelling])), "fixture.py")
    assert set(found.values()) == {guard_emitter_scan.FROM_ADJACENT_PAIR}, (
        f"a pair spelled `{spelling}` reads as {sorted(set(found.values()))}, "
        f"so a hand spill written that way is a silence"
    )


def test_the_scan_sees_an_emitter_wired_through_a_partial() -> None:
    """A roster is only as good as the wiring the scan can see.

    An emitter handed to `functools.partial` is wired as hard as one called
    by name, and a scan keyed on an opening paren saw neither — the #1268
    boundary emitter is installed exactly that way at `functions.py:544` and
    `closures.py:424`, so the blind spot was live rather than hypothetical
    (PR #1478 review, F5).  Read from the tree: those two sites must be what
    the scan reports for that emitter.
    """
    wired = guard_emitter_scan.emitter_call_sites(
        "_emit_boundary_refinement_guard")
    assert wired == {"_compile_fn/?", "_compile_lifted_closure/?"}, (
        f"the scan no longer sees the partial-wired boundary emitter: "
        f"{sorted(wired)}"
    )


def test_the_partial_form_is_what_the_scan_would_have_missed(
    tmp_path: Path,
) -> None:
    """And the fix is load-bearing: the old pattern misses that form.

    Driven against a scratch module rather than the tree, so the cell says
    what the PATTERN does rather than what today's source happens to
    contain.
    """
    import re as _re
    module = (
        "class C:\n"
        "    def wire(self):\n"
        "        return functools.partial(self._emit_x, ctx)\n"
    )
    paren_only = _re.compile(r"self\._emit_x\(")
    word_boundary = _re.compile(r"self\._emit_x\b")
    assert not paren_only.search(module), (
        "the paren-only pattern matches a partial after all — this cell is "
        "asserting nothing"
    )
    assert word_boundary.search(module), (
        "the word-boundary pattern misses a partial, so the scan's fix does "
        "not do what its docstring says"
    )


def test_dropping_any_boundary_roster_entry_is_visible() -> None:
    """EVERY entry, not one example.

    A comparison of SETS is satisfied by a roster that still names each call
    site through some other entry, so the comparison is driven once per entry
    and each is load-bearing on its own.
    """
    wired = _component_emitter_sites()
    for position, site in sorted(_COMPONENT_GUARD_SITES.items()):
        without = {
            s for p, s in _COMPONENT_GUARD_SITES.items() if p != position
        }
        assert without != wired, (
            f"dropping `{position}` ({site}) leaves the comparison "
            f"unchanged, so nothing holds that entry to an emitter"
        )


# =====================================================================
# The cells
# =====================================================================

#: (position, route index, representation) -> a shape the backend refuses
#: outright, in the compiler's own words.  Not a cell: a product refused
#: before the guard layer exercises that refusal rather than the binding, and
#: TESTING.md § Class Instruments is explicit that such a cell is worse than
#: an absent one because it reads as coverage.
_UNSUPPORTED_SHAPES: dict[tuple[str, int, str], str] = {
    ("State write boundary", 0, "string"):
        "Function 'f' uses State with unsupported type — skipped",
    ("State write boundary", 0, "array"):
        "Function 'f' uses State with unsupported type — skipped",
    **{
        ("State write boundary", route, repr_name):
            "Function 'f' uses State with unsupported type — skipped"
        for route in (1, 2, 3)
        for repr_name in ("string", "array")
    },
    ("map value", 0, "array"):
        "Map/Set with an Array-typed or zero-size key, value, or element is "
        "not supported — function skipped",
}

#: (position, route index, representation) -> a product whose SATISFYING twin
#: `vera verify` REFUSES, with the reason, because the producer its route
#: routes the value through does not establish the refinement.
#:
#: Not a cell, and not a defect either: a callee declared `-> @Int` with
#: `ensures(true)` PERMITS a violating result, so narrowing its result into a
#: `{ @Int | @Int.0 > 0 }` cell is refuted (E505) — the modular rule Vera
#: applies everywhere.  It bites exactly the bases whose predicate the solver
#: can STATE, which is why the opaque route's live cells are the handle ones,
#: and those are the cells #1439 was about.  Held to the live compiler by
#: `test_every_modular_refusal_is_still_refused`, so an entry cannot outlive
#: the refusal it names.
_MODULAR_REFUSALS: dict[tuple[str, int, str], str] = {
    ("State write boundary", route, repr_name):
        "the producer's `ensures(true)` establishes nothing, and this base's "
        "predicate IS statable, so the write is refuted at verification "
        "rather than reaching the guard"
    # Measured: `byte` is NOT among them.  Its predicate carries the base's
    # implicit `0 <= @Byte.0 <= 255` range, and the producer's unconstrained
    # result leaves the solver unable to refute `< 10` outright — so that
    # product stays a live cell and its guard is what answers.
    for route in (1, 2, 3)
    for repr_name in ("int", "nat", "float64", "bool")
}

#: (position, route index, representation) -> a defect this matrix finds that
#: this PR does not fix, with the measurement and the issue it belongs to.
#: Skipped here and pinned by a cell of its own at the end of the file, which
#: asserts what the compiler does TODAY: the day the defect is fixed that cell
#: fails, and both entries are meant to be deleted together.  A class
#: instrument trimmed until it is green measures the trimming.
_KNOWN_RED: dict[tuple[str, int, str], str] = {}

_CELLS = [
    (position, index, repr_name)
    for position, routes in sorted(_ALL_ROUTES.items())
    for index in range(len(routes))
    for repr_name in _REPRS
]


def _ids(cell: tuple[str, int, str]) -> str:
    position, index, repr_name = cell
    route = _ALL_ROUTES[position][index]
    label = f"{position}[{route.name}]" if route.name else position
    return f"{label.replace(' ', '-')}-{repr_name}"


# =====================================================================
# The measurement
# =====================================================================

_CACHE: dict[tuple[str, int, str], dict] = {}


def _write(tmp_path: Path, source: str, name: str) -> Path:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return p


def _envelope(proc: subprocess.CompletedProcess[str]) -> dict:
    try:
        parsed = json.loads(proc.stdout)
    except json.JSONDecodeError:  # pragma: no cover — a crash, not a verdict
        pytest.fail(
            f"`vera verify --json` produced no envelope:\n"
            f"{proc.stdout[-800:]}\n{proc.stderr[-800:]}"
        )
    if not isinstance(parsed, dict):  # pragma: no cover — defensive
        pytest.fail(f"`vera verify --json` produced {type(parsed)}")
    return parsed


def _statuses(envelope: dict) -> set[str]:
    return {
        o["status"] for o in envelope.get("obligations", ())
        if o["kind"] in _NARROWING_KINDS
    }


def _errors(envelope: dict) -> list[str]:
    return [
        d.get("error_code") for d in envelope.get("diagnostics", ())
        if d.get("severity") == "error"
    ]


def _sources(cell: tuple[str, int, str]) -> tuple[str, str]:
    position, index, repr_name = cell
    r = _REPRS[repr_name]
    build = _ALL_ROUTES[position][index].build
    return (
        build(r.instance("good")),  # type: ignore[operator]
        build(r.instance("bad")),   # type: ignore[operator]
    )


def _measure(cell: tuple[str, int, str], tmp_path: Path) -> dict:
    """Verify and run both twins of one cell, once per session.

    Cached because three readings ask about one measurement, and the
    measurement is CLI invocations — of which the last is skipped whenever
    the artifact already refused the violating value.
    """
    cached = _CACHE.get(cell)
    if cached is not None:
        return cached
    good_src, bad_src = _sources(cell)

    good_path = _write(tmp_path, good_src, "good.vera")
    good_env = _envelope(_cli("verify", "--json", str(good_path)))
    good_run = _cli("run", str(good_path))

    bad_path = _write(tmp_path, bad_src, "bad.vera")
    bad_run = _cli("run", str(bad_path))
    bad_errors: list[str] = []
    if bad_run.returncode == 0:
        # Only then does the STATIC answer matter: a value the artifact has
        # already refused needs no second question, and asking it anyway
        # would half again the matrix's wall time.
        bad_errors = _errors(_envelope(_cli("verify", "--json", str(bad_path))))

    out = dict(
        good_source=good_src,
        statuses=_statuses(good_env),
        errors=_errors(good_env),
        good_runs=good_run.returncode == 0,
        good_output=(good_run.stdout + good_run.stderr)[-600:],
        bad_refused_at_run=bad_run.returncode != 0,
        bad_output=(bad_run.stdout + bad_run.stderr)[-600:],
        bad_errors=bad_errors,
    )
    _CACHE[cell] = out
    return out


def _disposition(cell: tuple[str, int, str]) -> None:
    """Apply this product's disposition, if it has one."""
    unsupported = _UNSUPPORTED_SHAPES.get(cell)
    if unsupported is not None:
        pytest.skip(f"the backend refuses the shape: {unsupported}")
    modular = _MODULAR_REFUSALS.get(cell)
    if modular is not None:
        pytest.skip(f"verification refuses the satisfying twin: {modular}")
    known_red = _KNOWN_RED.get(cell)
    if known_red is not None:
        pytest.skip(
            f"pinned by its own cell at the end of this file: {known_red}")


# =====================================================================
# Reading 1: the satisfying value runs — #1466's own property
# =====================================================================


@pytest.mark.parametrize("cell", _CELLS, ids=_ids)
def test_a_guard_never_refuses_a_value_it_admits(
    cell: tuple[str, int, str], tmp_path: Path,
) -> None:
    """THE reading #1466 is about, and the one no sibling instrument has.

    A guard exists to refuse what the refinement forbids.  One that refuses
    what it ADMITS is worse than absent: the program is correct, `vera
    verify` says so, and the artifact will not run it.
    """
    _disposition(cell)
    m = _measure(cell, tmp_path)
    assert not m["errors"], (
        f"{_ids(cell)}: the SATISFYING program is refused statically "
        f"({m['errors']}), so this cell measures that refusal rather than "
        f"the guard's binding:\n{m['good_source']}"
    )
    assert m["good_runs"], (
        f"{_ids(cell)}: the guard refuses a value its own refinement "
        f"ADMITS:\n{m['good_output']}"
    )


# =====================================================================
# Reading 2: the violating value is refused, under this position's name
# =====================================================================


@pytest.mark.parametrize("cell", _CELLS, ids=_ids)
def test_a_violating_value_is_refused(
    cell: tuple[str, int, str], tmp_path: Path,
) -> None:
    """The complement, without which reading 1 is satisfied by NO guard.

    Refused statically where the value is refutable (a literal at a scalar
    base is), and by the artifact otherwise — and when the artifact is what
    refuses it, the trap is ATTRIBUTED: it names this refinement's predicate
    and the role of the position that refused, so a guard cannot pass by
    trapping over some other value or under another position's name.
    """
    _disposition(cell)
    expected = _expected_record(cell)
    if expected != _GUARDED:
        pytest.skip(f"the record discloses this position for this base: "
                    f"{expected}")
    m = _measure(cell, tmp_path)
    assert m["bad_refused_at_run"] or m["bad_errors"], (
        f"{_ids(cell)}: the violating value is refused by nothing — not by "
        f"verification, and not by the artifact:\n{m['bad_output']}"
    )
    if m["bad_refused_at_run"] and "Refinement violation" in m["bad_output"]:
        witness = _REPRS[cell[2]].witness
        assert witness in m["bad_output"], (
            f"{_ids(cell)}: the trap does not name this refinement's "
            f"predicate ({witness!r}), so it refuses something else:\n"
            f"{m['bad_output']}"
        )
        roles = _expected_roles(cell)
        assert any(role in m["bad_output"] for role in roles), (
            f"{_ids(cell)}: the trap names none of the roles that may refuse "
            f"it ({roles}):\n{m['bad_output']}"
        )


# =====================================================================
# Reading 3: the record says what the artifact does
# =====================================================================
#
# The expectation is a RULE over the cell, deliberately not a lookup in the
# registry: the point of this reading is that dropping a registry entry must
# RED a cell, and a reading that consulted the registry to decide what to
# expect would move with it (R-1465 review, Finding 3).

_GUARDED = "guarded-or-proved"

_CONSTRUCTION_POSITIONS = frozenset(
    site for sites in binders.CONSTRUCTION_SITES.values() for site in sites
)


def _expected_record(cell: tuple[str, int, str]) -> str:
    """What the obligation stream must say about this cell's position."""
    position, index, repr_name = cell
    base = _REPRS[repr_name].base
    stores = (position in _CONSTRUCTION_POSITIONS
              or _ALL_ROUTES[position][index].constructs)
    if stores and base not in narrowing.REFINED_CONSTRUCTION_SCALAR_BASES:
        return (
            "disclosed: a construction store tees the value into one scalar "
            "local, and this base has no scalar representation "
            "(`narrowing.REFINED_CONSTRUCTION_SCALAR_BASES`)"
        )
    return _GUARDED


def _expected_roles(cell: tuple[str, int, str]) -> tuple[str, ...]:
    """The role the trap must print when the ARTIFACT refuses this cell.

    Derived rather than fixed per route, because a value crossing a
    CONSTRUCTION position is refused by the store before it ever reaches the
    position's own boundary guard — and the store prints its own `<type>
    binding` role, under a `where` naming the store ("Tuple(…) construction").
    So a tuple component over a base the store guards traps as a binding, and
    the same component over a base the store DISCLOSES traps at the boundary
    as "tuple component", which is the reading the pair rows rest on.
    """
    position, index, repr_name = cell
    route = _ALL_ROUTES[position][index]
    base = _REPRS[repr_name].base
    stores = position in _CONSTRUCTION_POSITIONS or route.constructs
    if stores and base in narrowing.REFINED_CONSTRUCTION_SCALAR_BASES:
        if route.store_reaches:
            return ("binding",)
        # The store is there and its guard does not reach this component, so
        # either it or the boundary may be what refuses — which of the two is
        # a fact about the checker's target threading, not about the binding
        # this matrix measures.
        return ("binding", route.role)
    return (route.role,)


@pytest.mark.parametrize("cell", _CELLS, ids=_ids)
def test_the_record_matches_the_rule(
    cell: tuple[str, int, str], tmp_path: Path,
) -> None:
    """A position that can be guarded claims a check; one that cannot
    discloses it.

    Both directions matter.  A position quietly losing its guard keeps
    reading 1 green — nothing refuses anything — and flips its status to
    `tier3_unguarded`, so this is the reading that sees it; and a base the
    store cannot lower must DISCLOSE rather than claim, which is the
    over-claim this release exists to remove.

    The assertion is membership rather than set equality, because one
    program legitimately carries several narrowings at several positions: a
    `Map` value bound by a `let` discloses the element position while the
    store itself is proved, so a cell's own status is one of the set rather
    than the whole of it.  "No position is left unbacked" over the whole
    product is the sibling generator's reading, not this one's.
    """
    _disposition(cell)
    m = _measure(cell, tmp_path)
    expected = _expected_record(cell)
    statuses = m["statuses"]
    assert statuses, (
        f"{_ids(cell)}: a refinement narrowing at this position is recorded "
        f"NOWHERE — not verified, not tier3, not tier3_unguarded"
    )
    if expected == _GUARDED:
        assert statuses & {"tier3", "verified"}, (
            f"{_ids(cell)}: a guard can be emitted for this base at this "
            f"position, and the stream says {sorted(statuses)}"
        )
    else:
        assert "tier3_unguarded" in statuses, (
            f"{_ids(cell)}: {expected}, and the stream says "
            f"{sorted(statuses)}"
        )


def test_every_modular_refusal_is_still_refused(tmp_path: Path) -> None:
    """A product excluded as refuted is still refuted, and by E505.

    The complement of the unsupported-shape check: an entry that outlives
    its refusal is an absent cell wearing a reason.  The SATISFYING twin is
    what must be refused here — that is what makes the product unmeasurable
    — and the code must be the narrowing refutation rather than any other
    refusal that happens to be fatal.
    """
    for cell in sorted(_MODULAR_REFUSALS):
        good_src, _bad = _sources(cell)
        envelope = _envelope(_cli(
            "verify", "--json", str(_write(tmp_path, good_src, "m.vera"))))
        assert "E505" in _errors(envelope), (
            f"{_ids(cell)} is excluded as refuted at verification, and "
            f"verification now says {_errors(envelope)}"
        )


def test_every_unsupported_shape_says_so_in_the_compilers_words(
    tmp_path: Path,
) -> None:
    """An excluded product is excluded for a reason the COMPILER still gives.

    Without this, an entry outlives the refusal it names and the cell stays
    skipped after the shape becomes supported — an absent cell wearing a
    reason, which is the failure mode the exclusion list exists to avoid.
    """
    for cell, message in sorted(_UNSUPPORTED_SHAPES.items()):
        good_src, _bad = _sources(cell)
        ran = _cli("run", str(_write(tmp_path, good_src, "u.vera")))
        assert message in (ran.stdout + ran.stderr), (
            f"{_ids(cell)} is excluded as unsupported, but the compiler no "
            f"longer says so:\n{(ran.stdout + ran.stderr)[-500:]}"
        )


# =====================================================================
# The two defects this matrix finds that this PR does not fix
# =====================================================================
#
# Pinned as what the compiler DOES, not as what it should: each assertion
# fails the day the defect is fixed, which is when the cell here is meant to
# be deleted, with its `_KNOWN_RED` entry where the matrix carries one.

#: Every representation, at every one of the write's four routes: the
#: differential below is what would have caught #1439, so it ranges over the
#: whole position rather than one spelling of it.  The PR #1478 reviewer
#: measured the unrouted forms' handle rows `tier3`-with-no-guard while the
#: routed one was green, which is exactly what a single-route reading misses.
_STATE_WRITE_REPRS = list(_REPRS)


@pytest.mark.parametrize("repr_name", _STATE_WRITE_REPRS)
@pytest.mark.parametrize("route", range(len(_TEMPLATES["State write boundary"])))
def test_a_state_write_claims_exactly_the_guard_it_emits(
    route: int, repr_name: str, tmp_path: Path,
) -> None:
    """The record and the ARTIFACT, differentially, at the write boundary.

    Two components answer one question here — the verifier records the write
    `tier3` or `tier3_unguarded`, and code generation either emits the check
    or does not — and a status is a claim about the other component, so a
    disagreement is invisible from inside either.  It was: the write guard
    asked which bases a CONSTRUCTION store can tee into a scalar local, so a
    `Map`, `Set`, `Tuple` or ADT cell was declined while the record said
    `tier3`, and the module carried no `$vera.contract_fail` call at all
    (#1439).

    A unit test on either side would have stayed green through that, which
    is why this reads BOTH and compares them, once per representation the
    cell can be declared at.  `verified` is not a claim about codegen — the
    obligation was discharged statically — so it says nothing either way,
    and the guard is emitted ungated regardless.
    """
    cell = ("State write boundary", route, repr_name)
    if cell in _UNSUPPORTED_SHAPES:
        pytest.skip("a pair cell is refused at registration; "
                    "`test_a_pair_state_cell_is_refused_and_says_so` pins it")
    # The SATISFYING twin, always: this reading is about what the record
    # claims for a program the compiler accepts, and the violating twin of
    # the literal route is refused by the CHECKER for the handle bases
    # (E331), which leaves no obligation to compare anything against.
    source = _sources(cell)[0]
    envelope = _envelope(_cli(
        "verify", "--json", str(_write(tmp_path, source, "s.vera"))))
    statuses = _statuses(envelope)
    wat = _cli("compile", "--wat", str(_write(tmp_path, source, "s.vera")))
    emitted = "contract_fail" in wat.stdout
    assert statuses, "the write raises no narrowing obligation at all"
    if "tier3" in statuses:
        assert emitted, (
            f"State write x {repr_name}: the record claims a runtime check "
            f"({sorted(statuses)}) and the module carries none"
        )
    elif "tier3_unguarded" in statuses:
        assert not emitted, (
            f"State write x {repr_name}: the record discloses the write as "
            f"unguarded ({sorted(statuses)}) and the module guards it, so a "
            f"reader is told to add a bound the artifact already enforces"
        )


#: Refined bases built OUT of the axis rather than beside it (PR #1478
#: review): a pair inside a handle, a handle inside a handle, and a user ADT
#: with a pair field.  Crossed with the tuple routes only, where an offset
#: is what a guard has to get right — the eleven-row axis already measures
#: every representation at every position, and these ask a narrower
#: question: does the binding hold when the refined value is COMPOSITE.
_COMPOSITE_BASES: dict[str, tuple[str, str, str]] = {
    # (declarations, satisfying value, violating value)
    "option-of-string": (
        "type R = { @Option<String> | @Option<String>.0 == Some(\"x\") };\n",
        'Some("x")', "None",
    ),
    "nested-tuple": (
        "type R = { @Tuple<Tuple<Int, Int>, Int> | "
        "fst2(@Tuple<Tuple<Int, Int>, Int>.0) > 0 };\n\n"
        "private fn fst2(@Tuple<Tuple<Int, Int>, Int> -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  let Tuple<@Tuple<Int, Int>, @Int> = "
        "@Tuple<Tuple<Int, Int>, Int>.0;\n"
        "  let Tuple<@Int, @Int> = @Tuple<Int, Int>.0;\n  @Int.1\n}\n",
        "Tuple(Tuple(1, 1), 1)", "Tuple(Tuple(0 - 1, 1), 1)",
    ),
    "adt-with-a-pair-field": (
        "private data Pairish {\n  MkPairish(String, Int)\n}\n\n"
        "type R = { @Pairish | width(@Pairish.0) > 0 };\n\n"
        "private fn width(@Pairish -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  match @Pairish.0 {\n"
        "    MkPairish(@String, @Int) -> string_length(@String.0) + @Int.0\n"
        "  }\n}\n",
        'MkPairish("x", 1)', 'MkPairish("", 0)',
    ),
}

#: The tuple routes, where a composite base's offset is what is at stake.
_COMPOSITE_ROUTES = ("parameter", "after-pair", "after-two-pairs",
                     "depth-three")


@pytest.mark.parametrize("base_name", sorted(_COMPOSITE_BASES))
@pytest.mark.parametrize("route_name", _COMPOSITE_ROUTES)
def test_a_composite_refined_base_binds_at_a_tuple_boundary(
    route_name: str, base_name: str, tmp_path: Path,
) -> None:
    """A refined value that is itself composite still binds whole.

    Every row of the axis is a base the language spells in one word; these
    are bases built out of others — `Option<String>`, a tuple of tuples, an
    ADT whose own first field is a pair — and each is a handle at the
    boundary, so the binding is one local and the OFFSET is what a
    decomposition can get wrong.  The satisfying value must run and the
    violating one must be refused, at the routes where something sits in
    front of the guarded component.
    """
    decls, good, bad = _COMPOSITE_BASES[base_name]
    route = next(r for r in _ALL_ROUTES["tuple component"]
                 if r.name == route_name)
    build = route.build
    good_src = build(_Instance(decls, good, "Int", "1"))   # type: ignore[operator]
    bad_src = build(_Instance(decls, bad, "Int", "1"))     # type: ignore[operator]

    envelope = _envelope(_cli(
        "verify", "--json", str(_write(tmp_path, good_src, "c.vera"))))
    assert not _errors(envelope), (
        f"{route_name}/{base_name}: the satisfying program is refused "
        f"statically ({_errors(envelope)}):\n{good_src}"
    )
    ran = _cli("run", str(_write(tmp_path, good_src, "c.vera")))
    assert ran.returncode == 0, (
        f"{route_name}/{base_name}: the guard refuses a value its own "
        f"refinement admits:\n{(ran.stdout + ran.stderr)[-500:]}"
    )
    bad_path = _write(tmp_path, bad_src, "cbad.vera")
    bad_run = _cli("run", str(bad_path))
    refused = bad_run.returncode != 0 or _errors(
        _envelope(_cli("verify", "--json", str(bad_path))))
    assert refused, (
        f"{route_name}/{base_name}: the violating value is refused by "
        f"nothing:\n{(bad_run.stdout + bad_run.stderr)[-500:]}"
    )


@pytest.mark.parametrize("repr_name", ("string", "array"))
@pytest.mark.parametrize("route", (0, 1, 2, 3))
def test_a_pair_state_cell_is_refused_and_says_so(
    route: int, repr_name: str, tmp_path: Path,
) -> None:
    """The rows the matrix cannot measure still pin something.

    A `State` cell's value crosses four host imports carrying ONE word
    (`state_get_X (result W)`, `state_put_X (param W)`), so a `(ptr, len)`
    pair has no way through whatever the write guard could bind.  Code
    generation refuses the cell at registration and drops the function; the
    matrix's three readings cannot run, because there is no artifact to run.

    What must still hold is that the refusal is SAID and the record is
    honest: `vera verify` does not refuse the program, the obligation
    discloses `tier3_unguarded` rather than claiming a check inside a
    function the module does not contain (#1439, #1268's lesson at this
    boundary), and the compiler names the refusal in its own words.  Before
    this PR the record said `tier3` for exactly these rows.
    """
    cell = ("State write boundary", route, repr_name)
    good_src, _bad = _sources(cell)
    path = _write(tmp_path, good_src, "pair-cell.vera")
    envelope = _envelope(_cli("verify", "--json", str(path)))
    assert not _errors(envelope), (
        f"the program is refused at verification: {_errors(envelope)}"
    )
    statuses = _statuses(envelope)
    assert "tier3_unguarded" in statuses, (
        f"a pair `State` cell is registered by nobody, and the record says "
        f"{sorted(statuses)}"
    )
    assert "tier3" not in statuses, (
        f"the record claims a runtime check for a write inside a function "
        f"code generation drops: {sorted(statuses)}"
    )
    ran = _cli("run", str(path))
    assert "uses State with unsupported type" in (ran.stdout + ran.stderr), (
        f"the compiler no longer names the refusal:\n"
        f"{(ran.stdout + ran.stderr)[-400:]}"
    )


#: A value of `Never` for the cells whose type has no other value to write:
#: a declared function that throws.  An UNDECLARED call stood here until
#: #1513 made an unresolved call an error, so a program holding one no
#: longer reaches the verifier at all.
_NEVER_FN = (
    "private fn never_value(@Unit -> @Never)\n"
    "  requires(true)\n  ensures(true)\n  effects(<Exn<Int>>)\n"
    "{\n  Exn.throw(0)\n}\n\n"
)
_NEVER = "never_value(())"
_THROWS = "<Exn<Int>>"

#: Cell types whose REPRESENTATION decides whether code generation
#: registers a `State<T>` cell, each with the value written into it, the
#: declarations it needs, the enclosing function's effect row, and whether
#: the record must DISCLOSE the write.  A row the backend REGISTERS carries
#: a real literal and the cell asserts the artifact exists: an undeclared
#: initialiser made code generation drop the whole function before
#: `_register_state_cell` was reached, and the registered rows then compared
#: a `tier3` claim against a module containing no `$f` at all — the #1268
#: shape inside the cell that exists to detect it (PR #1478 review, F12).
#: A row the backend REFUSES must never be recorded `tier3`, a claim of a
#: runtime check the refused registration never emits.  Its write is
#: disclosed (`tier3_unguarded`) where the verifier cannot state the
#: predicate over the cell's type; a `String` literal against `true` it
#: proves outright, so that row's record is Tier 1 and discloses nothing.
#:
#: `Future<Future<Never>>` and an ALIAS to `Never` are listed because the
#: shared rule answers for them too and nothing said so: both recorded
#: `tier3` at `8557dc24` beside `Never` itself (PR #1478 review).
_CELL_REPRESENTATIONS: dict[str, tuple[bool, str, str, str, bool]] = {
    # cell type: (registered, initial value, extra declarations,
    #             effect row, disclosed)
    "Int": (True, "5", "", "pure", False),
    "Float64": (True, "1.0", "", "pure", False),
    "Option<Int>": (True, "Some(1)", "", "pure", False),
    "String": (False, '"s"', "", "pure", False),      # a pair: no way
    "Array<Int>": (False, "[1]", "", "pure", True),   #   through a one-word
    "Unit": (False, "()", "", "pure", True),          # zero-size
    "Never": (False, _NEVER, _NEVER_FN, _THROWS, True),  # no representation
    "Future<Never>": (False, _NEVER, _NEVER_FN, _THROWS, True),  # the same
    "Future<Future<Never>>": (False, _NEVER, _NEVER_FN, _THROWS, True),
    "NeverAlias": (False, _NEVER, "type NeverAlias = Never;\n\n" + _NEVER_FN,
                   _THROWS, True),
}


@pytest.mark.parametrize("cell_type", sorted(_CELL_REPRESENTATIONS))
def test_the_record_and_registration_agree_about_a_state_cell(
    cell_type: str, tmp_path: Path,
) -> None:
    """One rule, two oracles, and a differential rather than a promise.

    `vera.types.state_cell_lowerable` is asked by `_register_state_cell`
    from the cell's TYPE EXPRESSION and by the verifier from the checker's
    semantic type.  Two oracles is exactly the shape that drifts invisibly —
    the verifier's answer is a claim about the backend's — so this drives
    both over the representations that decide the question and asserts they
    agree: a cell the backend registers may be recorded `tier3`, and one it
    refuses must be disclosed.

    Measured before the fix: a refined `State<Never>` and
    `State<Future<Never>>` recorded `tier3` while registration dropped the
    function with E607, because the verifier asked only about erasure.
    """
    expected, init, prelude, effects, disclosed = (
        _CELL_REPRESENTATIONS[cell_type])
    source = (
        f"{prelude}type R = {{ @{cell_type} | true }};\n\n"
        "public fn f(@Unit -> @Int)\n"
        f"  requires(true)\n  ensures(true)\n  effects({effects})\n"
        "{\n"
        f"  handle[State<R>](@R = {init}) {{\n"
        "    put(@R) -> { resume(()) }\n"
        "  } in {\n    1\n  }\n}\n"
    )
    path = _write(tmp_path, source, "cell.vera")
    envelope = _envelope(_cli("verify", "--json", str(path)))
    assert not _errors(envelope), _errors(envelope)
    statuses = _statuses(envelope)
    ran = _cli("run", str(path))
    registered = "uses State with unsupported type" not in (
        ran.stdout + ran.stderr)
    wat = _cli("compile", "--wat", str(path)).stdout

    assert registered == expected, (
        f"`State<{cell_type}>` registration changed: the backend "
        f"{'registers' if registered else 'refuses'} it"
    )
    if registered:
        # What the row is FOR: a record read against an artifact that
        # exists.  Without this the whole positive arm passes for a module
        # the compiler dropped.
        assert "$f" in wat, (
            f"`State<{cell_type}>` is registered and the module carries no "
            f"`$f`, so the record is being compared against nothing"
        )
        assert "tier3_unguarded" not in statuses, (
            f"`State<{cell_type}>` is registered and the record discloses "
            f"the write as unguarded: {sorted(statuses)}"
        )
        if "tier3" in statuses:
            assert "contract_fail" in wat, (
                f"`State<{cell_type}>`: the record claims a runtime check "
                f"and the module carries none"
            )
        else:
            # `@Int` and `@Float64` discharge statically against `true`;
            # a claim of neither kind would mean the write raised no
            # obligation at all.
            assert "verified" in statuses, sorted(statuses)
    else:
        assert "$f" not in wat, (
            f"`State<{cell_type}>` is refused at registration and the "
            f"module carries `$f` anyway"
        )
        assert "tier3" not in statuses, (
            f"`State<{cell_type}>` is refused at registration and the record "
            f"claims a runtime check: {sorted(statuses)}"
        )
        if disclosed:
            assert "tier3_unguarded" in statuses, (
                f"`State<{cell_type}>` is refused at registration and the "
                f"record says {sorted(statuses)}"
            )
        else:
            assert statuses == {"verified"}, sorted(statuses)


#: What the module docstring says the `@Byte` literal tally is, as
#: `{error code: routes}` with the totals beside it.  A hand-written tally
#: is a measurement that stops being one: this read "seven of eighteen" and
#: then "five of the six tuple routes" while the file grew to twenty-seven
#: routes (CodeRabbit on PR #1478).
_BYTE_LITERAL_TALLY = {"E202": 7, "E121": 1, "E213": 3, "E170": 1, "E314": 1}
_BYTE_LITERAL_TOTALS = (13, 27)


def test_the_byte_literal_tally_is_what_the_routes_measure(
    tmp_path: Path,
) -> None:
    """The docstring's `@Byte` count, recomputed from the routes.

    The row uses a helper because a literal is refused at some positions;
    saying WHICH is a measurement, and a measurement written into prose
    drifts the moment the axis grows.  So it is taken again here, per route,
    from the compiler.
    """
    import re as _re

    literal = _Repr(
        decls=_REPRS["byte"].decls, base="Byte", good="3", bad="200",
        repr_class="scalar", safe="3", witness="@Byte.0 < 10",
    )
    refused: dict[str, int] = {}
    routes = 0
    for _position, entries in sorted(_ALL_ROUTES.items()):
        for route in entries:
            routes += 1
            source = route.build(literal.instance("good"))  # type: ignore[operator]
            checked = _cli(
                "check", str(_write(tmp_path, source, "byte.vera")))
            if checked.returncode == 0:
                continue
            found = _re.search(
                r"\[(E\d+)\]", checked.stdout + checked.stderr)
            code = found.group(1) if found else "?"
            refused[code] = refused.get(code, 0) + 1
    assert (sum(refused.values()), routes) == _BYTE_LITERAL_TOTALS, (
        f"the docstring says {_BYTE_LITERAL_TOTALS[0]} of "
        f"{_BYTE_LITERAL_TOTALS[1]} routes refuse a `@Byte` literal; the "
        f"compiler refuses {sum(refused.values())} of {routes}"
    )
    assert refused == _BYTE_LITERAL_TALLY, (
        f"the docstring's per-code tally is {_BYTE_LITERAL_TALLY} and the "
        f"measurement is {refused}"
    )
    text = __doc__ or ""
    assert "THIRTEEN of the" in text and "Seven E202" in text, (
        "the docstring no longer states the tally this cell recomputes"
    )


def test_a_refined_function_type_has_the_closure_representation() -> None:
    """A refinement over a function type is a closure pointer, like the bare
    spelling.

    `wasm_representation` tested the WRAPPED type in its function-type
    branch where every branch above it tests the unwrapped base, so a
    `{ fn(…) | … }` answered "unsupported" and anything keyed on that read
    it as having no representation (CodeRabbit on PR #1478).
    """
    from vera import ast as vera_ast
    from vera.types import (
        BOOL,
        FunctionType,
        RefinedType,
        wasm_representation,
    )

    bare = FunctionType((BOOL,), BOOL, frozenset())
    refined = RefinedType(bare, vera_ast.BoolLit(value=True))
    assert wasm_representation(bare) == "i32"
    assert wasm_representation(refined) == "i32", (
        "a refinement over a function type answers "
        f"{wasm_representation(refined)!r}, so the branch is reading the "
        f"wrapper rather than the base"
    )


def test_1439_a_state_write_over_a_handle_base_carries_its_guard(
    tmp_path: Path,
) -> None:
    """#1439's remaining half: the write is checked, not merely claimed.

    The `State` write guard used to ask `_refined_component_wasm_type`,
    which answers None for every base outside the construction-scalar
    roster — a HANDLE base included, though its value is the one i32 the
    store already tees into — while the verifier's `State write boundary`
    arm recorded the write `tier3`.  The module carried no
    `$vera.contract_fail` call at all and a violating value was stored.

    The cells above read the statuses and the two verdicts; this one reads
    the ARTIFACT, because a record and a run can agree for a reason other
    than a guard, and what was missing was the guard.
    """
    cell = ("State write boundary", 1, "tuple")
    m = _measure(cell, tmp_path)
    assert not m["errors"], m["errors"]
    assert "tier3" in m["statuses"], sorted(m["statuses"])
    wat = _cli("compile", "--wat", str(_write(
        tmp_path, _sources(cell)[1], "state.vera")))
    assert "contract_fail" in wat.stdout, (
        "the record claims a runtime check and the module carries none"
    )
    assert m["bad_refused_at_run"], m["bad_output"]


def test_1424_a_tuple_sub_pattern_returned_from_its_arm_crashes_verify(
    tmp_path: Path,
) -> None:
    """#1424, pinned.  This asserts the DEFECT; see the issue for the class.

    An ADT sub-pattern binder of `Tuple` type, returned from its own arm and
    joined with an arm that builds a fresh `Tuple`, reaches the verifier's
    sort resolution by two routes that disagree.  `vera check` is clean.

    The payload is built from `@Nat` values.  The matrix's own cell for this
    position built it from literals, `Some(Tuple(1, 1))`, and crashed only
    because the literals were typed `Nat` against the declared
    `Tuple<Int, Int>`; since #1541 they take that declared type, so the cell
    verifies and runs in the matrix above, and a declared `@Nat` operand is
    what still reaches the two disagreeing routes.
    """
    source = """public fn f(@Nat -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Tuple<Int, Int>> = Some(Tuple(@Nat.0, @Nat.0));
  match @Option<Tuple<Int, Int>>.0 {
    Some(@Tuple<Int, Int>) -> @Tuple<Int, Int>.0,
    None -> Tuple(1, 1)
  }
}
"""
    path = _write(tmp_path, source, "sub.vera")
    assert _cli("check", "--quiet", str(path)).returncode == 0
    verified = _cli("verify", str(path))
    assert verified.returncode != 0, (
        "#1424 appears to be FIXED — verification no longer crashes.  Remove "
        "this cell"
    )
    output = verified.stdout + verified.stderr
    assert "E699" in output and "sort mismatch" in output, output[-400:]
