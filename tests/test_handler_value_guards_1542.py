"""A value at a handler position is held to its type where the obligation
table says it is (#1542's handle-value and `resume` lines).

Two mechanisms, each one site.

* The table (`vera/obligations/table.py`, `_Builder.handle_rows`).  The
  requirement a `handle`'s value is held to reaches the leaves of its body,
  and of an `Exn` clause that resumes nowhere, as it does a block's, an
  `if`'s and a `match`'s; every `refine_bind` and `nat_bind` row that
  hand-down listed was turned unguarded by a reason of its own, written
  when code generation emitted no store check inside a handle.  It emits
  one now (a construction is checked by its own row, #1834, and an
  `apply_fn` argument at its leaves, #1889), so the rows are checks: a
  `Some(float_to_int(x))` built as a handle's value at `Option<PosInt>`,
  or a `Tuple<Nat, Int>` produced there, ran with its component violated.
* Code generation (`vera/wasm/calls_handlers.py`, the `get` clause).  A
  `get` clause's tail `resume(x)` is the operation's result at the cell's
  type, and the table lists its row there.  The lowering ran the sign
  guard on `x` and not the predicate's, which the three other `State` write
  boundaries (the initial value, `put`'s argument, a `with` override) run,
  so `resume(x)` at `State<Pos>` returned -5.

The instrument is the census of handler positions, read off the lowering
top to bottom (`State`: the initial value, `put`'s argument, a `put` binder
narrower than the cell, `get`'s resume, a `with` override, and the handle's
value at a `let`, at an `apply_fn` argument and at a function's return;
`Exn`: the `throw` payload, a `throw` binder narrower than the payload, a
non-resuming clause's value and the body's value), by the value's shape (a
refinement at the head, `Nat` at the head, a refined tuple component and a
refined `Option` payload), by whether the solver decides the refinement
(`Small`) or not (`Short`).  The source is an opaque call, so the run
decides each cell.  A user effect's handler is refused at check (E340) and
has no position here; `put`'s resume is `Unit`, and an `Exn` clause does
not resume.

Each cell asserts its verdict, its rows' statuses and the run at a
violating and a satisfying argument.  A refinement below a composite's
head is checked only where a boundary decomposes the value, so by rule 2
(spec §2.6.5) a refined tuple component at a `State` write boundary, at a
`get` resume and at a handle's value bound by a `let` is disclosed (`E506`,
the verdict the value has at a `let` written directly), as a refined
`Option` payload and a binder's component are; no cell is a row listed as
checked that no check answers (`E541`).
"""

from __future__ import annotations

import pytest

from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs
# a sample of its cells, and all of them when it changes this file or a
# module that decides its class: the table's rows, the verifier's reading of
# them, and the handler lowering's guards.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/obligations/table.py",
        "vera/verifier.py",
        "vera/wasm/calls_handlers.py",
    ],
)

PRELUDE = (
    "type Short = { @Int | string_length(to_string(@Int.0)) < 3 };\n"
    "type Small = { @Int | @Int.0 < 10 };\n"
)

#: shape -> (the type T, its base B, `mk`'s body, `rd`'s body, a literal of
#: T, the argument the value violates T at, the value built in place, for a
#: composite).  `mk` and `sc` are opaque to the solver, and `rd` reads the
#: refined part back as an `Int`.
_TUPLE_RD = "let Tuple<@Int, @Int> = @Tuple<Int, Int>.0;\n  @Int.1"
_OPTION_RD = "option_unwrap_or(@Option<Int>.0, 0)"
_TUPLE_BUILT = "Tuple(sc(@Int.0), 0)"
_OPTION_BUILT = "Some(sc(@Int.0))"
SHAPES: dict[str, tuple[str, str, str, str, str, int, str | None]] = {
    "nat": ("Nat", "Int", "@Int.0", "@Int.0", "1", -5, None),
    "short": ("Short", "Int", "@Int.0", "@Int.0", "1", 5000, None),
    "small": ("Small", "Int", "@Int.0", "@Int.0", "1", 50, None),
    "tuple_nat": ("Tuple<Nat, Int>", "Tuple<Int, Int>", "Tuple(@Int.0, 0)",
                  _TUPLE_RD, "Tuple(1, 0)", -5, _TUPLE_BUILT),
    "tuple_short": ("Tuple<Short, Int>", "Tuple<Int, Int>", "Tuple(@Int.0, 0)",
                    _TUPLE_RD, "Tuple(1, 0)", 5000, _TUPLE_BUILT),
    "tuple_small": ("Tuple<Small, Int>", "Tuple<Int, Int>", "Tuple(@Int.0, 0)",
                    _TUPLE_RD, "Tuple(1, 0)", 50, _TUPLE_BUILT),
    "option_nat": ("Option<Nat>", "Option<Int>", "Some(@Int.0)", _OPTION_RD,
                   "Some(1)", -5, _OPTION_BUILT),
    "option_short": ("Option<Short>", "Option<Int>", "Some(@Int.0)",
                     _OPTION_RD, "Some(1)", 5000, _OPTION_BUILT),
    "option_small": ("Option<Small>", "Option<Int>", "Some(@Int.0)",
                     _OPTION_RD, "Some(1)", 50, _OPTION_BUILT),
}

#: The satisfying argument: every shape's `mk(3)` holds, and `go` returns 3.
SATISFYING = 3

_STATE_BOOL = ("handle[State<Bool>](@Bool = true) {{\n"
               "    get(@Unit) -> {{ resume(@Bool.0) }},\n"
               "    put(@Bool) -> {{ resume(()) }}\n  }}")

#: position -> `go`'s body, over T, B and G (a literal of T).
POSITIONS: dict[str, str] = {
    "state_init": (
        "handle[State<{T}>](@{T} = {V}) {{\n"
        "    get(@Unit) -> {{ resume(@{T}.0) }},\n"
        "    put(@{T}) -> {{ resume(()) }}\n"
        "  }} in {{\n    rd(get(()))\n  }}"),
    "put_argument": (
        "handle[State<{T}>](@{T} = {G}) {{\n"
        "    get(@Unit) -> {{ resume(@{T}.0) }},\n"
        "    put(@{T}) -> {{ resume(()) }}\n"
        "  }} in {{\n    put({V});\n    rd(get(()))\n  }}"),
    "put_binder": (
        "handle[State<{B}>](@{B} = mk(0)) {{\n"
        "    get(@Unit) -> {{ resume(@{B}.0) }},\n"
        "    put(@{T}) -> {{ resume(()) }}\n"
        "  }} in {{\n    put({V});\n    rd(get(()))\n  }}"),
    "get_resume": (
        "handle[State<{T}>](@{T} = {G}) {{\n"
        "    get(@Unit) -> {{ resume({V}) }},\n"
        "    put(@{T}) -> {{ resume(()) }}\n"
        "  }} in {{\n    rd(get(()))\n  }}"),
    "with_override": (
        "handle[State<{T}>](@{T} = {G}) {{\n"
        "    get(@Unit) -> {{ resume(@{T}.0) }} with @{T} = {V},\n"
        "    put(@{T}) -> {{ resume(()) }}\n"
        "  }} in {{\n    let @Int = rd(get(()));\n    rd(get(()))\n  }}"),
    "state_value_let": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    {V}\n  }};\n"
        "  rd(@{T}.0)"),
    "state_value_apply": (
        "let @FT = fn(@{B} -> @Int) effects(pure) {{ rd(@{B}.0) }};\n"
        "  apply_fn(@FT.0, " + _STATE_BOOL + " in {{\n    {V}\n  }})"),
    "state_value_return": "rd(hv(@Int.0))",
    "exn_throw": (
        "handle[Exn<{T}>] {{\n    throw(@{T}) -> {{ rd(@{T}.0) }}\n"
        "  }} in {{\n    throw({V})\n  }}"),
    "exn_binder": (
        "handle[Exn<{B}>] {{\n    throw(@{T}) -> {{ rd(@{T}.0) }}\n"
        "  }} in {{\n    throw({V})\n  }}"),
    "exn_clause_value": (
        "let @{T} = handle[Exn<Int>] {{\n    throw(@Int) -> {{ {V} }}\n"
        "  }} in {{\n    throw(@Int.0)\n  }};\n  rd(@{T}.0)"),
    "exn_body_value": (
        "let @{T} = handle[Exn<Int>] {{\n    throw(@Int) -> {{ {G} }}\n"
        "  }} in {{\n    {V}\n  }};\n  rd(@{T}.0)"),
}

_EXN_INT = ("handle[Exn<Int>] {{\n      throw(@Int) -> {{ {G} }}\n    }}")

#: The handle's value at a join (inside its body, around it, a handle in a
#: handle) and at the other positions a value takes its requirement at (a
#: call's argument, a constructor's field): the hand-down's own positions.
JOIN_POSITIONS: dict[str, str] = {
    "if_in_body": (
        "let @{T} = " + _STATE_BOOL + " in {{\n"
        "    if @Int.0 > 100 then {{ {V} }} else {{ {V} }}\n  }};\n  rd(@{T}.0)"),
    "match_in_body": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    match @Int.0 > 100 {{\n"
        "      true -> {V},\n      false -> {V}\n    }}\n  }};\n  rd(@{T}.0)"),
    # Each arm on its own: the arm is chosen by the cell (opaque to the
    # verifier, so both arms stay a join), not by the tested value, so the
    # satisfying and the violating argument both run the arm holding it.
    "if_then_arm": (
        "let @{T} = " + _STATE_BOOL + " in {{\n"
        "    if get(()) then {{ {V} }} else {{ {G} }}\n  }};\n  rd(@{T}.0)"),
    "if_else_arm": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    put(false);\n"
        "    if get(()) then {{ {G} }} else {{ {V} }}\n  }};\n  rd(@{T}.0)"),
    "match_true_arm": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    match get(()) {{\n"
        "      true -> {V},\n      false -> {G}\n    }}\n  }};\n  rd(@{T}.0)"),
    "match_false_arm": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    put(false);\n"
        "    match get(()) {{\n      true -> {G},\n      false -> {V}\n"
        "    }}\n  }};\n  rd(@{T}.0)"),
    "block_in_body": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    put(false);\n    {V}\n"
        "  }};\n  rd(@{T}.0)"),
    "exn_in_state": (
        "let @{T} = " + _STATE_BOOL + " in {{\n    " + _EXN_INT + " in {{\n"
        "      {V}\n    }}\n  }};\n  rd(@{T}.0)"),
    "state_in_exn": (
        "let @{T} = " + _EXN_INT + " in {{\n    " + _STATE_BOOL + " in {{\n"
        "      {V}\n    }}\n  }};\n  rd(@{T}.0)"),
    "call_argument": "take(" + _STATE_BOOL + " in {{\n    {V}\n  }})",
    "ctor_field": (
        "let @Option<{T}> = Some(" + _STATE_BOOL + " in {{\n    {V}\n  }});\n"
        "  match @Option<{T}>.0 {{\n    Some(@{T}) -> rd(@{T}.0),\n    None -> 0\n  }}"),
    "if_outside": (
        "let @{T} = if @Int.0 != 7 then {{ " + _STATE_BOOL + " in {{\n"
        "    {V}\n  }} }} else {{ {G} }};\n  rd(@{T}.0)"),
}
HANDLER_POSITIONS = dict(POSITIONS)
POSITIONS.update(JOIN_POSITIONS)

_HV = ("private fn hv(@Int -> @{T})\n  requires(true)\n  ensures(true)\n"
       "  effects(pure)\n{{\n  " + _STATE_BOOL + " in {{\n    {V}\n  }}\n}}\n\n")

_PLAIN = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


#: Where the value comes from: an opaque call's result (`mk`), or a
#: construction written at the position over an opaque scalar (`sc`).
SOURCES = ("call", "built")


def _program(shape: str, position: str, source: str = "call") -> str:
    t, b, mk, rd, good, _, built = SHAPES[shape]
    value = built if source == "built" else "mk(@Int.0)"
    assert value is not None
    fill = {"T": t, "B": b, "G": good, "V": value}
    src = PRELUDE
    if position == "state_value_apply":
        src = f"type FT = fn({t} -> Int) effects(pure);\n" + src
    src += f"\nprivate fn sc(@Int -> @Int)\n{_PLAIN}{{\n  @Int.0\n}}\n\n"
    src += f"private fn mk(@Int -> @{b})\n{_PLAIN}{{\n  {mk}\n}}\n\n"
    src += f"private fn rd(@{b} -> @Int)\n{_PLAIN}{{\n  {rd}\n}}\n\n"
    if position == "call_argument":
        src += f"private fn take(@{t} -> @Int)\n{_PLAIN}{{\n  rd(@{t}.0)\n}}\n\n"
    if position == "state_value_return":
        src += _HV.format(**fill)
    src += (f"public fn go(@Int -> @Int)\n{_PLAIN}{{\n  "
            + POSITIONS[position].format(**fill) + "\n}\n")
    return src


# The verdicts.  CHECKED: `vera verify` accepts, every narrowing row is
# verified or `tier3` with a check behind it, and a violating argument traps.
# REFUSED: the solver refutes the narrowing (E503, E505), and the compiled
# program traps.  REFUSED_UNCHECKED: refuted, and a component the refusal
# answers runs through.  DISCLOSED: accepted with a row no check guards
# (E504, E506), and the value runs through.  No cell is a row listed as
# checked that no check answers (E541): rule 2, spec §2.6.5.
CHECKED, REFUSED, REFUSED_UNCHECKED = "checked", "refused", "refused_unchecked"
DISCLOSED = "disclosed"

_ALL = tuple(HANDLER_POSITIONS)
#: The positions the verifier decides a narrowing at (it refutes one there):
#: every one bar a clause's binder, a `get` clause's body and a `with`
#: override, which it reads in the clause's own scope, and an `Exn`
#: handle's value.
_DECIDED = ("state_init", "put_argument", "state_value_let",
            "state_value_apply", "state_value_return", "exn_throw")
#: The write boundaries the verifier refutes a built `Nat` component at.
_NAT_WRITES = ("state_init", "put_argument", "exn_throw")
_BINDERS = ("put_binder", "exn_binder")


def _verdicts() -> dict[tuple[str, str], str]:
    v: dict[tuple[str, str], str] = {}
    for shape in ("tuple_nat", "option_nat", "short"):
        v.update({(shape, p): CHECKED for p in _ALL})
    for shape in ("nat", "small"):
        v.update({(shape, p): REFUSED if p in _DECIDED else CHECKED for p in _ALL})
    v.update({("option_short", p): DISCLOSED for p in _ALL})
    # A refined tuple component: checked where a boundary decomposes the
    # value (a closure argument, a function's return), disclosed at a
    # binder and everywhere else (rule 2, spec §2.6.5).
    v.update({("tuple_short", p): DISCLOSED for p in _ALL})
    v.update({("tuple_short", p): CHECKED
              for p in ("state_value_apply", "state_value_return")})
    v.update({("tuple_small", p): DISCLOSED for p in _ALL})
    v.update({("tuple_small", p): REFUSED_UNCHECKED
              for p in _DECIDED})
    v.update({("tuple_small", p): REFUSED
              for p in ("state_value_apply", "state_value_return")})
    # A refined payload: refuted where the verifier decides it, disclosed
    # elsewhere.
    v.update({("option_small", p): REFUSED_UNCHECKED if p in _DECIDED
              else DISCLOSED for p in _ALL})
    assert set(v) == {(s, p) for s in SHAPES for p in HANDLER_POSITIONS}
    out = {(s, "call", p): verdict for (s, p), verdict in v.items()}
    out.update({(s, "built", p): verdict for (s, p), verdict in _built().items()})
    out.update(_joins())
    return out


#: The join positions the verifier decides a narrowing at: every one bar a
#: handle nested in a handle (an `Exn` handle's value, which it does not
#: read) and an arm chosen by the cell (a refutation under a premise over
#: `get`'s stand-in is no violation, spec §6.4.2, so the narrowing is left to
#: its run-time check).
_NESTED = ("exn_in_state", "state_in_exn")
_ARMS = ("if_then_arm", "if_else_arm", "match_true_arm", "match_false_arm")
_UNDECIDED = _NESTED + _ARMS
_JOIN_DECIDED = tuple(p for p in JOIN_POSITIONS if p not in _UNDECIDED)


def _joins() -> dict[tuple[str, str, str], str]:
    """The handle's value at the hand-down's own positions.  As at the
    handler positions: `Nat`, `Short` and every built composite are
    checked (refused where the verifier decides a `Nat` or a `Small`); a
    refined payload from a call is disclosed where it is not refuted; a
    refined tuple component from a call is checked where a boundary
    decomposes it (a call's argument) and disclosed everywhere else (rule
    2, spec §2.6.5: the `let`'s verdict)."""
    v: dict[tuple[str, str, str], str] = {}
    j = tuple(JOIN_POSITIONS)
    for shape in ("nat", "small"):
        v.update({(shape, "call", p): CHECKED if p in _UNDECIDED else REFUSED for p in j})
    for shape in ("short", "tuple_nat", "option_nat"):
        v.update({(shape, "call", p): CHECKED for p in j})
    v.update({("option_short", "call", p): DISCLOSED for p in j})
    v.update({("option_small", "call", p): DISCLOSED if p in _UNDECIDED
              else REFUSED_UNCHECKED for p in j})
    v.update({("tuple_short", "call", p): DISCLOSED for p in j})
    v[("tuple_short", "call", "call_argument")] = CHECKED
    v.update({("tuple_small", "call", p): DISCLOSED if p in _UNDECIDED
              else REFUSED_UNCHECKED for p in j})
    v[("tuple_small", "call", "call_argument")] = REFUSED
    for shape in ("tuple_nat", "option_nat", "tuple_short", "option_short"):
        v.update({(shape, "built", p): CHECKED for p in j})
    for shape in ("tuple_small", "option_small"):
        v.update({(shape, "built", p): CHECKED if p in _UNDECIDED else REFUSED
                  for p in j})
    return v


def _built() -> dict[tuple[str, str], str]:
    """A composite built at the position: its construction is a store,
    which checks the component (or payload) by its own row, at every
    position bar a clause binder narrower than what it receives.  The
    verifier refutes a narrowing it decides, a `Nat` one only at a write
    boundary (inside a `handle`'s value it reads the construction nowhere),
    a `Small` one at every position it decides a call's result at."""
    v: dict[tuple[str, str], str] = {}
    for shape, decided in (("tuple_nat", _NAT_WRITES), ("option_nat", _NAT_WRITES),
                           ("tuple_short", ()), ("option_short", ()),
                           ("tuple_small", _DECIDED),
                           ("option_small", _DECIDED)):
        v.update({(shape, p): REFUSED if p in decided else CHECKED for p in _ALL})
        v.update({(shape, p): DISCLOSED for p in _BINDERS
                  if not shape.endswith("_nat")})
    return v


VERDICTS = _verdicts()

_NARROWING = ("refine_bind", "nat_bind")
_REFUTED = {"E503", "E505"}


@pytest.mark.parametrize(("shape", "source", "position"), sorted(VERDICTS))
def test_a_handler_position_holds_its_value_to_its_type(
    shape: str, source: str, position: str,
) -> None:
    verdict = VERDICTS[(shape, source, position)]
    src = _program(shape, position, source)
    bad = SHAPES[shape][5]
    verified = pipeline.verify(src, reconcile=True)
    assert verified.ran, verified.checked.errors
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None
    mismatches = [m.obligation for m in reconciled.reconciliation.mismatches]
    errors = {d.error_code for d in verified.errors}
    statuses = sorted(o.status for o in verified.obligations
                      if o.kind in _NARROWING and o.status != "verified")
    compiled = pipeline.compile(src)
    assert pipeline.run(compiled, fn="go", args=[SATISFYING]).value == SATISFYING
    ran = pipeline.run(compiled, fn="go", args=[bad])
    if verdict == CHECKED:
        assert verified.ok, (errors, statuses)
        assert mismatches == [] and statuses, statuses
        assert set(statuses) == {"tier3"}, statuses
        assert ran.trap is not None, ran.value
    elif verdict in (REFUSED, REFUSED_UNCHECKED):
        assert errors and errors <= _REFUTED, errors
        assert "violated" in statuses and mismatches == [], (statuses, mismatches)
        if verdict == REFUSED:
            assert ran.trap is not None, ran.value
        else:
            assert ran.value == bad
    else:
        assert verdict == DISCLOSED
        assert verified.ok, errors
        assert "tier3_unguarded" in statuses and mismatches == [], statuses
        assert ran.value == bad


# ---------------------------------------------------------------------
# The reported lines, red first.
# ---------------------------------------------------------------------

def _checked_and_trapping(src: str, fn: str, bad: float | int,
                          good: float | int, kind: str,
                          check: str | None = None) -> str:
    """Assert *src* verifies with its *kind* row checked (`tier3`, and a
    check in *fn* that is the runtime half of *check*, by default *kind*,
    answering it) and that *bad* traps; return the trap."""
    verified = pipeline.verify(src, reconcile=True)
    assert verified.ok, [(d.error_code, d.description) for d in verified.errors]
    rows = [o.status for o in verified.obligations if o.kind == kind]
    assert "tier3" in rows and "tier3_unguarded" not in rows, rows
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None
    assert reconciled.reconciliation.mismatches == []
    compiled = pipeline.compile(src)
    assert compiled.checks(obligation=check or kind, function=fn)
    assert pipeline.run(compiled, fn=fn, args=[good]).ok
    ran = pipeline.run(compiled, fn=fn, args=[bad])
    assert ran.trap is not None, ran.value
    return str(ran.trap)


_PAYLOAD_1837 = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn go(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<PosInt> = handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    Some(float_to_int(@Float64.0))
  };
  option_unwrap_or(@Option<PosInt>.0, 1)
}
"""


def test_repro_a_payload_built_as_a_handles_value_is_checked_1837() -> None:
    trap = _checked_and_trapping(_PAYLOAD_1837, "go", -5.0, 3.0, "refine_bind")
    assert "Refinement violation in Some(" in trap, trap


_HANDLE_AT_APPLY = """\
type Short = {{ @Int | string_length(to_string(@Int.0)) < 3 }};
type FT = fn(Tuple<{C}, Int> -> Int) effects(pure);

private fn mk(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  Tuple(@Int.0, 7)
}}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @FT = fn(@Tuple<Int, Int> -> @Int) effects(pure) {{
    let Tuple<@Int, @Int> = @Tuple<Int, Int>.0;
    @Int.1
  }};
  apply_fn(@FT.0,
    handle[State<Int>](@Int = @Int.0) {{
      get(@Unit) -> {{ resume(@Int.0) }},
      put(@Int) -> {{ resume(()) }}
    }} in {{
      mk(get(()))
    }}
  )
}}
"""


def test_repro_a_handles_value_at_a_closure_argument_has_its_refined_component_checked() -> None:
    trap = _checked_and_trapping(
        _HANDLE_AT_APPLY.format(C="Short"), "go", 5000, 3, "refine_bind")
    assert "closure argument (tuple component)" in trap, trap


def test_repro_a_handles_value_at_a_closure_argument_has_its_nat_component_checked() -> None:
    trap = _checked_and_trapping(
        _HANDLE_AT_APPLY.format(C="Nat"), "go", -5, 3, "nat_bind",
        check="component_coercion")
    assert "Negative value bound into a @Nat slot" in trap, trap


_RESUME = """\
type Pos = { @Int | @Int.0 > 0 };

public fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Pos) -> { resume(()) }
  } in {
    get(())
  }
}
"""

_RESUME_SET = """\
type RS = { @Set<Int> | set_size(@Set<Int>.0) > 0 };

public fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<RS>](@RS = set_add(set_new(), 1)) {
    get(@Unit) -> { resume(if @Int.0 > 0 then { set_add(set_new(), 1) } else { set_new() }) },
    put(@RS) -> { resume(()) }
  } in {
    set_size(get(()))
  }
}
"""


def test_repro_a_get_resume_at_a_refined_cell_runs_the_predicate_guard() -> None:
    trap = _checked_and_trapping(_RESUME, "g", -5, 3, "refine_bind")
    assert "Refinement violation in State get resume" in trap, trap


def test_repro_a_get_resume_at_a_refined_set_cell_runs_the_predicate_guard() -> None:
    trap = _checked_and_trapping(_RESUME_SET, "g", -1, 1, "refine_bind")
    assert "Refinement violation in State get resume" in trap, trap


def test_repro_a_nat_payload_built_as_a_handles_value_is_obligated() -> None:
    """The `Nat` requirement reaches a handle's value as a block's tail's
    does: `Some(sc(x))` built there at `Option<Nat>` was listed nowhere,
    verified clean and returned -5."""
    src = _program("option_nat", "state_value_let", "built")
    trap = _checked_and_trapping(src, "go", -5, 3, "nat_bind",
                                 check="component_coercion")
    assert "Negative value bound into a @Nat slot" in trap, trap


_REFUTED_IN_HANDLE = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<PosInt> = handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    Some(0 - 5)
  };
  option_unwrap_or(@Option<PosInt>.0, 1)
}
"""


def test_a_payload_refuted_inside_a_handle_keeps_its_refusal() -> None:
    """The value's record is the rows the hand-down lists below a handle
    (the payload's), now that they are checks: a payload the solver refutes
    is refused (E505) at the payload, not left to its run-time check."""
    verified = pipeline.verify(_REFUTED_IN_HANDLE, reconcile=True)
    assert [(o.status, o.error_code, o.line) for o in verified.obligations
            if o.kind == "refine_bind" and o.status != "verified"] == [
        ("violated", "E505", 12)]
    assert {d.error_code for d in verified.errors} == {"E505"}


# The gather's own shape (`verifier._construction_skeleton`,
# `_handle_value_skeleton`): which stores it reads below a handle's value,
# and that it reads a handle's value and no other join's.

_STORE_IN_HANDLE = """\
type Small = {{ @Int | @Int.0 < 10 }};

private fn sc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  @Int.0
}}

private fn pair(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  Tuple(@Int.0, 0)
}}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  let @{T} = handle[State<Bool>](@Bool = true) {{
    get(@Unit) -> {{ resume(@Bool.0) }},
    put(@Bool) -> {{ resume(()) }}
  }} in {{
    {V}
  }};
  {N}
}}
"""


def _records(src: str) -> list[tuple[str, str, int, int]]:
    verified = pipeline.verify(src, reconcile=True)
    return sorted((o.status, o.error_code, o.line, o.column)
                  for o in verified.obligations
                  if o.kind == "refine_bind" and o.status != "verified")


def test_an_array_literal_refuted_inside_a_handle_keeps_its_refusal() -> None:
    """The value's record reads an array literal's elements below a handle:
    `[sc(x)]` at `Array<Small>` is refuted at the element."""
    src = _STORE_IN_HANDLE.format(T="Array<Small>", V="[sc(@Int.0)]",
                                  N="array_length(@Array<Small>.0)")
    assert _records(src) == [("violated", "E505", 28, 6)]


def test_a_map_insert_value_inside_a_handle_has_the_values_record() -> None:
    """The value's record reads a `map_insert`'s value below a handle: the
    value is checked at run time, and the record says so (the `E506`
    note), where a record keyed to no row is dropped."""
    src = _STORE_IN_HANDLE.format(
        T="Map<Int, Small>", V="map_insert(map_new(), 1, sc(@Int.0))",
        N="map_size(@Map<Int, Small>.0)")
    assert _records(src) == [("tier3", "E506", 28, 30)]


#: The other stores below a handle's value, each read by the value's record
#: (the hunt over this change's decisions): a store's key and element, a
#: construction below a construction, an element below a payload and a
#: component a call's result carries below a payload.
_STORES_IN_HANDLE = {
    "set_element": ("Set<Small>", "set_add(set_new(), sc(@Int.0))",
                    "set_size(@Set<Small>.0)", [("tier3", "E506", 28, 24)]),
    "map_key": ("Map<Small, Int>", "map_insert(map_new(), sc(@Int.0), 1)",
                "map_size(@Map<Small, Int>.0)", [("tier3", "E506", 28, 27)]),
    "nested_construction": ("Option<Tuple<Small, Int>>", "Some(Tuple(sc(@Int.0), 0))",
                            "0", [("violated", "E505", 28, 16)]),
    "element_below_payload": ("Option<Array<Small>>", "Some([sc(@Int.0)])", "0",
                              [("tier3", "E506", 28, 11)]),
    "component_below_payload": ("Option<Tuple<Small, Int>>", "Some(pair(@Int.0))",
                                "0", [("violated", "E505", 28, 10)]),
}


@pytest.mark.parametrize("store", sorted(_STORES_IN_HANDLE))
def test_a_store_below_a_handles_value_has_the_values_record(store: str) -> None:
    t, value, use, want = _STORES_IN_HANDLE[store]
    assert _records(_STORE_IN_HANDLE.format(T=t, V=value, N=use)) == want


_RESUME_REFINED_NAT = """\
type SmallNat = { @Nat | @Nat.0 < 10 };

public fn g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<SmallNat>](@SmallNat = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@SmallNat) -> { resume(()) }
  } in {
    nat_to_int(get(()))
  }
}
"""


def test_a_get_resume_runs_the_predicate_before_the_sign() -> None:
    """At a refinement over `Nat`, the `get` resume runs the predicate's
    check first, as `put`'s write does: -5 traps at the refinement."""
    ran = pipeline.run(_RESUME_REFINED_NAT, fn="g", args=[-5])
    assert ran.trap is not None, ran.value
    assert "Refinement violation in State get resume" in str(ran.trap), ran.trap
    assert pipeline.run(_RESUME_REFINED_NAT, fn="g", args=[3]).value == 3


_RESUME_NAT = _RESUME_REFINED_NAT.replace(
    "type SmallNat = { @Nat | @Nat.0 < 10 };\n\n", "").replace("SmallNat", "Nat")


def _two_tuple_sites() -> str:
    """One function with two handle values at `Tuple<Short, Int>`: one in a
    constructor's field (disclosed: a store checks no tuple component below
    it) and one at a call's argument (checked by the callee's boundary)."""
    field = _program("tuple_short", "ctor_field")
    arg = _program("tuple_short", "call_argument")
    take = arg[arg.index("private fn take"):arg.index("public fn go")]
    call = arg.split("public fn go")[1].split("{", 1)[1].rsplit("}", 1)[0].strip()
    return field.replace("public fn go", take + "public fn go").replace(
        "  match @Option<Tuple<Short, Int>>.0 {",
        "  " + call + " + match @Option<Tuple<Short, Int>>.0 {")


def test_two_handle_values_in_one_function_keep_their_own_rows() -> None:
    """Each value's record is keyed to its own component rows: the field's
    is disclosed where its leaf stands, the argument's is a run-time check
    noted at its own leaf, not at the other value's handle.  (A record
    that took every path row of its function moved the argument's note to
    its handle, line 48.)"""
    src = _two_tuple_sites()
    lines = src.splitlines()
    leaves = [i for i, text in enumerate(lines, 1) if text.strip() == "mk(@Int.0)"]
    verified = pipeline.verify(src, reconcile=True)
    assert verified.ok, [d.error_code for d in verified.errors]
    notes = sorted(d.location.line for d in verified.warnings
                   if d.error_code == "E506")
    assert notes == leaves, (notes, leaves)
    statuses = sorted((o.line, o.status) for o in verified.obligations
                      if o.kind in _NARROWING and o.line in leaves)
    assert statuses == [(leaves[0], "tier3_unguarded"), (leaves[1], "tier3")], statuses


_RECEIVER_HEAD = """\
type Pos = { @Int | @Int.0 > 0 };

private fn opq(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @TYPE = HANDLE;
  READ
}
"""
#: A store whose receiver is itself a store: the table hands the value's
#: type into a `map_insert`'s and a `set_add`'s receiver as into its key,
#: value and element, so the inner value is held to the component type.
_RECEIVERS = {
    "map": ("Map<Int, {C}>", "map_insert(map_insert(map_new(), 1, opq(@Int.0)), 2, 3)",
            "map_size(@Map<Int, {C}>.0)", 2),
    "set": ("Set<{C}>", "set_add(set_add(set_new(), opq(@Int.0)), 2)",
            "set_size(@Set<{C}>.0)", 2),
    "map_in_map": ("Map<Int, Map<Int, {C}>>",
                   "map_insert(map_new(), 1, map_insert(map_insert(map_new(), 1, opq(@Int.0)), 2, 3))",
                   "map_size(@Map<Int, Map<Int, {C}>>.0)", 1),
    "ctor": ("Option<Map<Int, {C}>>", "Some(map_insert(map_insert(map_new(), 1, opq(@Int.0)), 2, 3))",
             "0", 0),
}
_RECEIVER_HANDLES = {
    "state_body": ("handle[State<Bool>](@Bool = true) {{\n    get(@Unit) -> {{ resume(@Bool.0) }},\n"
                   "    put(@Bool) -> {{ resume(()) }}\n  }} in {{\n    {V}\n  }}"),
    "exn_clause": "handle[Exn<Int>] {{\n    throw(@Int) -> {{ {V} }}\n  }} in {{\n    throw(@Int.0)\n  }}",
}


def test_repro_a_nested_receiver_below_a_handles_value_is_checked() -> None:
    """The value stored in a nested receiver (`map_insert(map_insert(...,
    opq(x)), ...)`) below a handle's value has its row recorded and its
    check emitted: -5 traps, 3 runs through.  Sixteen programs, one test:
    each store, each handle, at `Pos` and at `Nat`."""
    for store, (ty, value, read, out) in sorted(_RECEIVERS.items()):
        for handle, form in sorted(_RECEIVER_HANDLES.items()):
            for comp in ("Pos", "Nat"):
                where = (store, handle, comp)
                src = (_RECEIVER_HEAD.replace("TYPE", ty.format(C=comp))
                       .replace("HANDLE", form.format(V=value))
                       .replace("READ", read.format(C=comp)))
                verified = pipeline.verify(src, reconcile=True)
                assert verified.ok, (where, [d.error_code for d in verified.errors])
                statuses = sorted(o.status for o in verified.obligations
                                  if o.kind in _NARROWING)
                assert statuses and set(statuses) == {"tier3"}, (where, statuses)
                reconciled = verified.reconciled
                assert reconciled is not None and reconciled.reconciliation is not None
                assert reconciled.reconciliation.mismatches == [], where
                compiled = pipeline.compile(src)
                assert pipeline.run(compiled, fn="go", args=[-5]).trap is not None, where
                assert pipeline.run(compiled, fn="go", args=[3]).value == out, where


_STORE_JOIN = """\
type Small = { @Int | @Int.0 < 10 };

private fn mk(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn mt(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, 0)
}

public fn go(@Bool, @Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<TYPE> = [JOIN, JOIN];
  0
}
"""
#: A join whose arm stands where an array literal stores it: the arm under
#: test holds LEAF, the other a literal of the component type.
_STORE_JOINS = {
    "if_then": "if @Bool.0 then { LEAF } else { Tuple(1, 0) }",
    "if_else": "if @Bool.0 then { Tuple(1, 0) } else { LEAF }",
    "match_arm": "match @Bool.0 { true -> LEAF, false -> Tuple(1, 0) }",
}


def _store_join(component: str, leaf: str, join: str) -> str:
    return _STORE_JOIN.replace("TYPE", component).replace(
        "JOIN", _STORE_JOINS[join].replace("LEAF", leaf))


def test_repro_a_stored_construction_through_a_join_keeps_its_own_component_type() -> None:
    """`Tuple(float_to_int(f), 0)` at `Tuple<Nat, Int>` through a join's arm into an
    array literal's element: the arm is handed the store's own component
    type, so the field's `Nat` row is the store's sign check, answered by
    the `Nat` guard, not by a composite coercion."""
    for join in sorted(_STORE_JOINS):
        verified = pipeline.verify(
            _store_join("Tuple<Nat, Int>", "Tuple(float_to_int(@Float64.0), 0)", join), reconcile=True)
        assert verified.ok, (join, [d.error_code for d in verified.errors])
        reconciled = verified.reconciled
        assert reconciled is not None and reconciled.reconciliation is not None
        rc = reconciled.reconciliation
        emitters = {c.emitter for o, c in rc.pairs if o.kind == "nat_bind"}
        assert emitters == {"wasm/operators.py:_emit_nat_bind_guard"}, (join, emitters)


_UNEVALUATED_REASONS = """\
public fn uninlined_put(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = 10 / @Int.0
  } in {
    get(())
  }
}

public fn nested_uninlined(@Int -> @String)
  requires(@Int.0 != 0)
  ensures(string_length(@String.result) >= handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = 10 / @Int.0
  } in {
    get(())
  })
  effects(pure)
{
  "ab"
}
"""


def test_repro_a_row_no_check_evaluates_names_its_innermost_reason() -> None:
    """A division in a `put` clause no call inlines is disclosed with that
    clause's reason, also where the clause sits inside an `ensures` that is
    not lowered (two reasons stacked: the innermost one names the row)."""
    verified = pipeline.verify(_UNEVALUATED_REASONS)
    disclosed = {(d.location.line, d.location.column): d.description
                 for d in verified.warnings
                 if d.error_code == "E543" and "'div_zero'" in d.description}
    assert set(disclosed) == {(8, 45), (18, 45)}, disclosed
    for text in disclosed.values():
        assert "the handler clause is inlined at no operation call" in text, text


def test_a_block_tail_hands_the_store_its_own_component_type() -> None:
    """A `Tuple<Nat, Int>` built as a handle's value in a constructor's
    field: the handle body's block tail is handed the store's own component
    type, so the field's `Nat` row is the store's sign check, answered by
    the `Nat` guard, not by a composite coercion."""
    src = _program("tuple_nat", "ctor_field", "built")
    verified = pipeline.verify(src, reconcile=True)
    assert verified.ok, [d.error_code for d in verified.errors]
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None
    rc = reconciled.reconciliation
    emitters = [c.emitter for o, c in rc.pairs if o.kind == "nat_bind"]
    assert emitters == ["wasm/operators.py:_emit_nat_bind_guard"], emitters
    assert rc.mismatches == [], rc.mismatches


@pytest.mark.parametrize("shape", ["nat", "short"])
def test_a_clause_check_is_answered_at_each_inlined_site(shape: str) -> None:
    """A `with` override inlined at two `get` sites lists a row per site,
    each under its site's evaluation, and the join pairs each with its own
    emitted check: none unanswered (E541), none unrecorded (W004).  The
    clause's lowering ties the check to the site it is inlined at."""
    src = _program(shape, "with_override")
    verified = pipeline.verify(src, reconcile=True)
    assert verified.ok, [d.error_code for d in verified.errors]
    codes = {d.error_code for d in verified.errors} | {
        d.error_code for d in verified.warnings}
    assert not codes & {"E541", "W004"}, codes
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None
    rc = reconciled.reconciliation
    assert rc.mismatches == [], rc.mismatches
    line = next(i for i, text in enumerate(src.splitlines(), 1)
                if " with @" in text)
    paired = sorted(c.row for o, c in rc.pairs
                    if o.kind in _NARROWING and o.line == line)
    assert len(paired) == 2 and len(set(paired)) == 2, paired


def test_a_get_resume_at_a_nat_cell_runs_the_sign_check() -> None:
    """The sign check is the only one at a `Nat` cell: -5 traps there, not
    at a refinement.  (At a refinement over `Nat` the predicate's check
    holds the base's sign too: -5 satisfies `@Nat.0 < 10` above and still
    traps at the refinement, so the sign check after it is reached only
    here.)"""
    ran = pipeline.run(_RESUME_NAT, fn="g", args=[-5])
    assert ran.trap is not None, ran.value
    assert "Negative value bound into a @Nat slot" in str(ran.trap), ran.trap
    assert "Refinement violation" not in str(ran.trap), ran.trap
    assert pipeline.run(_RESUME_NAT, fn="g", args=[3]).value == 3


_JOIN_NOT_A_HANDLE = """\
type Small = { @Int | @Int.0 < 10 };

private fn sc(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Small> = if @Int.0 > 100 then { Some(sc(@Int.0)) } else { mk(@Int.0) };
  option_unwrap_or(@Option<Small>.0, 0)
}
"""


def test_an_if_joins_construction_keeps_its_own_record() -> None:
    """Below an `if` the construction descent records the field itself, so
    the join's value keeps its own record (at the `mk` arm) beside it: the
    gather reads a handle's value and no other join's."""
    assert _records(_JOIN_NOT_A_HANDLE) == [
        ("violated", "E505", 24, 52), ("violated", "E505", 24, 73)]
