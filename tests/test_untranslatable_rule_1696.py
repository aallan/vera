"""One rule for an expression the verifier cannot translate (#1696).

THE MECHANISM.  An expression outside the decidable fragment — a closure
applied through `apply_fn`, an effect operation's result, a generic call, a
fold, a `Map` or `Set` built in place, a `match` on `map_get`'s result, a
refinement predicate calling a host function — was modelled as an
unconstrained value, and the fact around it was handled four ways at once:

* a `let` of one bound a span-named `_opaque_*` constant, which only a
  postcondition's or a primitive operation's refutation knew to discount; a
  binding-site narrowing was refuted over it (#1470's E503, E505 and E526
  members, m01b, m09, m13, m15);
* a call's result was counter-named, so each pass over a `let` minted a new
  one and an `assume` constrained a constant the goal never read (#1601);
* an `if` whose condition did not translate translated both branches with
  no path condition, so a callee's `ensures` was assumed on runs that never
  made the call (#1571, a false Tier 1 the compiled postcondition catches);
* a call with one untranslatable argument was dropped whole, its `ensures`
  with it (#1595's `decreases` and precondition, m11), and a literal with
  one untranslatable element became an unknown array (m09).

THE RULE (`vera/smt.py`, PLAN § 2 of the v0.2.7 sprint).  R1: one stand-in
per untranslatable node, of the sort of its checked type, named by the
node's identity and the terms it reads, seen as one term by every pass; a
call's result is named by its call node and argument terms the same way.
R2: the stand-in carries what its type states and nothing more: `Nat`'s
`>= 0` and a refinement's translatable conjuncts.  R3: the context
translates around it — an untranslatable condition is a stand-in `Bool`
each branch's facts hold under, a `match` arm runs under the negation of
every earlier arm's condition, a call with a stand-in argument keeps its
`ensures`, a literal keeps its length, a `State` handler whose every clause
resumes once in tail position has its body's value.  R4: a `sat` whose
goal, assumptions or path conditions mention a stand-in reports the row
undecided (Tier 3 behind its guard), for every kind and a call precondition
included, unless the goal is false for every value the stand-in could take,
which is a violation; a stand-in's model value is not a run.

THE INSTRUMENT.  The refutation-site × stand-in-source matrix #1470 asked
for: every site that can refuse a program (E500, E501, E502, E503, E505,
E526, E527, E528, E529) crossed with every source of a value the verifier
cannot pin (a refinement with an untranslatable conjunct at a parameter, a
return and a type argument; an untranslatable `let`, condition, argument,
scrutinee and literal element; a `State` read; a handler's value; a fold;
`set_size`; a generic call; a call read twice).  Each cell is a program
whose run completes, so a refusal would be false: the cell asserts no
refusal and that the run completes (`vera run` is the oracle).  Beside it:
the proof direction (for each source, a program whose run traps proves
nothing), #1470's permutation row (an unrelated `let` changes no verdict),
the `State.get(())`/`get(())` spelling row, the `repro` pins of the issue's
thirteen reproducing lines, a regression cell for m10, and strict xfails for
m04 (the index's post-fact, #1695) and m06 (an element's `>= 0`, #1814).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/smt.py", "vera/verifier.py"])

FILE = "untranslatable.vera"


# =====================================================================
# Helpers
# =====================================================================

def _verify(source: str) -> pipeline.Verified:
    """Verify *source*, which must type-check cleanly."""
    verified = pipeline.verify(source, file=FILE)
    errors = verified.checked.errors
    assert not errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:90]) for d in errors]}")
    return verified


def _run(source: str, fn: str, args: list[int]) -> pipeline.Ran:
    """Compile and run *fn*; the fixture must compile."""
    ran = pipeline.run(source, fn, args, file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, (
        "fixture must compile, got: "
        f"{[(d.error_code, d.description[:90]) for d in ran.compiled.errors]}"
        if ran.compiled is not None else "no compile")
    return ran


def _statuses(verified: pipeline.Verified, kind: str) -> list[str]:
    """The status of every *kind* obligation, in record order."""
    return [o.status for o in verified.obligations if o.kind == kind]


def _codes(verified: pipeline.Verified) -> list[str]:
    return sorted(d.error_code for d in verified.errors)


def _warning_codes(verified: pipeline.Verified) -> list[str]:
    return sorted(d.error_code for d in verified.warnings)


def _ensures_status(verified: pipeline.Verified, fn: str) -> str:
    (status,) = [o.status for o in verified.obligations
                 if o.kind == "ensures" and o.fn_name == fn]
    return status


# =====================================================================
# The sources: a value the verifier cannot pin, which a run makes 5
# =====================================================================

_U = """\
type U = { @Int | int_to_float(@Int.0) > 0.0 && @Int.0 > 0 };
"""

_PICK = """\
private forall<T> fn pick(@Bool, @T, @T -> @T)
  requires(true)
  ensures(@T.result == @T.1 || @T.result == @T.0)
  effects(pure)
{
  if @Bool.0 then {
    @T.1
  } else {
    @T.0
  }
}
"""

_STATE_MAIN = """\

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = 4) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    f(())
  }
}
"""


@dataclass(frozen=True)
class Source:
    """One way a value the verifier cannot pin reaches an obligation.

    *value* is the expression the site reads (5 at run time); *prefix* the
    statements that bind it; *wrap* puts the site's body in the context the
    source needs (a `match` arm for a type argument), given the body and a
    neutral twin for the other arm."""

    id: str
    value: str
    decls: str = ""
    params: str = ""
    effects: str = "pure"
    prefix: str = ""
    wrap: Callable[[str, str], str] | None = None
    main: str = ""
    run_fn: str = "f"
    run_args: tuple[int, ...] = ()


def _in_some_arm(body: str, neutral: str) -> str:
    indent = "\n    "
    return (
        "match mk2(5) {\n"
        f"    Some(@U) -> {{{indent}{body.replace(chr(10), indent)}{indent}}},\n"
        f"    None -> {{{indent}{neutral.replace(chr(10), indent)}{indent}}}\n"
        "  }")


SOURCES: tuple[Source, ...] = (
    Source("s01_unstatable_parameter", "@U.0", decls=_U, params="@U", run_args=(5,)),
    Source("s02_unstatable_return", "mk(5)", decls=_U + """\

private fn mk(@Int -> @U)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""),
    Source("s03_unstatable_type_argument", "@U.0", decls=_U + """\

private fn mk2(@Int -> @Option<U>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""", wrap=_in_some_arm),
    Source("s04_untranslatable_let", "@Int.0",
           prefix="let @Int = apply_fn(fn(@Unit -> @Int) effects(pure) { 5 }, ());\n"),
    Source("s05_untranslatable_condition", "@Int.0",
           prefix="let @Int = if apply_fn(fn(@Unit -> @Bool) effects(pure) { true }, ()) "
                  "then { 5 } else { 7 };\n"),
    Source("s06_untranslatable_argument", "five(pick(true, 1, 2))", decls=_PICK + """\

private fn five(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 5)
  effects(pure)
{
  5
}
"""),
    Source("s07_untranslatable_scrutinee", "@Int.0",
           prefix='let @Map<String, Int> = map_insert(map_new(), "a", 2);\n'
                  'let @Int = match map_get(@Map<String, Int>.0, "a") {\n'
                  "  Some(@Int) -> 5,\n"
                  "  None -> 5\n"
                  "};\n"),
    Source("s08_literal_element", "@Int.0", decls=_PICK,
           prefix="let @Array<Int> = [pick(true, 1, 1), 2, 3];\n"
                  "let @Int = nat_to_int(array_length(@Array<Int>.0)) + 2;\n"),
    Source("s09_state_read", "nat_to_int(@Nat.0) + 1", params="@Unit",
           effects="<State<Nat>>", prefix="let @Nat = get(());\n", main=_STATE_MAIN,
           run_fn="main"),
    Source("s10_handler_value",
           "handle[State<Nat>](@Nat = 4) {\n"
           "    get(@Unit) -> { resume(@Nat.0) },\n"
           "    put(@Nat) -> { resume(()) }\n"
           "  } in {\n"
           "    nat_to_int(get(())) + 1\n"
           "  }"),
    Source("s11_fold",
           "array_fold([2, 3], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })"),
    Source("s12_set_size", "nat_to_int(set_size(set_add(set_add(set_new(), 1), 2))) + 3"),
    Source("s13_generic_call", "@Int.0", decls=_PICK,
           prefix="let @Int = pick(true, 5, 5);\n"),
    Source("s14_call_read_twice", "@Int.0", decls="""\
private fn ext(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 * 2 + 1
}
""", prefix="let @Int = ext(2);\nassume(@Int.0 == 5);\n"),
)


# =====================================================================
# The sites: every obligation kind that can refuse a program
# =====================================================================

@dataclass(frozen=True)
class Site:
    code: str
    kind: str
    body: Callable[[str], str]
    decls: str = ""
    ensures: str = "true"


SITES: tuple[Site, ...] = (
    Site("E500", "ensures", lambda v: v, ensures="@Int.result > 0"),
    Site("E501", "call_pre", lambda v: f"inv({v})", decls="""\
private fn inv(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  100 / @Int.0
}
"""),
    Site("E502", "nat_sub",
         lambda v: f"let @Nat = {v};\nlet @Nat = 1;\nnat_to_int(@Nat.1 - @Nat.0)"),
    Site("E503", "nat_bind", lambda v: f"let @Nat = {v};\n0"),
    Site("E505", "refine_bind", lambda v: f"let @Pos = {v};\n0",
         decls="type Pos = { @Int | @Int.0 > 0 };\n"),
    Site("E526", "div_zero", lambda v: f"100 / {v}"),
    Site("E527", "index_bounds",
         lambda v: f"let @Nat = {v};\nlet @Array<Int> = [1, 2, 3, 4, 5, 6];\n"
                   "@Array<Int>.0[@Nat.0]"),
    Site("E528", "int_overflow", lambda v: f"{v} + 1"),
    Site("E529", "float_to_int_domain", lambda v: f"float_to_int(int_to_float({v}))"),
)


def program(source: Source, site: Site, *, prelude: str = "") -> str:
    """The cell's program: *site*'s obligation over *source*'s value, in a
    function a run completes."""
    body = site.body(source.value)
    if source.wrap is not None:
        body = source.wrap(body, site.body("1"))
    indent = "\n  "
    stmts = (prelude + source.prefix).replace("\n", indent)
    params = f"{source.params} " if source.params else ""
    return (
        f"{source.decls}{site.decls}\n"
        f"public fn f({params}-> @Int)\n"
        f"  requires(true)\n"
        f"  ensures({site.ensures})\n"
        f"  effects({source.effects})\n"
        f"{{{indent}{stmts}{body.replace(chr(10), indent)}\n}}\n"
        f"{source.main}")


_CELLS = [
    pytest.param(site, source, id=f"{site.code}-{source.id}")
    for site in SITES for source in SOURCES
]


@pytest.mark.parametrize(("site", "source"), _CELLS)
def test_no_refutation_rests_on_a_stand_in(site: Site, source: Source) -> None:
    """The matrix: the obligation over the source's value is never refused,
    since the run completes; it is proved or left to its runtime check."""
    src = program(source, site)
    verified = _verify(src)
    assert not verified.errors, [d.format() for d in verified.errors]
    statuses = _statuses(verified, site.kind)
    # A user callee's discharged precondition leaves no record (its check
    # is the callee's prologue; #1480 records the undischarged ones), so
    # the E501 column asserts the absence of a refusal alone.
    assert statuses or site.kind == "call_pre", site.kind
    assert "violated" not in statuses, (site.kind, statuses)
    ran = _run(src, source.run_fn, list(source.run_args))
    assert ran.ok, f"the run trapped: {ran.trap}"


# =====================================================================
# The proof direction: a run that traps proves nothing
# =====================================================================

_U2 = """\
type U2 = { @Int | int_to_float(@Int.0) >= 0.0 };
"""

#: Each source, producing 0 instead of 5, under the division: the run traps,
#: so the `div_zero` row is never `verified`.
REFUTING: tuple[Source, ...] = (
    Source("s01_unstatable_parameter", "@U2.0", decls=_U2, params="@U2", run_args=(0,)),
    Source("s02_unstatable_return", "mk(0)", decls=_U2 + """\

private fn mk(@Int -> @U2)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""),
    Source("s03_unstatable_type_argument", "@U2.0", decls=_U2 + """\

private fn mk2(@Int -> @Option<U2>)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""", wrap=lambda body, neutral: _in_some_arm(body, neutral).replace(
        "mk2(5)", "mk2(0)").replace("Some(@U)", "Some(@U2)")),
    Source("s04_untranslatable_let", "@Int.0",
           prefix="let @Int = apply_fn(fn(@Unit -> @Int) effects(pure) { 0 }, ());\n"),
    Source("s05_untranslatable_condition", "@Int.0",
           prefix="let @Int = if apply_fn(fn(@Unit -> @Bool) effects(pure) { true }, ()) "
                  "then { 0 } else { 5 };\n"),
    Source("s06_untranslatable_argument", "zero(pick(true, 1, 2))", decls=_PICK + """\

private fn zero(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""),
    Source("s07_untranslatable_scrutinee", "@Int.0",
           prefix='let @Map<String, Int> = map_insert(map_new(), "a", 2);\n'
                  'let @Int = match map_get(@Map<String, Int>.0, "a") {\n'
                  "  Some(@Int) -> 0,\n"
                  "  None -> 5\n"
                  "};\n"),
    Source("s08_literal_element", "@Int.0", decls=_PICK,
           prefix="let @Array<Int> = [pick(true, 1, 1)];\n"
                  "let @Int = nat_to_int(array_length(@Array<Int>.0)) - 1;\n"),
    Source("s09_state_read", "nat_to_int(@Nat.0)", params="@Unit",
           effects="<State<Nat>>", prefix="let @Nat = get(());\n",
           main=_STATE_MAIN.replace("(@Nat = 4)", "(@Nat = 0)"),
           run_fn="main"),
    Source("s10_handler_value",
           "handle[State<Nat>](@Nat = 0) {\n"
           "    get(@Unit) -> { resume(@Nat.0) },\n"
           "    put(@Nat) -> { resume(()) }\n"
           "  } in {\n"
           "    nat_to_int(get(()))\n"
           "  }"),
    Source("s11_fold",
           "array_fold([0, 0], 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })"),
    Source("s12_set_size", "nat_to_int(set_size(set_new()))"),
    Source("s13_generic_call", "@Int.0", decls=_PICK,
           prefix="let @Int = pick(true, 0, 0);\n"),
    Source("s14_call_read_twice", "@Int.0", decls="""\
private fn ext(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
""", prefix="let @Int = ext(0);\n"),
)

_DIVISION = SITES[5]
assert _DIVISION.code == "E526"


@pytest.mark.parametrize("source", REFUTING, ids=lambda s: s.id)
def test_a_run_that_traps_proves_nothing(source: Source) -> None:
    """The proof direction: a division the run refutes is never `verified`,
    whatever the stand-in's model value happens to be."""
    src = program(source, _DIVISION)
    verified = _verify(src)
    statuses = _statuses(verified, "div_zero")
    assert statuses and "verified" not in statuses, statuses
    ran = _run(src, source.run_fn, list(source.run_args))
    assert not ran.ok, "the run completed where a division by zero was due"


# =====================================================================
# #1470's permutation row, and the spelling row
# =====================================================================

@pytest.mark.parametrize("source", SOURCES, ids=lambda s: s.id)
def test_an_unrelated_let_changes_no_verdict(source: Source) -> None:
    """#1470's row: an unrelated `let` of an arbitrary type before the
    obligation reads what the obligation read without it."""
    plain = _verify(program(source, _DIVISION))
    permuted = _verify(program(
        source, _DIVISION, prelude="let @Option<Int> = Some(1);\n"))
    assert _statuses(permuted, "div_zero") == _statuses(plain, "div_zero")
    assert _codes(permuted) == _codes(plain)


_DBL = """\
private fn dbl(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0 + @Nat.0)
  effects(pure)
{
  @Nat.0 + @Nat.0
}

public fn f(@Unit -> @Int)
  requires(true)
  ensures(@Int.result != 1)
  effects(<State<Nat>>)
{
  let @Nat = %s;
  nat_to_int(dbl(@Nat.0))
}
"""

M05_QUALIFIED = _DBL % "State.get(())"
M05_BARE = _DBL % "get(())"


def test_repro_m05_the_two_spellings_of_a_state_read_give_one_verdict() -> None:
    """m05 and m05b: a `State<Nat>` read carries `>= 0` whether spelled
    `State.get(())` or `get(())` (the latter is what 41 of 42 corpus files
    use), so `dbl`'s `ensures` is assumed and `f`'s proves."""
    qualified = _verify(M05_QUALIFIED)
    bare = _verify(M05_BARE)
    assert _ensures_status(qualified, "f") == _ensures_status(bare, "f")
    assert _ensures_status(qualified, "f") == "verified", _codes(qualified)
    assert not qualified.errors and not bare.errors


# =====================================================================
# The issue's lines, pinned
# =====================================================================

M01 = """\
type U = { @Int | int_to_float(@Int.0) > 0.0 && @Int.0 > 0 };

public fn use_it(@U -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  100 / @U.0
}
"""


def test_repro_m01_1470_an_unstatable_refinement_states_its_translatable_conjunct() -> None:
    """#1470 at a parameter: `U`'s second conjunct forbids 0, and its first
    calls `int_to_float`, outside the fragment; the division proves from the
    conjunct that translates.  The run gives 25."""
    verified = _verify(M01)
    assert not verified.errors, _codes(verified)
    assert _statuses(verified, "div_zero") == ["verified"]
    assert _run(M01, "use_it", [4]).value == 25


M01_RETURN = """\
type U = { @Int | int_to_float(@Int.0) > 0.0 && @Int.0 > 0 };

private fn mk(@Int -> @U)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn use_it(@Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  100 / mk(@Int.0)
}
"""

M01_TYPE_ARG = """\
type U = { @Int | int_to_float(@Int.0) > 0.0 && @Int.0 > 0 };

private fn mk(@Int -> @Option<U>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn use_it(@Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@U) -> 100 / @U.0,
    None -> 0
  }
}
"""


@pytest.mark.parametrize("src", [M01_RETURN, M01_TYPE_ARG], ids=["return", "type argument"])
def test_repro_m01_1470_at_a_refined_return_and_a_type_argument(src: str) -> None:
    """#1470's other two positions: the value is a call's result of `U`, or
    the payload of one; neither supplies a zero the type forbids."""
    verified = _verify(src)
    assert "E526" not in _codes(verified), _codes(verified)
    assert "violated" not in _statuses(verified, "div_zero")
    assert _run(src, "use_it", [4]).value == 25


M01B = """\
public fn g(@Int -> @Nat)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  let @Int = apply_fn(fn(@Unit -> @Int) effects(pure) { 5 }, ());
  let @Nat = @Int.0;
  @Nat.0
}
"""


def test_repro_m01b_1470_a_narrowing_of_an_untranslatable_let_is_a_runtime_check() -> None:
    """#1470's 2026-09-24 comment: `apply_fn` states nothing about the
    value, so the `@Nat` narrowing is Tier 3 behind its guard, never E503.
    The run gives 5."""
    verified = _verify(M01B)
    assert not verified.errors, _codes(verified)
    assert _statuses(verified, "nat_bind") == ["tier3"]
    assert _run(M01B, "g", [3]).value == 5


_CHECK_POS = """\
private fn check_pos(@Int -> @Int)
  requires(true)
  ensures(@Int.0 > 0)
  effects(pure)
{
  apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 }, @Int.0)
}
"""

M02 = _CHECK_POS + """
public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = if apply_fn(fn(@Int -> @Bool) effects(pure) { @Int.0 > 100 }, @Int.0) then {
    check_pos(@Int.0)
  } else {
    0
  };
  @Int.1
}
"""


def test_repro_m02_1571_a_callees_ensures_holds_only_under_the_condition() -> None:
    """#1571: the `if` condition does not translate; `check_pos`'s claim
    about its argument is assumed only under the condition's stand-in, so
    `f`'s `ensures` is not proved: the refutation escapes the claim by
    choosing the stand-in false, and rests on it.  The run with -3 fails
    it.  `check_pos`'s own `ensures`, a claim about its parameter no body
    can make true, is refuted as it is."""
    verified = _verify(M02)
    assert _ensures_status(verified, "f") == "tier3", _codes(verified)
    assert _ensures_status(verified, "check_pos") == "violated"
    ran = _run(M02, "f", [-3])
    assert not ran.ok and "Postcondition" in str(ran.trap)


M02B = _CHECK_POS + """
public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  match @Bool.0 {
    true -> @Int.0,
    true -> check_pos(@Int.0),
    false -> 1
  }
}
"""


def test_repro_m02b_1571_an_arm_runs_under_the_earlier_arms_negation() -> None:
    """#1571's twin: the second arm is shadowed by the first, so its call's
    `ensures` holds nowhere; `f`'s `ensures` is not proved, and the run with
    `true -3` fails it."""
    verified = _verify(M02B)
    assert _ensures_status(verified, "f") != "verified"
    ran = _run(M02B, "f", [1, -3])
    assert not ran.ok and "Postcondition" in str(ran.trap)


_RUN_LOOP = """\
private fn step(@%(t)s -> @%(t)s)
  requires(true)
  ensures(true)
  effects(pure)
{
  @%(t)s.0
}

public fn run_loop(@%(t)s, @Nat, @Nat -> @Int)
  requires(@Nat.1 <= @Nat.0)
  ensures(true)
  decreases(@Nat.0 - @Nat.1)
  effects(pure)
{
  if @Nat.1 < @Nat.0 then {
    %(call)s
  } else {
    0
  }
}
"""

M03_INLINE = _RUN_LOOP % {
    "t": "Array<Array<Bool>>",
    "call": "run_loop(step(@Array<Array<Bool>>.0), @Nat.1 + 1, @Nat.0)"}
M03_LET = _RUN_LOOP % {
    "t": "Array<Array<Bool>>",
    "call": "let @Array<Array<Bool>> = step(@Array<Array<Bool>>.0);\n"
            "    run_loop(@Array<Array<Bool>>.0, @Nat.1 + 1, @Nat.0)"}


def test_repro_m03_1595_a_call_with_a_stand_in_argument_keeps_its_proofs() -> None:
    """#1595: `step` returns an `Array<Array<Bool>>`, a type the solver had
    no sort for, so the recursive call with it inline lost its `decreases`
    and precondition proofs; the two spellings now give one verdict."""
    inline = _verify(M03_INLINE)
    let = _verify(M03_LET)
    assert _statuses(inline, "decreases") == _statuses(let, "decreases") == ["verified"]
    assert "E532" not in _warning_codes(inline), _warning_codes(inline)
    assert "E525" not in _warning_codes(inline), _warning_codes(inline)
    assert _statuses(inline, "call_pre") == _statuses(let, "call_pre")


M04 = """\
public fn f(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2];
  let @Nat = @Array<Int>.0[@Nat.0];
  @Nat.0
}
"""


@pytest.mark.xfail(strict=True, reason=(
    "#1696's m04 rests on the obligation table's post-fact rule (#1695): "
    "an index the bounds check guards is in bounds for the rest of its "
    "scope, so the element is one of the literal's."))
def test_repro_m04_an_indexed_element_narrowed_into_nat_is_not_refused() -> None:
    verified = _verify(M04)
    assert "E503" not in _codes(verified), _codes(verified)


M06 = """\
public fn f(@Array<Nat> -> @Int)
  requires(array_length(@Array<Nat>.0) > 0)
  ensures(@Int.result >= 0)
  effects(pure)
{
  nat_to_int(@Array<Nat>.0[0])
}
"""


@pytest.mark.xfail(strict=True, reason=(
    "#1696's m06 is a composite fact (#1814): an `Array<Nat>` element's "
    "`>= 0` is assumed only once every producer of a composite is a row."))
def test_repro_m06_an_array_nat_element_carries_its_sign() -> None:
    verified = _verify(M06)
    assert _ensures_status(verified, "f") == "verified", _codes(verified)


M07 = """\
private fn external_library_call(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 * 2 + 1
}

public fn trusted(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = external_library_call(@Int.0);
  assume(@Int.0 > 0);
  @Int.0
}
"""


def test_repro_m07_1601_an_assume_over_a_let_bound_call_reaches_the_ensures() -> None:
    """#1601: every pass reads one term for the call, so the `assume`
    constrains the value the `ensures` reads; the assumption is counted."""
    verified = _verify(M07)
    assert not verified.errors, _codes(verified)
    assert _ensures_status(verified, "trusted") == "verified"
    assert "W003" in _warning_codes(verified)


M08 = """\
public fn f(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  handle[State<Nat>](@Nat = 3) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    put(4);
    nat_to_int(get(()))
  }
}
"""


def test_repro_m08_a_state_nat_cells_read_under_its_handler_carries_its_sign() -> None:
    """The 2026-10-22 line: the handler's every clause resumes once in tail
    position, so the handle has its body's value, and the cell's read is a
    `Nat`."""
    verified = _verify(M08)
    assert _ensures_status(verified, "f") == "verified", _warning_codes(verified)
    assert _run(M08, "f", [1]).value == 4


M08_NON_CANONICAL = """\
public fn f(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { 0 - 1 }
  } in {
    if @Bool.0 then { throw(1) } else { 5 }
  }
}
"""


def test_repro_m08_a_handler_that_does_not_resume_has_the_clauses_value() -> None:
    """The negative space of the handle rule: a clause that does not resume
    gives the handle the clause's value, so `f`'s false `ensures` is never
    proved; the run with `true` fails it."""
    verified = _verify(M08_NON_CANONICAL)
    assert _ensures_status(verified, "f") != "verified"
    ran = _run(M08_NON_CANONICAL, "f", [1])
    assert not ran.ok and "Postcondition" in str(ran.trap)


M09 = _PICK + """
private fn need(@Nat -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

public fn f(@Bool, @Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [pick(@Bool.0, @Int.0, @Int.0), 2];
  let @Int = nat_to_int(array_length(@Array<Int>.0));
  need(@Int.0)
}
"""


def test_repro_m09_a_literal_with_a_stand_in_element_keeps_its_length() -> None:
    """The 2026-10-22 line: the literal's length is 2 whatever `pick`
    returns, so the narrowing into `need`'s `@Nat` proves."""
    verified = _verify(M09)
    assert not verified.errors, _codes(verified)
    assert "violated" not in _statuses(verified, "nat_bind")
    assert _statuses(verified, "nat_bind")[-1] == "verified"


M10 = """\
private data Tally {
  Amber(Bool),
  Basalt
}

public fn in_place(@Bool -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = match Basalt {
    Amber(@Bool) -> 1,
    Basalt -> 1
  };
  let @Nat = @Int.0;
  @Nat.0
}
"""


def test_repro_m10_a_match_on_a_constructor_applied_in_place_stays_proved() -> None:
    """Regression cell: the line did not reproduce at the v0.2.6 cut (the
    typed program's construction sorts), and stays proved."""
    verified = _verify(M10)
    assert not verified.errors, _codes(verified)
    assert _statuses(verified, "nat_bind") == ["verified"]


M11 = """\
type Span = { @Int | @Int.0 >= 1 && @Int.0 <= 28 };
""" + _PICK + """
private fn need(@Span -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

private fn two(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 2)
  effects(pure)
{
  2
}

public fn generic_at_int(@Bool -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = two(pick(@Bool.0, 1, 2));
  need(@Nat.0)
}
"""


def test_repro_m11_a_call_with_a_stand_in_argument_keeps_its_ensures() -> None:
    """The 2026-10-22 line: `two`'s argument does not translate, and its
    `ensures(@Int.result == 2)` is still assumed, so `need`'s refinement
    proves."""
    verified = _verify(M11)
    assert not verified.errors, _codes(verified)
    assert _statuses(verified, "refine_bind") == ["verified"]


M12 = """\
private fn need(@Int -> @Int)
  requires(@Int.0 >= -6 && @Int.0 <= 22)
  ensures(true)
  effects(pure)
{
  @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "a", 2);
  let @Nat = match map_get(@Map<String, Int>.0, "a") {
    Some(@Int) -> 2,
    None -> 2
  };
  need(@Nat.0)
}
"""


def test_repro_m12_a_match_on_a_stand_in_scrutinee_has_its_arms_value() -> None:
    """The 2026-10-22 line: `map_get`'s result is a stand-in of its type,
    the arms both yield 2, and `need`'s precondition proves."""
    verified = _verify(M12)
    assert not verified.errors, _codes(verified)
    # A discharged user precondition leaves no record (its check is the
    # callee's prologue), so the proof shows as the absence of the E532
    # demotion and of the E501 refusal.
    assert "E532" not in _warning_codes(verified), _warning_codes(verified)
    assert _statuses(verified, "call_pre") == []


M13 = """\
type Span = { @Int | @Int.0 >= -14 && @Int.0 <= 15 };
type Score = Int;

private fn f2(@Span -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn g(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Score = if false then {
    let @Map<String, Int> = map_insert(map_insert(map_new(), "a", -2), "c", 4);
    7
  } else {
    9
  };
  f2(@Score.0)
}
"""


def test_repro_m13_a_branch_let_the_verifier_cannot_translate_keeps_the_branchs_value() -> None:
    """The 2026-10-26 line: the `Map` bound inside the branch is a stand-in
    and the branch's value is 7, so the refinement at `f2` proves."""
    verified = _verify(M13)
    assert not verified.errors, _codes(verified)
    assert _statuses(verified, "refine_bind") == ["verified"]


M14 = """\
type NEI = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private fn hd(@Array<Int> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Int>.0[0]
}

public fn f(@NEI -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  hd(@NEI.0)
}
"""


def test_repro_m14_a_refined_parameter_over_an_array_base_states_its_predicate() -> None:
    """The 2026-10-28 line: the parameter's refinement is `hd`'s `requires`
    word for word, and it is stated whatever the base."""
    verified = _verify(M14)
    assert not verified.errors, _codes(verified)
    assert "E532" not in _warning_codes(verified), _warning_codes(verified)
    assert _statuses(verified, "call_pre") == []


M15 = """\
type Span = { @Int | @Int.0 >= -2 && @Int.0 <= 19 };

public fn f3(-> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Span = if -4 <= -3 then {
    let @Map<String, Int> = map_insert(map_new(), "b", 3);
    5 * 3
  } else {
    8 + 7
  };
  handle[State<Nat>](@Nat = @Span.0 + -6) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    true
  }
}
"""


def test_repro_m15_an_if_whose_branch_binds_a_map_keeps_its_value() -> None:
    """The 2026-11-02 line (seed 2900205): the `if`'s value is 15 whatever
    the branch's `Map` is, so the narrowing of `@Span.0 + -6` proves, as the
    twin without the inner `let` does."""
    verified = _verify(M15)
    assert not verified.errors, _codes(verified)
    assert _statuses(verified, "nat_bind") == ["verified"]
    assert _statuses(verified, "refine_bind") == ["verified"]


# =====================================================================
# The rule's own bounds
# =====================================================================

RECURSIVE_BRANCH = _CHECK_POS + """
public fn f(@Int, @Nat -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Int.0
  } else {
    let @Int = check_pos(@Int.0);
    f(@Int.1, @Nat.0 - 1)
  }
}
"""


def test_a_callees_claim_in_a_recursive_branch_stays_in_its_branch() -> None:
    """One term per call node does not let the measure walk's read of the
    recursive branch assume `check_pos`'s claim about `@Int.0` outside it:
    `f`'s `ensures` is refuted (the run with `-3 0` fails it)."""
    verified = _verify(RECURSIVE_BRANCH)
    assert _ensures_status(verified, "f") == "violated", _codes(verified)
    ran = _run(RECURSIVE_BRANCH, "f", [-3, 0])
    assert not ran.ok and "Postcondition" in str(ran.trap)


GENUINE_VIOLATION_OVER_A_STAND_IN = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @Int = apply_fn(fn(@Unit -> @Int) effects(pure) { 5 }, ());
  @Int.0 - @Int.0 - 1
}
"""


def test_a_goal_false_for_every_value_of_the_stand_in_is_a_violation() -> None:
    """R4's bound: `x - x - 1 > 0` is false whatever `x` is, so the
    `ensures` is refused, not left to a runtime check."""
    verified = _verify(GENUINE_VIOLATION_OVER_A_STAND_IN)
    assert _ensures_status(verified, "f") == "violated"
    assert "E500" in _codes(verified)


PRECONDITION_FALSE_FOR_EVERY_VALUE = """\
private fn inv(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  100 / @Int.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = apply_fn(fn(@Unit -> @Int) effects(pure) { 5 }, ());
  inv(@Int.0 - @Int.0)
}
"""


def test_a_precondition_false_for_every_value_of_the_stand_in_is_refused() -> None:
    """R4 at a call: `0 > 0` is false for every value the stand-in takes, so
    the call is E501; a precondition some value satisfies is E532 (the
    matrix's E501 column)."""
    verified = _verify(PRECONDITION_FALSE_FOR_EVERY_VALUE)
    assert _statuses(verified, "call_pre") == ["violated"]
    assert "E501" in _codes(verified)


STAND_IN_RETURN = """
type Pos = { @Int | @Int.0 > 0 };

public fn f(@Unit -> @Pos)
  requires(true)
  ensures(true)
  effects(<Random>)
{
  Random.random_int(1, 9)
}
"""


def test_repro_an_unknown_over_a_stand_in_reads_as_the_stand_in(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """A refutation that rests on a stand-in is undecided whatever the
    solver answers short of a proof (R4), so an `unknown` — a query that
    ran out of its budget — reports the stand-in's reason, not the
    clock's: `examples/maximum_syntax.vera`'s floating-point queries over
    `int_to_float`'s stand-in take seconds, and a loaded runner timed one
    of two identical runs out, so the two disagreed on the rationale."""
    def stand_in_reason(verified: pipeline.Verified) -> list[str]:
        return [d.rationale for d in verified.result.diagnostics
                if d.error_code == "E506"]

    real = stand_in_reason(_verify(STAND_IN_RETURN))
    assert len(real) == 1 and "opaque stand-in" in real[0], real
    import z3
    monkeypatch.setattr(z3.Solver, "check", lambda self, *a: z3.unknown)
    assert stand_in_reason(_verify(STAND_IN_RETURN)) == real
