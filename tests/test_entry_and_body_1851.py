"""A function with a check after its body is an entry and a body (#1851).

THE MECHANISM.  A call in tail position leaves by `return_call` only where
no check runs after it (`ObligationTable.tail_calls`, #1849).  A function
whose return runs a check after its body (a non-trivial `ensures`, a
guarded refined return: the table's epilogue) therefore kept no tail call,
proved or not, and a tail-recursive loop with a postcondition used a stack
frame per step: `count_proved` exhausted the WASM call stack at 50,000
steps while its `ensures(true)` twin ran a million.

THE RULE (spec §6.2.2, §11.8.3, §5.6.1).  An `ensures` is checked where a
function returns to its caller.  A function with a check after its body
that calls itself in tail position (`ObligationTable.split`) compiles as an
entry, under the declaration's symbol and export, which calls the body once
and runs the check on what it returns, and a body (`$:<name>@body`), which
keeps its tail calls: a self call in tail position transfers to the body,
a call of another function to that function's entry.  Everything that runs
before the body (a `requires`, a refined parameter's guard, the measure)
stays in the body and runs on every hop; a self call that is not in tail
position calls the entry, so its value is checked.  Every other function
compiles as before.

THE INSTRUMENT.  The check after the body (a postcondition the verifier
proves, one it does not, a refined return type, a postcondition over
`old` and `new` state) × the loop's form (a counting loop, an accumulator
whose call is a block's tail behind a `let`, a loop that allocates on every
hop, a `where` helper, a loop reached by another function's tail call) ×
the oracle:

* deep: a million steps run to the value the `ensures(true)` twin gives;
* entry: a result that violates the check at the caller's arguments traps
  at the entry, naming the function (the proved column has no violating
  input: the verifier proved there is none);
* hop: a `requires` false at an inner hop traps there, as the twin does.

Beside it, each run on every pull request: the issue's `count_proved`
(`repro`); the decided behaviour of a hop whose own instance of the
postcondition fails inside a call whose result satisfies it; a non-tail
self call checked through the entry; mutual recursion's bound, pinned; the
measure checked at each hop of a split function; the entry rooting what
its check reads under eager collection; no body symbol in anything a user
reads; and the WAT shape (the entry holds no `return_call`, the body's self
call transfers to the body, a function that is not split compiles as one).
"""

from __future__ import annotations

import re

from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/obligations/table.py", "vera/codegen/functions.py",
    "vera/tail_position.py", "vera/wasm/calls.py"])

FILE = "entry_body.vera"
DEEP = 1_000_000
#: The precondition's bound on the accumulator: a loop from 0 past it
#: violates `requires` at the hop where the accumulator reaches it.
LIMIT = 4_000_000


# =====================================================================
# The checks after the body
# =====================================================================


@dataclass(frozen=True)
class Check:
    """A check after the loop's body: the loop's return type *ret*, its
    `ensures` clause, its effect row, the statement each hop runs before
    the call (*step*), the declarations the program needs, and the
    arguments at which the check fails at the caller (``None`` where none
    exists), with the trap's kind."""

    id: str
    ret: str = "Nat"
    ensures: str = "true"
    effect: str = "pure"
    step: str = ""
    decls: str = ""
    violate: tuple[int, int] | None = None
    #: The step that makes `violate` fail, where the check is the step's.
    bad_step: str | None = None
    kind: str = "contract_violation"
    #: The depth the loop runs to: far past the call stack's (a few tens of
    #: thousands of frames), and less for the state check, whose every hop
    #: is two host calls.
    deep: int = DEEP
    #: What the trap at `violate` says: the check's own message, never the
    #: precondition's.
    message: str = "Postcondition violation in "


_SMALL = """\
private fn small(@Nat -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0 <= 3000000
}

"""

CHECKS = (
    Check("proved", ensures="@Nat.result >= @Nat.1"),
    Check("unproved", ensures="small(@Nat.result)", decls=_SMALL,
          violate=(3_000_001, 0)),
    Check("refined", ret="Small", message="Refinement violation in ",
          decls="type Small = { @Nat | @Nat.0 <= 3000000 };\n\n",
          violate=(3_000_001, 0)),
    Check("state",
          ensures="new(State<Int>) == old(State<Int>) + nat_to_int(@Nat.0)",
          effect="<State<Int>>",
          step="let @Int = get(());\nput(@Int.0 + 1);\n",
          violate=(0, 3), deep=200_000, bad_step="let @Int = get(());\nput(@Int.0 + 2);\n"),
)

FORMS = ("counting", "accumulator", "allocating", "where", "reached")


# =====================================================================
# The programs
# =====================================================================


def _indent(text: str, by: str = "  ") -> str:
    return "\n".join(by + ln if ln else ln for ln in text.splitlines())


_LST = """\
private data Lst {
  Nil,
  Cons(Nat, Lst)
}

"""


def _loop(check: Check, form: str, *, twin: bool, bad: bool,
          name: str = "loop") -> str:
    """The loop: `name(acc, n)`, a `Lst` before them in the allocating
    form, counting `n` down and `acc` up, under *check* (``ensures(true)``
    and a plain `Nat` return in the *twin*)."""
    lst = "@Lst, " if form == "allocating" else ""
    ret = "Nat" if twin else check.ret
    ensures = "true" if twin else check.ensures
    step = check.bad_step if bad and check.bad_step else check.step
    cons = "Cons(@Nat.0, @Lst.0), " if form == "allocating" else ""
    if form == "accumulator":
        call = (f"let @Nat = @Nat.0 - 1;\n"
                f"{name}({cons}@Nat.2 + 1, @Nat.0)")
    else:
        call = f"{name}({cons}@Nat.1 + 1, @Nat.0 - 1)"
    hop = _indent(step + call, "    ")
    return (f"fn {name}({lst}@Nat, @Nat -> @{ret})\n"
            f"  requires(@Nat.1 <= {LIMIT})\n"
            f"  ensures({ensures})\n"
            f"  decreases(@Nat.0)\n"
            f"  effects({check.effect})\n"
            "{\n"
            "  if @Nat.0 == 0 then {\n"
            "    @Nat.1\n"
            "  } else {\n"
            f"{hop}\n"
            "  }\n"
            "}\n")


def program(check: Check, form: str, *, twin: bool = False,
            bad: bool = False) -> str:
    """The program: *check*'s declarations, the loop in *form*, and
    `go(acc, n)`, which runs it and returns its value as a `Nat`."""
    ret = "Nat" if twin else check.ret
    nil = "Nil, " if form == "allocating" else ""
    decls = check.decls + (_LST if form == "allocating" else "")
    loop = _loop(check, form, twin=twin, bad=bad)
    go_head = (f"public fn go(@Nat, @Nat -> @Nat)\n"
               "  requires(true)\n  ensures(true)\n"
               f"  effects({check.effect})\n")
    if form == "where":
        return (decls + go_head + "{\n"
                f"  let @{ret} = loop({nil}@Nat.1, @Nat.0);\n"
                f"  @{ret}.0\n}}\nwhere {{\n" + _indent(loop) + "\n}\n")
    if form == "reached" and ret == "Nat":
        body = f"  loop({nil}@Nat.1, @Nat.0)\n"
    else:
        body = (f"  let @{ret} = loop({nil}@Nat.1, @Nat.0);\n"
                f"  @{ret}.0\n")
    return decls + "private " + loop + "\n" + go_head + "{\n" + body + "}\n"


def _run(source: str, args: list[int]) -> pipeline.Ran:
    ran = pipeline.run(source, "go", args, file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, [
        (d.error_code, d.description[:120]) for d in ran.compiled.errors
    ] if ran.compiled is not None else "no compile"
    return ran


def _outcome(source: str, args: list[int]) -> tuple[str, object]:
    ran = _run(source, args)
    if ran.trap is not None:
        return ("trap", ran.trap.kind)
    return ("value", ran.value)


CELLS = [(c, f) for c in CHECKS for f in FORMS]
IDS = [f"{c.id}-{f}" for c, f in CELLS]


@pytest.mark.parametrize(("check", "form"), CELLS, ids=IDS)
def test_a_million_steps_run_to_the_twins_value(check: Check, form: str) -> None:
    source = program(check, form)
    compiled = pipeline.compile(source, file=FILE)
    assert compiled.ok
    assert re.search(r"return_call \$:\S*loop@body\b", compiled.wat)
    assert _outcome(source, [0, check.deep]) == ("value", check.deep)
    assert _outcome(program(check, form, twin=True), [0, check.deep]) == (
        "value", check.deep)


VIOLATING = [(c, f) for c, f in CELLS if c.violate is not None]


@pytest.mark.parametrize(
    ("check", "form"), VIOLATING,
    ids=[f"{c.id}-{f}" for c, f in VIOLATING])
def test_a_violation_at_the_callers_arguments_traps_at_the_entry(
    check: Check, form: str,
) -> None:
    assert check.violate is not None
    ran = _run(program(check, form, bad=True), list(check.violate))
    assert ran.trap is not None
    assert ran.trap.kind == check.kind
    assert check.message in str(ran.trap), str(ran.trap)
    assert "loop" in str(ran.trap)
    assert "@body" not in str(ran.trap)
    # The trap fires in the entry, which the backtrace names once: the
    # body's frame and its entry's are one function's.
    names = [f.func for f in ran.trap.frames if not f.is_builtin]
    assert names[0].endswith("loop") and names.count(names[0]) == 1, names


@pytest.mark.parametrize(("check", "form"), CELLS, ids=IDS)
def test_a_precondition_false_at_an_inner_hop_traps_there(
    check: Check, form: str,
) -> None:
    """The call starts five below `LIMIT` and `acc` passes it at the sixth
    hop: that hop's `requires` traps, in the split function as in its
    twin.  Starting near the bound keeps the run to a few hops: the trap
    is at an inner hop all the same."""
    args = [LIMIT - 5, 10]
    got = _outcome(program(check, form), args)
    assert got == ("trap", "contract_violation")
    assert got == _outcome(program(check, form, twin=True), args)
    ran = _run(program(check, form), args)
    assert ran.trap is not None and "Precondition violation" in str(ran.trap)


# =====================================================================
# The issue's program, and the decided behaviour
# =====================================================================


_ISSUE = """\
public fn count_plain(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    count_plain(@Nat.1 + 1, @Nat.0 - 1)
  }
}

public fn count_proved(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    count_proved(@Nat.1 + 1, @Nat.0 - 1)
  }
}
"""


def test_repro_count_proved_runs_a_million_steps() -> None:
    """The issue's program: both `ensures` verify, and the proved one runs
    as deep as the plain one (at base it exhausted the stack at 50,000)."""
    verified = pipeline.verify(_ISSUE, file=FILE)
    assert verified.ok
    for fn in ("count_plain", "count_proved"):
        assert pipeline.run(_ISSUE, fn, [0, DEEP], file=FILE).value == DEEP


_HOP = """\
public fn hop(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.1 == 0 || @Nat.result == 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    hop(@Nat.1 + 1, @Nat.0 - 1)
  }
}
"""


def test_repro_a_hops_own_postcondition_is_not_checked_inside_the_loop() -> None:
    """The decided behaviour: `hop(0, 5)` returns 5, which satisfies the
    postcondition at the caller's arguments (`@Nat.1 == 0`).  The hop
    `hop(1, 4)` inside it returns 5 too, which its own instance does not
    allow; the check runs where the function returns to its caller, so
    that hop is not checked.  A direct call at the hop's arguments is."""
    assert pipeline.run(_HOP, "hop", [0, 5], file=FILE).value == 5
    direct = pipeline.run(_HOP, "hop", [1, 4], file=FILE)
    assert direct.trap is not None
    assert direct.trap.kind == "contract_violation"
    assert "Postcondition violation in hop" in str(direct.trap)


_NON_TAIL = """\
public fn depth(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    depth(@Nat.0 - 1) + 1
  }
}

public fn twisted(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    if @Nat.0 == 3 then {
      twisted(@Nat.0 - 1)
    } else {
      twisted(@Nat.0 - 1) + 1
    }
  }
}
"""


def test_repro_a_self_call_not_in_tail_position_calls_the_entry() -> None:
    """`depth` calls itself only outside tail position: it is not split,
    and compiles as one function.  `twisted` has both: its tail call
    transfers to the body, its other self call calls the entry, whose
    check catches the wrong answer of the inner call at 3 (it returns 2)
    before any caller sees it."""
    compiled = pipeline.compile(_NON_TAIL, file=FILE)
    assert compiled.ok
    assert "$:depth@body" not in compiled.wat
    assert "return_call $:twisted@body" in compiled.wat
    assert "call $:twisted\n" in compiled.wat + "\n"
    assert pipeline.run(_NON_TAIL, "depth", [1000], file=FILE).value == 1000
    ran = pipeline.run(_NON_TAIL, "twisted", [5], file=FILE)
    assert ran.trap is not None and ran.trap.kind == "contract_violation"
    assert "Postcondition violation in twisted" in str(ran.trap)


_MUTUAL = """\
public fn ping(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    pong(@Nat.1 + 1, @Nat.0 - 1)
  }
}

public fn pong(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    ping(@Nat.1 + 1, @Nat.0 - 1)
  }
}
"""


def test_repro_mutual_recursion_stays_bounded_by_the_call_stack() -> None:
    """Unchanged, pinned: neither function calls itself, so neither is
    split; the pair runs 10,000 steps and exhausts the stack at 20,000."""
    compiled = pipeline.compile(_MUTUAL, file=FILE)
    assert "@body" not in compiled.wat and "return_call" not in compiled.wat
    assert pipeline.run(_MUTUAL, "ping", [0, 10_000], file=FILE).value == 10_000
    deep = pipeline.run(_MUTUAL, "ping", [0, 20_000], file=FILE)
    assert deep.trap is not None and deep.trap.kind == "stack_exhausted"


_MEASURE = """\
public fn stuck(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result >= @Nat.1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    stuck(@Nat.1 + 1, @Nat.0)
  }
}
"""


def test_repro_the_measure_is_checked_at_each_hop_of_a_split_function() -> None:
    """The measure is checked at the self call, before the transfer: a hop
    that does not decrease it traps there, where without the check the
    loop would never end."""
    compiled = pipeline.compile(_MEASURE, file=FILE)
    assert "return_call $:stuck@body" in compiled.wat
    ran = pipeline.run(_MEASURE, "stuck", [0, 3], file=FILE)
    assert ran.trap is not None and ran.trap.kind == "contract_violation"
    assert "decreases() measure in 'stuck'" in str(ran.trap)


# =====================================================================
# A generic function's clone (a line of #1525)
# =====================================================================


def _generic(ensures: str, step: str = "@Nat.0 - 1") -> str:
    return f"""\
public forall<T> fn gcount(@T, @Nat, @Nat -> @Nat)
  requires(true)
  ensures({ensures})
  decreases(@Nat.0)
  effects(pure)
{{
  if @Nat.0 == 0 then {{
    @Nat.1
  }} else {{
    gcount(@T.0, @Nat.1 + 1, {step})
  }}
}}

public fn run_bool(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  gcount(true, 0, @Nat.0)
}}

public fn run_int(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  gcount(7, 0, @Nat.0)
}}
"""


@pytest.mark.parametrize("ensures", ["true", "@Nat.result >= @Nat.1"],
                         ids=["ensures-true", "ensures-real"])
@pytest.mark.parametrize("fn", ["run_bool", "run_int"])
def test_repro_a_generic_clones_self_tail_call_transfers(
    ensures: str, fn: str,
) -> None:
    """A clone's self call still names the generic (`gcount`), and the one
    predicate resolves it through the typed program to the clone
    (`gcount$Bool`, `gcount$Int`): the measure is checked at the call and
    the call transfers, to the clone itself or, with a real postcondition,
    to the clone's body.  At base the call was a plain call and the loop
    exhausted the stack at a million steps."""
    source = _generic(ensures)
    compiled = pipeline.compile(source, file=FILE)
    clone = "gcount$Bool" if fn == "run_bool" else "gcount$Int"
    target = f"{clone}@body" if ensures != "true" else clone
    assert f"return_call $:{target}\n" in compiled.wat
    assert pipeline.run(source, fn, [DEEP], file=FILE).value == DEEP


def test_repro_a_generic_clones_measure_is_checked_at_each_hop() -> None:
    ran = pipeline.run(_generic("@Nat.result >= @Nat.1", "@Nat.0"),
                       "run_int", [3], file=FILE)
    assert ran.trap is not None and ran.trap.kind == "contract_violation"
    assert "decreases() measure in 'gcount$Int'" in str(ran.trap)


# =====================================================================
# The collector, the names, the shape
# =====================================================================


_ROOTS = """\
private data Lst {
  Nil,
  Cons(Nat, Lst)
}

private fn keep(@String, @Array<Nat>, @Lst, @Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.1 + @Nat.0
    && string_contains(string_concat(@String.0, "!"), "hello!")
    && @Array<Nat>.0[2] == 3)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    keep(@String.0, @Array<Nat>.0, Cons(@Nat.0, @Lst.0), @Nat.1 + 1, @Nat.0 - 1)
  }
}

public fn go(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  keep(string_concat("hel", "lo"), [1, 2, 3], Nil, 0, @Nat.0)
}
"""


@pytest.mark.parametrize("eager", [False, True], ids=["lazy", "eager"])
def test_repro_the_entry_roots_what_its_check_reads(
    eager: bool, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A loop that allocates on every hop, with a `String` and an `Array`
    parameter its postcondition reads after the body returns, and
    allocates while it reads them: the same answer with a collection at
    every allocation as without."""
    if eager:
        monkeypatch.setenv("VERA_EAGER_GC", "1")
    else:
        monkeypatch.delenv("VERA_EAGER_GC", raising=False)
    compiled = pipeline.compile(_ROOTS, file=FILE)
    assert "return_call $:keep@body" in compiled.wat
    ran = pipeline.run(compiled, "go", [2000])
    assert ran.trap is None, str(ran.trap)
    assert ran.value == 2000


_NAMED = """\
public fn walk(@Nat, @Nat -> @Nat)
  requires(@Nat.1 < 100)
  ensures(@Nat.result == @Nat.1)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    walk(@Nat.1 + 1, @Nat.0 - 1)
  }
}
"""


@pytest.mark.parametrize(
    ("args", "head"),
    [([0, 200], "Precondition violation in walk"),
     ([0, 3], "Postcondition violation in walk")],
    ids=["requires-at-inner-hop", "ensures-at-entry"])
def test_repro_no_user_reads_the_body_symbol(
    args: list[int], head: str, tmp_path: Path,
) -> None:
    """A trap in the body (a `requires` at an inner hop) and a trap in the
    entry (the postcondition): the text, the `--json` envelope and the
    backtrace name `walk`, once, and never its body's symbol."""
    ran = pipeline.run(_NAMED, "walk", args, file=FILE)
    assert ran.trap is not None
    text = str(ran.trap)
    assert head in text and "@body" not in text
    assert "@body" not in repr(ran.envelope())
    frames = [f.func for f in ran.trap.frames]
    assert frames == ["walk"], frames
    path = tmp_path / FILE
    path.write_text(_NAMED, encoding="utf-8")
    for argv in (["run", path, "--fn", "walk", "--", *map(str, args)],
                 ["run", "--json", path, "--fn", "walk", "--",
                  *map(str, args)]):
        out = pipeline.cli(*argv)
        assert out.returncode != 0
        assert "@body" not in out.stdout + out.stderr
        assert "walk" in out.stdout + out.stderr


def test_repro_vera_test_reports_the_declared_name(tmp_path: Path) -> None:
    path = tmp_path / FILE
    path.write_text(_NAMED, encoding="utf-8")
    for argv in (["test", "--trials", "5", path],
                 ["test", "--json", "--trials", "5", path],
                 ["test", "--distrust", "--trials", "5", path]):
        out = pipeline.cli(*argv)
        assert "@body" not in out.stdout + out.stderr
        assert "walk" in out.stdout


def _functions(wat: str) -> dict[str, str]:
    out: dict[str, str] = {}
    name = None
    for line in wat.splitlines():
        if line.startswith("  (func $"):
            name = line.split()[1]
            out[name] = ""
        elif name is not None:
            out[name] += line + "\n"
    return out


def test_the_entry_holds_no_return_call_and_the_body_transfers_to_itself() -> None:
    fns = _functions(pipeline.compile(_ISSUE, file=FILE).wat)
    assert "return_call" not in fns["$:count_proved"]
    assert "call $:count_proved@body" in fns["$:count_proved"]
    assert "return_call $:count_proved@body" in fns["$:count_proved@body"]
    # A function with no check after its body is not split.
    assert "$:count_plain@body" not in fns
    assert "return_call $:count_plain" in fns["$:count_plain"]


_WASI = """\
private fn count(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.1 + @Nat.0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    count(@Nat.1 + 1, @Nat.0 - 1)
  }
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(nat_to_string(count(0, 1000000)))
}
"""


def test_a_split_loop_runs_under_the_wasi_target(tmp_path: Path) -> None:
    """The WASI Preview 2 component carries the entry and the body as the
    core module does, and runs the loop a million steps."""
    path = tmp_path / FILE
    path.write_text(_WASI, encoding="utf-8")
    out = pipeline.cli("run", "--target", "wasi-p2", path)
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "1000000"


# =====================================================================
# --distrust reads a trap in a function that transfers to itself
# =====================================================================


_DISTRUST = """\
public fn walk(@Nat, @Nat -> @Nat)
  requires(@Nat.1 < 100)
  ensures(@Nat.result >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @Nat.1
  } else {
    walk(@Nat.1 + 1, @Nat.0 - 1)
  }
}
"""


def _attributed(args: list[int]) -> tuple[str, str]:
    """What `--distrust` makes of a trial of `walk` at *args*: the trap,
    attributed by the index `vera test` builds."""
    from vera.tester import TrialResult, _TrapIndex
    compiled = pipeline.compile(_DISTRUST, file=FILE)
    verified = pipeline.verify(_DISTRUST, file=FILE)
    index = _TrapIndex.joined(
        verified.result, compiled.result,
        program=compiled.checked.program, file=FILE, resolved_modules=[])
    ran = pipeline.run(compiled, "walk", args)
    assert ran.trap is not None
    trial = TrialResult(
        fn_name="walk", args={}, status="fail", message=str(ran.trap),
        trap_kind=ran.trap.kind,
        trap_frames=[(f.func, f.is_builtin) for f in ran.trap.frames])
    decl = next(d.decl for d in compiled.checked.program.declarations
                if getattr(d.decl, "name", None) == "walk")
    index.attribute(trial, decl)
    return trial.status, trial.attribution


def test_repro_a_precondition_trap_at_an_inner_hop_refutes_no_proof() -> None:
    """`walk(99, 3)` passes its own `requires` and fails it at the next
    hop, which the body reaches by `return_call`, so the backtrace holds
    one `walk` frame, as at the trial's own call.  The trap is the
    `requires` check's, which stands for a call the verifier did not
    prove: it must not be read as the proved postcondition's or the
    proved measure's, which would report a refutation (E703) of a proof
    that held."""
    status, attribution = _attributed([99, 3])
    assert status == "unattributed", (status, attribution)



_STRING = """\
public fn cs(@String, @Nat -> @String)
  requires(true)
  ensures(string_length(@String.result) >= 0)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    @String.0
  } else {
    cs(@String.0, @Nat.0 - 1)
  }
}
"""


def test_repro_a_string_postcondition_with_no_check_is_not_split() -> None:
    """A non-trivial `ensures` on a `String` result is compiled into no
    check (spec §11.8), so nothing runs after the body and the function
    is not split: one function, keeping its own `return_call`."""
    compiled = pipeline.compile(_STRING, file=FILE)
    assert "@body" not in compiled.wat
    assert "return_call $:cs\n" in compiled.wat + "\n"


_TAIL_CALLER = """\
public fn f(@Nat -> @Nat)
  requires(@Nat.0 < 1000)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  @Nat.0
}

public fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f(@Nat.0)
}
"""


def test_repro_another_functions_tail_call_does_not_hide_a_refutation() -> None:
    """`g` tail-calls `f` (`return_call $:f`), and `f` never calls itself:
    a trap of `f`'s proved `ensures` check in a trial of `f` (beside
    the entry check of its `requires`, which the trial's own call sets aside) (a test double:
    the frames and kind such a trap would carry) contradicts the proof,
    and is reported refuted.  Only `f`'s own body, or its split body,
    transferring to itself makes its frame ambiguous."""
    from vera.tester import TrialResult, _TrapIndex
    compiled = pipeline.compile(_TAIL_CALLER, file=FILE)
    assert "return_call $:f\n" in compiled.wat + "\n"
    verified = pipeline.verify(_TAIL_CALLER, file=FILE)
    index = _TrapIndex.joined(
        verified.result, compiled.result,
        program=compiled.checked.program, file=FILE, resolved_modules=[])
    trial = TrialResult(
        fn_name="f", args={}, status="fail", message="",
        trap_kind="contract_violation", trap_frames=[("f", False)])
    decl = next(d.decl for d in compiled.checked.program.declarations
                if getattr(d.decl, "name", None) == "f")
    index.attribute(trial, decl)
    assert trial.status == "refuted", (trial.status, trial.attribution)


@pytest.mark.parametrize(
    ("frames", "status"),
    [([("f", False), ("f$exn_boundary", False)], "refuted"),
     ([("f", False), ("vera.print", True)], "refuted"),
     ([("f", False), ("g", False)], "unattributed")],
    ids=["exn-boundary-caller", "builtin-caller", "declared-caller"])
def test_repro_the_frames_after_the_trials_own_call_say_where_it_fired(
    frames: list[tuple[str, bool]], status: str,
) -> None:
    """The frames after `f`'s say whether the trap fired at the trial's
    own call: the exported wrapper `f$exn_boundary` and a built-in are
    the trial's way in, so the entry check of `f`'s `requires` is set
    aside and the proved `ensures` check is what fired (refuted); a
    declared caller `g` makes the `requires` check stand for `g`'s call,
    which the trial did not make (unattributed)."""
    from vera.tester import TrialResult, _TrapIndex
    compiled = pipeline.compile(_TAIL_CALLER, file=FILE)
    verified = pipeline.verify(_TAIL_CALLER, file=FILE)
    index = _TrapIndex.joined(
        verified.result, compiled.result,
        program=compiled.checked.program, file=FILE, resolved_modules=[])
    trial = TrialResult(
        fn_name="f", args={}, status="fail", message="",
        trap_kind="contract_violation", trap_frames=frames)
    decl = next(d.decl for d in compiled.checked.program.declarations
                if getattr(d.decl, "name", None) == "f")
    index.attribute(trial, decl)
    assert trial.status == status, (trial.status, trial.attribution)


#: A module text for `--distrust`'s index: a split function `f` (its entry
#: calls its body, the body calls `helper` and transfers to itself), after
#: another function's tail call of it, then `g`, which calls `lone` and the
#: closure table, the closure, and `last`, whose call no earlier function
#: makes.
_SPLIT_WAT = """\
  (table 1 funcref)
  (elem (i32.const 0) func $anon_0)
  (func $:caller (param $p0 i64) (result i64)
    local.get 0
    return_call $:f
  )
  (func $:f (param $p0 i64) (result i64)
    local.get 0
    call $:f@body
  )
  (func $:f@body (param $p0 i64) (result i64)
    call $:helper
    local.get 0
    return_call $:f@body
  )
  (func $:g (result i64)
    call $:lone
    call_indirect (type $closure_sig_0)
  )
  (func $anon_0 (param $env i32) (result i64)
    call $:deep
  )
  (func $:lone (result i64)
    i64.const 1
  )
  (func $:helper (result i64)
    i64.const 1
  )
  (func $:last (result i64)
    call $:tail
  )
"""


def test_repro_distrust_reads_a_split_function_as_one_node() -> None:
    """`--distrust`'s call graph reads each function's own text: the split
    `f`'s entry and body are one node, `f`, holding what the body calls;
    a closure-table call adds the table to the function that makes it and
    keeps its direct calls; no function holds a later one's calls.  And
    `f` transfers to itself (its body's `return_call`, found after another
    function's tail call of `f`), where `helper` does not."""
    from vera.tester import _TrapIndex
    index = _TrapIndex([], [], _SPLIT_WAT)
    assert index.reachable("f") == {"f", "helper"}
    assert index.reachable("caller") == {"caller", "f", "helper"}
    assert index.reachable("g") == {"g", "lone", "anon_0", "deep"}
    assert index.reachable("lone") == {"lone"}
    assert index.reachable("helper") == {"helper"}
    assert index._transfers_to_itself("f")
    assert not index._transfers_to_itself("helper")
    assert not index._transfers_to_itself("caller")
    # A transfer that ends the module text, with no line after it.
    assert _TrapIndex([], [], "  (func $:h@body\n    return_call $:h@body"
                      )._transfers_to_itself("h")


# =====================================================================
# The backtrace and the join read a split function as its declaration
# =====================================================================


_CALLED = _NAMED + """
public fn go(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Nat = walk(0, @Nat.0);
  @Nat.0
}

public fn down(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    10 / @Int.0
  } else {
    down(@Int.0, @Nat.0 - 1) + 1
  }
}
"""


def test_repro_the_backtrace_names_a_split_function_once_and_its_callers() -> None:
    """A trap in `walk`'s body, reached from `go`, shows `walk` once (its
    body's frame and its entry's) and then `go`; a function that is not
    split shows a frame for every call of itself."""
    ran = pipeline.run(_CALLED, "go", [200], file=FILE)
    assert ran.trap is not None
    assert [f.func for f in ran.trap.frames] == ["walk", "go"]
    ran = pipeline.run(_CALLED, "down", [0, 3], file=FILE)
    assert ran.trap is not None and ran.trap.kind == "divide_by_zero"
    assert [f.func for f in ran.trap.frames] == ["down"] * 4


def test_repro_the_backtrace_reader_normalises_each_frame() -> None:
    """The reader's own handling of a frame's name, by wasmtime frame
    stand-ins: a leading `$` stripped once (a split body's and its entry's
    shown once, as `walk`), a frame with no name or none at all skipped."""
    from vera.runtime.traps import _resolve_trap_frames

    class Frame:
        def __init__(self, name: str | None) -> None:
            self.func_name = name

    class Nameless:
        pass

    trap = Exception()
    trap.frames = [  # type: ignore[attr-defined]
        Frame("$:walk@body"), Frame("$:walk"), Frame(None), Nameless(),
        Frame("$:go")]
    got = _resolve_trap_frames(
        trap, {"walk": (FILE, 1, 12), "go": (FILE, 14, 21)})
    assert [(f.func, f.file, f.line_start) for f in got] == [
        ("walk", FILE, 1), ("go", FILE, 14)]


_EXN = """\
public fn risky(@Nat -> @Nat)
  requires(@Nat.0 < 1000)
  ensures(@Nat.result >= @Nat.0)
  effects(<Exn<String>>)
{
  if @Nat.0 == 0 then {
    throw("zero")
  } else {
    @Nat.0
  }
}
"""


@pytest.mark.parametrize(
    ("source", "names"),
    [(_generic("@Nat.result >= @Nat.1"), {"gcount$Bool", "gcount$Int"}),
     (program(CHECKS[0], "where"), {"go$where$loop"}),
     (_EXN, {"risky", "risky$exn_boundary"})],
    ids=["generic-clones", "where-helper", "exn-boundary"])
def test_repro_the_join_reads_each_function_under_its_declaration(
    source: str, names: set[str],
) -> None:
    """The reconciliation's regions name the module functions compiled
    from a declaration as the record of checks names them: a split
    clone's entry and body as the clone, a `where` helper by its own
    name, an exported function's exception boundary under the function's
    region."""
    from vera.reconcile import _function_regions
    compiled = pipeline.compile(source, file=FILE)
    assert compiled.ok
    regions = set(_function_regions(compiled.result).values())
    assert frozenset(names) in regions, regions


def test_repro_the_entry_tripwire_refuses_a_transfer_in_the_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A test double of a check after the body that leaves by
    `return_call`: the split `walk`'s entry would hold it, and skip the
    check, so the compile stops with one [E699] naming `walk` and the
    call; the body, which may transfer, is not what the tripwire reads."""
    from vera.codegen.contracts import ContractsMixin
    original = ContractsMixin._compile_postconditions

    def planted(self, ctx, decl, *args):  # type: ignore[no-untyped-def]
        out = original(self, ctx, decl, *args)
        return [*out, "return_call $:walk"] if decl.name == "walk" else out

    monkeypatch.setattr(ContractsMixin, "_compile_postconditions", planted)
    compiled = pipeline.compile(_NAMED, file=FILE)
    refusals = [d for d in compiled.diagnostics if d.error_code == "E699"]
    assert len(refusals) == 1, [d.description for d in compiled.diagnostics]
    (refusal,) = refusals
    assert refusal.description == (
        "Internal compiler error while compiling 'walk': the entry of a "
        "split function holds the tail call 'return_call $:walk', which "
        "would skip the check after its body (#1851)")
    assert refusal.rationale == (
        "This is a codegen invariant violation — a split function's entry "
        "calls its body and runs the check once; only the body may leave "
        "by return_call.")
    assert refusal.fix == (
        "No change to the program is the remedy: report it, with this "
        "diagnostic, at https://github.com/aallan/vera/issues")
    assert refusal.spec_ref == (
        'Chapter 0, Section 0.5.1 "Diagnostic Structure"')


def test_repro_the_entry_tripwire_refuses_an_indirect_transfer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The tripwire reads an instruction's first word as a transfer when
    it starts with `return_call`, so a `return_call_indirect` in the entry
    is refused too."""
    from vera.codegen.contracts import ContractsMixin
    original = ContractsMixin._compile_postconditions
    transfer = "return_call_indirect (type $closure_sig_0)"

    def planted(self, ctx, decl, *args):  # type: ignore[no-untyped-def]
        out = original(self, ctx, decl, *args)
        return [*out, transfer] if decl.name == "walk" else out

    monkeypatch.setattr(ContractsMixin, "_compile_postconditions", planted)
    compiled = pipeline.compile(_NAMED, file=FILE)
    refusals = [d for d in compiled.diagnostics if d.error_code == "E699"]
    assert len(refusals) == 1, [d.description for d in compiled.diagnostics]
    assert f"'{transfer}'" in refusals[0].description


_EXN_MEASURE = """\
public fn countdown(@Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  decreases(@Nat.0 - 1)
  effects(<Exn<String>>)
{
  if @Nat.0 == 1 then {
    0
  } else {
    countdown(@Nat.0 - 1)
  }
}
"""


def test_repro_a_measure_with_no_check_gives_its_operations_its_reason() -> None:
    """A measure on an `Exn` row has no check, and every row its
    operations draw, at the entry evaluation and at the self tail call,
    carries the measure's reason, never none."""
    from vera.obligations.table import REASON_EXN_DECREASES
    table = pipeline.verify(_EXN_MEASURE, file=FILE).result.table
    rows = [r for r in table.rows if not r.guard.check]
    assert rows
    assert all(isinstance(r.guard.reason, str) and r.guard.reason
               for r in rows), [(r.kind, r.guard.reason) for r in rows]
    assert sum(r.guard.reason == REASON_EXN_DECREASES for r in rows) >= 3, [
        (r.kind, r.guard.reason) for r in rows]


_STATE_FROM_FIVE = """\
private fn tick(@Nat -> @Nat)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + nat_to_int(@Nat.0))
  decreases(@Nat.0)
  effects(<State<Int>>)
{
  if @Nat.0 == 0 then {
    0
  } else {
    let @Int = get(());
    put(@Int.0 + 1);
    tick(@Nat.0 - 1)
  }
}

public fn go(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  put(5);
  tick(@Nat.0)
}
"""


def test_repro_the_entry_takes_the_old_state_its_check_reads() -> None:
    """The entry takes the `old()` snapshot before it calls the body: from
    a state of 5, three hops leave 8, which the postcondition reads as 5
    plus 3.  A snapshot never taken would read 0 and trap."""
    compiled = pipeline.compile(_STATE_FROM_FIVE, file=FILE)
    assert "return_call $:tick@body" in compiled.wat
    ran = pipeline.run(compiled, "go", [3])
    assert ran.trap is None, str(ran.trap)
    assert ran.value == 0


def test_repro_a_private_split_function_is_not_exported() -> None:
    """The entry carries the declaration's export, and only a public
    declaration has one: the private `count` is exported under no name,
    entry or body, and the public `main` is."""
    wat = pipeline.compile(_WASI, file=FILE).wat
    assert '(export "count")' not in wat
    assert '(export "main")' in wat
