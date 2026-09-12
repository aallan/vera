"""Construction-position refinement guards (#1426).

#1412 put the construction positions on the obligation record: a refined
value placed into a constructor field, a tuple component, an array element
or a `Map` value is obligated where it is built.  What it could not do was
CHECK them — the §2.6.5 predicate lowering ran at pattern-bind sites only,
so each of those obligations disclosed `tier3_unguarded` / E506 and the
value went in unexamined.

This closes that half.  The site table both components read
(`vera.narrowing.REFINED_BIND_GUARDED_SITES`) gains the four construction
sites, and the same `_emit_bind_refine_guard` lowering runs at each store,
so a site cannot be classified guarded without being guarded or guarded
without being counted.

Every cell here is STORE-ONLY: it builds the container and never reads it
back.  A fixture that reads the component out is answered by the read-side
pattern-bind guard (#765) and cannot tell a store guard from a read guard —
which is exactly the confusion that put a false `guarded` on the array
element in #1412's own review round.  The value is `-4` against a `> 0`
predicate, so a clamp to zero, a default, or a dropped guard all read
differently from the trap.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from vera import narrowing

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

#: The repo root, for the one cell that pins a conformance program.
_PKG_PARENT_PATH = Path(vera.__file__).resolve().parents[1]

#: What the §2.6.5 guard says when it fires.
_REFINE_TRAP = "Refinement violation"


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


def _write(tmp_path: Path, source: str, name: str = "p.vera") -> Path:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return p


def _run(tmp_path: Path, source: str, *args: str, name: str = "p.vera") -> str:
    proc = _cli("run", str(_write(tmp_path, source, name)), *args)
    return proc.stdout + proc.stderr


def _wat(tmp_path: Path, source: str, name: str = "p.vera") -> str:
    proc = _cli("compile", "--wat", str(_write(tmp_path, source, name)))
    assert proc.returncode == 0, proc.stderr[-500:]
    return proc.stdout


def _obligations(tmp_path: Path, source: str,
                 name: str = "p.vera") -> tuple[list[dict], dict]:
    proc = _cli("verify", "--json", str(_write(tmp_path, source, name)))
    try:
        envelope = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None
    return envelope["obligations"], envelope



def _verify_in_process(source: str) -> list:
    """Obligations from an IN-PROCESS verify, for the cells that patch a table.

    The rest of this file drives the real CLI in a subprocess, which is what
    makes its claims about the shipped toolchain honest.  A cell that
    MUTATES a shared table cannot do that — the subprocess would import the
    unpatched module — so these two run in-process and pay for it by
    asserting only statuses the verifier itself derives.
    """
    from tests.verifier_helpers import _verify
    return list(_verify(source).obligations)

def _assert_partition(envelope: dict) -> None:
    """`len(obligations) == total + violated + tier3_unguarded`."""
    obs = envelope["obligations"]
    summary = envelope["verification"]
    violated = sum(1 for o in obs if o["status"] == "violated")
    unguarded = sum(1 for o in obs if o["status"] == "tier3_unguarded")
    assert len(obs) == summary["total"] + violated + unguarded, (
        f"the documented accounting broke: {len(obs)} records vs "
        f"{summary['total']} + {violated} + {unguarded}"
    )


_PRELUDE = "type Pos = { @Int | @Int.0 > 0 };\n\n"

#: The four construction positions, each STORE-ONLY: the container is built
#: from a value its component type forbids and never read back, so only a
#: guard AT THE STORE can trap.
_CONSTRUCTION_SHAPES: dict[str, str] = {
    "constructor field": _PRELUDE + """\
private data Box {
  MkBox(Pos)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Box = MkBox(@Int.0);
  1
}
""",
    "tuple component": _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Pos, Int> = Tuple(@Int.0, 1);
  1
}
""",
    "array element": _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Pos> = [@Int.0];
  1
}
""",
    "map value": _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Pos> = map_insert(map_new(), "k", @Int.0);
  1
}
""",
}


@pytest.mark.parametrize("site", sorted(_CONSTRUCTION_SHAPES))
def test_the_store_refuses_a_value_its_component_type_forbids(
    tmp_path: Path, site: str,
) -> None:
    """The property, read from a RUN: `-4` does not get into the container.

    Store-only, so the trap can only be the store's.  Before #1426 every one
    of these returned `1` — the value went in, the obligation said so, and
    nothing checked it.
    """
    out = _run(tmp_path, _CONSTRUCTION_SHAPES[site], "--fn", "f", "--", "-4",
               name=f"{site.replace(' ', '_')}_run.vera")
    assert _REFINE_TRAP in out, (
        f"a refined {site} accepted `-4` at construction, with nothing "
        f"downstream to catch it:\n{out}"
    )


@pytest.mark.parametrize("site", sorted(_CONSTRUCTION_SHAPES))
def test_the_guard_is_in_the_module_not_only_in_the_run(
    tmp_path: Path, site: str,
) -> None:
    """The artifact half, so a cell cannot pass on an unrelated trap.

    `$vera.contract_fail` is the §2.6.5 lowering's own signal; a bare
    `unreachable` from some other check would satisfy the run assertion
    above while leaving this site unguarded.
    """
    wat = _wat(tmp_path, _CONSTRUCTION_SHAPES[site],
               name=f"{site.replace(' ', '_')}_wat.vera")
    # Sliced to `f`'s own body, not searched module-wide: every shape also
    # emits the `let`'s declared-type boundary records, and the `Map` one
    # carries #1410's nested-refinement obligation, so a `contract_fail`
    # planted anywhere would satisfy a whole-module search — which is the
    # same attribution failure the docstring says this cell exists to avoid
    # (CR PR-review).
    _head, _sep, rest = wat.partition("(func $f ")
    assert rest, f"no `f` in the emitted module:\n{wat[:400]}"
    body = rest.split("\n  )")[0]
    assert "call $vera.contract_fail" in body, (
        f"no §2.6.5 guard is emitted in `f` for a refined {site}:\n{body}"
    )


@pytest.mark.parametrize("site", sorted(_CONSTRUCTION_SHAPES))
def test_the_obligation_and_the_guard_agree(
    tmp_path: Path, site: str,
) -> None:
    """Parity at the new sites: the record must not say `tier3_unguarded`.

    `-4` against `> 0` is refutable, so the status here is `violated` — the
    strongest verdict, and the one that proves the site is on the record at
    all.  What must NOT appear is an unguarded disclosure, which is what the
    site reported before the guard existed.
    """
    obs, envelope = _obligations(
        tmp_path, _CONSTRUCTION_SHAPES[site],
        name=f"{site.replace(' ', '_')}_obl.vera")
    # Read the record for the VALUE going in, not every `refine_bind` in the
    # program.  The `Map` shape also carries #1410's nested-refinement
    # obligation about the whole `map_insert(...)` expression — a different
    # site asking a different question (whether the SLOT's declared type is
    # established for later readers, for any producer, not just this literal
    # one), and it stays unguarded because codegen's boundary decomposition
    # reaches tuple components and stops.  Folding it in here would make this
    # cell fail for a reason that has nothing to do with the store.
    value = [(o["status"], o.get("error_code")) for o in obs
             if o["kind"] == "refine_bind" and o["description"] == "@Int.0"]
    assert value, (
        f"the refined {site} is not on the record at all: "
        f"{[(o['status'], o['description']) for o in obs]}"
    )
    assert ("violated", "E505") in value, (
        f"the refined {site} value is recorded as {value}, not the refutation "
        f"`-4` against `> 0` should produce"
    )
    assert ("tier3_unguarded", "E506") not in value, (
        f"the refined {site} still discloses an unguarded store while the "
        f"module guards it: {value}"
    )
    _assert_partition(envelope)


#: The two construction stores whose SIGN obligation was disclosed `E504`
#: while the predicate at the very same store was checked (#1440).  Kept
#: store-only for the reason the refined shapes above are: a fixture that
#: reads the component back is answered by the read-side pattern-bind guard
#: (#765), which cannot tell a store guard from a read guard.
_SIGN_SHAPES: dict[str, str] = {
    "array element": """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Nat> = [@Int.0];
  1
}
""",
    "map value": """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Nat> = map_insert(map_new(), "k", @Int.0);
  1
}
""",
}

#: What the sign guard says when it fires.
_NAT_TRAP = "Negative value bound into a @Nat slot"


@pytest.mark.parametrize("site", sorted(_SIGN_SHAPES))
def test_the_store_refuses_a_negative_into_a_nat_component(
    tmp_path: Path, site: str,
) -> None:
    """#1440: the sign obligation at these stores is checked, not disclosed.

    Both stores carried TWO obligations and checked one: #1426 gave the
    §2.6.5 predicate its guard here, and the `@Nat >= 0` beside it stayed
    `tier3_unguarded` / E504.  Nothing about the store justified the split —
    it was where the earlier work stopped — so `-4` went into an
    `@Array<Nat>` and the program returned normally.
    """
    out = _run(tmp_path, _SIGN_SHAPES[site], "--fn", "f", "--", "-4",
               name=f"{site.replace(' ', '_')}_sign.vera")
    assert _NAT_TRAP in out, (
        f"a refined-free `@Nat` {site} accepted `-4` at construction:\n{out}"
    )


@pytest.mark.parametrize("site", sorted(_SIGN_SHAPES))
def test_the_sign_obligation_no_longer_discloses_unguarded(
    tmp_path: Path, site: str,
) -> None:
    """And the record says so.

    `-4` against `>= 0` is refutable, so the status is `violated` — what
    must not appear is the E504 disclosure the site carried while the guard
    was absent.
    """
    obs, envelope = _obligations(
        tmp_path, _SIGN_SHAPES[site],
        name=f"{site.replace(' ', '_')}_sign_obl.vera")
    binds = [(o["status"], o.get("error_code"))
             for o in obs if o["kind"] == "nat_bind"]
    assert ("violated", "E503") in binds, binds
    assert ("tier3_unguarded", "E504") not in binds, (
        f"the `@Nat` {site} still discloses an unguarded store while the "
        f"module guards it: {binds}"
    )
    _assert_partition(envelope)


_STATE_PUT = _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(1) },
    put(@Pos) -> { resume(()) }
  } in {
    put(@Int.0);
    1
  }
}
"""

_STATE_PUT_OPAQUE = _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = 1) {
    get(@Unit) -> { resume(1) },
    put(@Pos) -> { resume(()) }
  } in {
    put(handle[Exn<Int>] { throw(@Int) -> { @Int.0 } } in { throw(@Int.0) });
    1
  }
}
"""


class TestTheStateWriteBoundaryChecksItsPredicate:
    """#1439: the §2.6.5 predicate at a `State` write.

    The three writes — the `handle` init, `put`'s argument, and a clause's
    `with @T = …` override — have guarded the SIGN direction since #1203,
    keyed off the cell's REPRESENTATION because a width question needs no
    more.  The predicate was the other half and was never lowered, so a
    `State<{ @Int | @Int.0 > 0 }>` cell took a `-4` and a later reader
    binding it at the refinement reasoned from a predicate that does not
    hold.  The `Exn` `throw` payload has taken this guard since #1268; this
    is the same lowering at the boundary beside it.
    """

    def test_the_write_refuses_a_value_the_cell_type_forbids(
        self, tmp_path: Path,
    ) -> None:
        out = _run(tmp_path, _STATE_PUT, "--fn", "f", "--", "-4",
                   name="state_put.vera")
        assert "Refinement violation in State put" in out, (
            f"the state cell accepted a value its own type forbids:\n{out}"
        )

    def test_and_the_classification_counts_that_guard(
        self, tmp_path: Path,
    ) -> None:
        """The parity half, on the leg where the flag is consulted.

        A refutable value settles statically and never reads the guarded
        flag, so the discriminator is an opaque producer: undecided, and
        therefore classified by whether a runtime check exists.  It must be
        `tier3` — the guard is emitted — where it read `tier3_unguarded`
        while the predicate went unlowered.
        """
        obs, envelope = _obligations(
            tmp_path, _STATE_PUT_OPAQUE, name="state_opaque.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert ("tier3", "E506") in binds, binds
        assert ("tier3_unguarded", "E506") not in binds, (
            f"the State write still discloses an unguarded boundary while "
            f"the module guards it: {binds}"
        )
        _assert_partition(envelope)


_R1412_STATE_INIT = _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Pos>](@Pos = array_length(string_lines("a")) - 5) {
    get(@Unit) -> { resume(1) },
    put(@Pos) -> { resume(()) }
  } in {
    2
  }
}
"""

_R1412_GENERIC_FIELD = _PRELUDE + """\
private data Box<T> {
  MkBox(T)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Box<Pos> = MkBox(@Int.0);
  1
}
"""

_R1412_NESTED_TUPLE = _PRELUDE + """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Tuple<Pos, Int>, Int> = Tuple(Tuple(@Int.0, 1), 2);
  1
}
"""


class TestTheReviewFoundThreeMoreDesyncs:
    """Three sites where the two components disagreed (R-1412 F1-F3).

    Each is the same defect in a different direction, and each was measured
    through the real pipeline rather than reasoned about:

    * **F1** — the `handle` init and a clause's `with @T = …` override are
      guarded by codegen, which keys all three `State` writes on one site
      string, while the verifier recorded the first and third under names of
      their own that are not in the table.  Both derived `False` and
      disclosed `tier3_unguarded` while the guard was emitted and trapping.
      The three writes now share ONE key, so a drop-mutation moves all three
      statuses with all three guards.
    * **F2** — a generic constructor field instantiated at a refinement:
      `field_type_exprs` keeps the type VARIABLE for `data Box<T>`, and the
      emitter preferred that declared expression over the instantiation, so
      it found no refinement to guard while the verifier obligated the
      instantiated one.  Precedence is by GUARDABILITY now, not by source.
    * **F3** — a nested literal carries no recorded target of its own, so
      `Tuple(Tuple(@Int.0, 1), 2)` guarded the outer components and left the
      inner ones unchecked.  The enclosing store hands its component type
      down, which is the codegen twin of the threading the verifier does.
    """

    def test_f1_the_state_init_counts_the_guard_it_has(
        self, tmp_path: Path,
    ) -> None:
        obs, envelope = _obligations(
            tmp_path, _R1412_STATE_INIT, name="f1.vera")
        binds = [(o["status"], o.get("error_code"))
                 for o in obs if o["kind"] == "refine_bind"]
        assert ("tier3", "E506") in binds, binds
        assert ("tier3_unguarded", "E506") not in binds, (
            f"the init discloses an unguarded write while the module guards "
            f"it and traps: {binds}"
        )
        _assert_partition(envelope)

    def test_f1_and_the_init_really_traps(self, tmp_path: Path) -> None:
        out = _run(tmp_path, _R1412_STATE_INIT, "--fn", "f", "--", "1",
                   name="f1run.vera")
        assert "Refinement violation in State cell init" in out, out

    @pytest.mark.parametrize(
        "shape,source,where",
        [
            ("f2-generic-field", _R1412_GENERIC_FIELD, "MkBox(…)"),
            ("f3-nested-tuple", _R1412_NESTED_TUPLE, "Tuple(…)"),
        ],
    )
    def test_the_value_that_escaped_is_refused(
        self, tmp_path: Path, shape: str, source: str, where: str,
    ) -> None:
        """Store-only, and `-4` used to come back out of both."""
        out = _run(tmp_path, source, "--fn", "f", "--", "-4",
                   name=f"{shape}.vera")
        assert "Refinement violation" in out and where in out, out
        assert out.strip() != "1", out


_F4_MAP_VIA_CALLEE = _PRELUDE + """\
private fn ins(@Int -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{ map_insert(map_new(), "a", @Int.0) }

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = ins(@Int.0);
  7
}
"""

_F4_ARRAY_VIA_CALLEE = _PRELUDE + """\
private fn mk(@Int -> @Array<Pos>)
  requires(true) ensures(true) effects(pure)
{ [@Int.0] }

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Array<Pos> = mk(@Int.0);
  7
}
"""


class TestAContainerBuiltInReturnPositionIsObligated:
    """A container CONSTRUCTED in return position (R-1412 F4).

    The store's component type comes from the DECLARED RETURN type, which is
    the only place it survives in this shape: the value being stored is a
    PARAMETER rather than a literal, and `map_insert`'s own argument target
    carries the erased base, because generic unification resolves the value
    parameter against the `map_new()` receiver.

    The array dual reached the record by accident.  An `ArrayLit` is visited
    by the walk wherever it stands, so `mk(@Int -> @Array<Pos>) { [@Int.0] }`
    was obligated and refuted; `ins(@Int -> @Map<String, Pos>)` entered no
    construction descent at all — the descent is reached from a `let` or an
    array literal, and this is neither — so it recorded nothing at its store
    while codegen guarded it.  A guard counted by no obligation is the same
    desync as an obligation counted by no guard, in the direction that reads
    as a clean program: `verify` said `ok: true`.

    The two legs are asserted together, because the array one is what says
    where the component type had to come from.
    """

    def test_the_map_store_is_refuted_like_its_array_dual(
        self, tmp_path: Path,
    ) -> None:
        map_obs, map_env = _obligations(
            tmp_path, _F4_MAP_VIA_CALLEE, name="f4map.vera")
        arr_obs, _ = _obligations(
            tmp_path, _F4_ARRAY_VIA_CALLEE, name="f4arr.vera")

        def value_records(obs: list[dict]) -> list[tuple]:
            return [(o["status"], o.get("error_code")) for o in obs
                    if o["kind"] == "refine_bind"
                    and o["description"] == "@Int.0"]

        assert ("violated", "E505") in value_records(arr_obs), arr_obs
        assert ("violated", "E505") in value_records(map_obs), (
            f"the `Map` value store built in return position carries no "
            f"record, while its array dual is refuted: {map_obs}"
        )
        assert map_env["ok"] is False, (
            "verify reports a clean program for a store it does not check"
        )
        _assert_partition(map_env)

    def test_and_both_stores_refuse_the_value_at_run_time(
        self, tmp_path: Path,
    ) -> None:
        """The guard was always there for the `Map` leg — that is the point.

        The defect was the missing RECORD, so this cell pins that the guard
        the record now counts is real, on both legs.
        """
        for source, name, where in (
            (_F4_MAP_VIA_CALLEE, "f4maprun.vera", "map value"),
            (_F4_ARRAY_VIA_CALLEE, "f4arrrun.vera", "array element"),
        ):
            out = _run(tmp_path, source, "--fn", "f", "--", "-4", name=name)
            assert "Refinement violation" in out and where in out, out


_CR_BRANCHING_RETURN = _PRELUDE + """\
private fn ins(@Int -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 > 100 then { map_insert(map_new(), "a", @Int.0) } else { map_insert(map_new(), "b", @Int.0) }
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = ins(@Int.0);
  7
}
"""


_CR_BRANCH_CONDITION_PROVES = _PRELUDE + """\
private fn ins(@Int -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  if @Int.0 > 100 then { map_insert(map_new(), "a", @Int.0) } else { map_new() }
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = ins(@Int.0);
  7
}
"""

_CR_MATCH_CONDITION_PROVES = _PRELUDE + """\
private fn ins(@Int -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  match @Int.0 > 100 {
    true -> map_insert(map_new(), "a", @Int.0),
    false -> map_new()
  }
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = ins(@Int.0);
  7
}
"""

_CR_MATCH_BINDER_IS_NOT_THE_PARAMETER = _PRELUDE + """\
private fn ins(@Int, @Option<Int> -> @Map<String, Pos>)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  match @Option<Int>.0 {
    Some(@Int) -> map_insert(map_new(), "a", @Int.0),
    None -> map_new()
  }
}

public fn f(@Int, @Option<Int> -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  let @Map<String, Pos> = ins(@Int.0, @Option<Int>.0);
  7
}
"""


def test_a_container_built_inside_a_branch_is_obligated(
    tmp_path: Path,
) -> None:
    """A branch stands where its arms do (CR PR-review).

    The return position hands the declared return type to the container
    descent, and the descent unwrapped a `Block` but stopped at an `if` or a
    `match` — so a container built inside a branch entered no descent at
    all.  Measured before the fix: this program verified `ok: true` with no
    record at either store while the body emitted TWO guards, which is the
    F4 class one level in and in the direction that reads as a clean
    program.

    Both arms are asserted, not just one: a descent that recursed into the
    `then` and forgot the `else` would satisfy a single-record check.
    """
    obs, envelope = _obligations(
        tmp_path, _CR_BRANCHING_RETURN, name="branchret.vera")
    stores = [(o["status"], o.get("error_code")) for o in obs
              if o["kind"] == "refine_bind" and o["description"] == "@Int.0"]
    assert len(stores) == 2, (
        f"a `Map` value store built inside a branch carries no record while "
        f"the module guards it: {obs}"
    )
    # Each arm gets its OWN answer, which is what makes this a differential
    # rather than a count.  `@Int.0 > 100` proves `@Int.0 > 0`, so the `then`
    # store is Tier 1; the `else` arm holds only `@Int.0 <= 100`, which
    # admits 0.  Asserting two `violated` (as this cell first did) pins the
    # defect R-1412 found: a descent that never receives the arm's path
    # condition refutes BOTH, and the fixture would re-pin it (R-1412 H1).
    assert stores.count(("verified", None)) == 1, (
        f"the `then` arm's condition proves the predicate, so its store is "
        f"Tier 1 — a `violated` is the verifier refusing a correct arm: "
        f"{obs}"
    )
    assert stores.count(("violated", "E505")) == 1, (
        f"the `else` arm holds only `@Int.0 <= 100`, which admits 0: {obs}"
    )
    assert envelope["ok"] is False
    _assert_partition(envelope)


def test_an_arm_condition_that_proves_the_predicate_discharges_the_store(
    tmp_path: Path,
) -> None:
    """The arm's path CONDITION has to reach the store (R-1412 H1).

    Descending into an arm without extending the path conditions refutes a
    store the arm's own condition proves.  This program is correct — it
    verified `ok: true` before the descent reached the arm at all — and the
    descent first landed it as `violated` / E505, reporting a counterexample
    (`@Int.0 = 0`) that is unreachable in the arm it was reported for.  The
    E505 fix paragraph advises "guard the binding with an `if` whose
    condition is the predicate"; this program does exactly that, so the
    refusal contradicted the diagnostic's own advice.
    """
    obs, envelope = _obligations(
        tmp_path, _CR_BRANCH_CONDITION_PROVES, name="branchproved.vera")
    stores = [(o["status"], o.get("error_code")) for o in obs
              if o["kind"] == "refine_bind" and o["description"] == "@Int.0"]
    assert stores == [("verified", None)], (
        f"the arm's own condition proves the predicate, so the store is "
        f"Tier 1; a `violated` here is the verifier refusing a correct "
        f"program: {obs}"
    )
    assert envelope["ok"] is True
    _assert_partition(envelope)


def test_the_match_twin_reads_its_arm_condition_too(
    tmp_path: Path,
) -> None:
    """The same claim for `match`, which reaches arms by a different route.

    `if` takes its condition from `translate_expr`; a `match` arm takes its
    from `_pattern_condition` against the translated scrutinee.  Two
    mechanisms means two chances to drop it, so the pair is asserted rather
    than the `if` alone.
    """
    obs, envelope = _obligations(
        tmp_path, _CR_MATCH_CONDITION_PROVES, name="matchproved.vera")
    stores = [(o["status"], o.get("error_code")) for o in obs
              if o["kind"] == "refine_bind" and o["description"] == "@Int.0"]
    assert stores == [("verified", None)], (
        f"the `true` arm holds `@Int.0 > 100`, which proves the predicate: "
        f"{obs}"
    )
    assert envelope["ok"] is True
    _assert_partition(envelope)


_1459_GENERIC_CALLEE = _PRELUDE + """\
private forall<T> fn head(@Array<T> -> @Option<T>)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true) effects(pure)
{
  Some(@Array<T>.0[0])
}

private fn build(@Array<Int> -> @Map<String, Pos>)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true) effects(pure)
{
  match head(@Array<Int>.0) {
    Some(@Int) -> map_insert(map_new(), "a", @Int.0),
    None -> map_new()
  }
}

public fn f(@Array<Int> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true) effects(pure)
{
  let @Map<String, Pos> = build(@Array<Int>.0);
  7
}
"""


_1459_TWO_INSTANCES = """\
private forall<T> fn head(@Array<T> -> @Option<T>)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true) effects(pure)
{
  Some(@Array<T>.0[0])
}

private forall<U> fn wrap(@Array<U> -> @Int)
  requires(array_length(@Array<U>.0) > 0)
  ensures(true) effects(pure)
{
  match head(@Array<U>.0) {
    Some(@U) -> 1,
    None -> 0
  }
}

public fn f(@Array<Int>, @Array<String> -> @Int)
  requires(array_length(@Array<Int>.0) > 0)
  ensures(true) effects(pure)
{
  wrap(@Array<Int>.0) + wrap(@Array<String>.0)
}
"""


def _call_pre_lines(obs: list[dict]) -> list[int]:
    """Line of every `call_pre` record, in stream order."""
    return [(o.get("location") or {}).get("line")
            for o in obs if o.get("kind") == "call_pre"]


_BLOCK_TAIL_LOCAL = _PRELUDE + """\
private fn mk(@Int -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 5;
  map_insert(map_new(), "a", @Int.0)
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = mk(@Int.0);
  7
}
"""

_BLOCK_TAIL_NO_SHADOW = _PRELUDE + """\
private fn mk(@String -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  let @Int = 5;
  map_insert(map_new(), "a", @Int.0)
}

public fn f(@String -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = mk(@String.0);
  7
}
"""

_BLOCK_TAIL_OPAQUE_SHADOW = _PRELUDE + """\
private fn mk(@Int -> @Map<String, Pos>)
  requires(@Int.0 > 0) ensures(true) effects(<Random>)
{
  let @Int = Random.random_int(0, 9);
  map_insert(map_new(), "a", @Int.0)
}

public fn f(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(<Random>)
{
  let @Map<String, Pos> = mk(@Int.0);
  7
}
"""


def _store_status(obs: list[dict]) -> list[tuple]:
    """Status of every refine_bind recorded for the stored slot."""
    return [(o["status"], o.get("error_code")) for o in obs
            if o["kind"] == "refine_bind" and o["description"] == "@Int.0"]


_STATE_OPAQUE = (
    "handle[Exn<Int>] { throw(@Int) -> { @Int.0 } } in { throw(@Int.0) }"
)

#: All THREE `State` write positions in one program, each given a value the
#: SMT layer cannot decide so the obligation lands at Tier 3 — the only
#: status that CONSULTS the guarded flag at all (a `violated` never reads
#: it, so a fixture built from refutable values would pin nothing).
_STATE_THREE_LEGS = _PRELUDE + f"""\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{{
  handle[State<Pos>](@Pos = {_STATE_OPAQUE}) {{
    get(@Unit) -> {{ resume(1) }},
    put(@Pos) -> {{ resume(()) }} with @Pos = {_STATE_OPAQUE}
  }} in {{
    put({_STATE_OPAQUE});
    1
  }}
}}
"""


def test_the_state_entry_moves_all_three_write_legs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Dropping the shared table's `State` entry moves init, update and put.

    The three positions keep their own diagnostic-facing site names, because
    those tell a reader WHICH write to fix, and answer the guardedness
    question through one key (`_STATE_WRITE_SITE`).  That is only worth
    anything if the three actually follow the table together, and they did
    not always: at `74db7ba1` this same mutation moved `put`'s status alone
    while zeroing all three guards — a table the statuses only partly obeyed
    (R-1412's F1).

    So the cell asserts the SET of three, not a count and not one leg.  A
    future tidy-up that reroutes any single position back to a literal
    leaves that leg on `tier3` while its siblings move, and this reds.
    """
    sites = [o for o in _verify_in_process(_STATE_THREE_LEGS)
             if o.kind == "refine_bind" and o.error_code == "E506"]
    assert [o.status for o in sites] == ["tier3"] * 3, (
        f"all three State writes should report a runtime-checked Tier 3 "
        f"while the table lists the site: "
        f"{[(o.line, o.status) for o in sites]}"
    )
    guarded_lines = sorted(o.line for o in sites)

    monkeypatch.setattr(
        narrowing, "REFINED_BIND_GUARDED_SITES",
        frozenset(narrowing.REFINED_BIND_GUARDED_SITES
                  - {"State write boundary"}),
    )
    dropped = [o for o in _verify_in_process(_STATE_THREE_LEGS)
               if o.kind == "refine_bind" and o.error_code == "E506"]
    assert [o.status for o in dropped] == ["tier3_unguarded"] * 3, (
        f"dropping the one table entry must move ALL THREE legs together — "
        f"a leg still reporting `tier3` is following something other than "
        f"the shared table: {[(o.line, o.status) for o in dropped]}"
    )
    assert sorted(o.line for o in dropped) == guarded_lines, (
        f"the same three positions must be the ones that moved: "
        f"{guarded_lines} vs {sorted(o.line for o in dropped)}"
    )


class TestABlockTailIsReadInItsOwnScope:
    """A `Block` stands where its tail does, in the tail's OWN scope.

    The third instance of one mistake: the descent entering a position
    without carrying the scope that position implies (the first two were an
    `if`/`match` arm's path condition and a `match` arm's pattern bindings).
    Here the descent handed the block's tail the ENCLOSING env, so a tail
    naming a block-local slot resolved to a same-named outer instead.

    The three cells below are the three grades that mistake has, and they
    are asserted together because only the middle one looks like a bug from
    the outside: whether a wrong scope REFUSES, merely loses precision, or
    PROVES depends entirely on what the outer env happens to hold at the
    same slot name.
    """

    def test_a_block_local_binding_proves_the_predicate(
        self, tmp_path: Path,
    ) -> None:
        """Grade (a): the false refusal.

        `let @Int = 5` then a store of `@Int.0` into a `Pos` map value.  The
        tail's `@Int.0` is the local `5`, which proves `> 0`.  Measured
        before the fix: `violated` / E505 and `ok: false`, because the
        descent resolved it to `mk`'s unconstrained `@Int` parameter and
        refuted THAT — a refusal of a program that compiles and runs clean
        (`vera run` returns 7, no guard fires).
        """
        obs, envelope = _obligations(
            tmp_path, _BLOCK_TAIL_LOCAL, name="blocklocal.vera")
        assert _store_status(obs) == [("verified", None)], (
            f"the tail's `@Int.0` is the block's own `5`, which proves the "
            f"predicate; anything else is the enclosing scope answering for "
            f"it: {obs}"
        )
        assert envelope["ok"] is True
        _assert_partition(envelope)

    def test_the_same_binding_without_a_shadow_is_also_tier_1(
        self, tmp_path: Path,
    ) -> None:
        """Grade (b): the degrade, which is the SAME defect looking harmless.

        Identical to (a) but the enclosing parameter is `@String`, so there
        is no same-type outer to mis-resolve onto — translation simply
        failed and the store recorded `tier3` / E506.  A reader would call
        that conservative rather than wrong, which is exactly why the pair
        is asserted together: one root, and only the shadowed spelling of it
        is loud.
        """
        obs, envelope = _obligations(
            tmp_path, _BLOCK_TAIL_NO_SHADOW, name="blocknoshadow.vera")
        assert _store_status(obs) == [("verified", None)], (
            f"the local `5` proves the predicate whether or not an outer "
            f"shares its slot name: {obs}"
        )
        _assert_partition(envelope)

    def test_an_untranslatable_shadow_does_not_inherit_the_outers_bound(
        self, tmp_path: Path,
    ) -> None:
        """Grade (c): the false PROOF, and the reason the policy is named.

        `mk` carries `requires(@Int.0 > 0)` and the block rebinds `@Int` to
        `Random.random_int(0, 9)`, which the SMT layer cannot translate and
        which can be 0.  Reading the tail in the enclosing scope discharged
        the store's predicate from the PARAMETER's bound and recorded
        `verified` — a Tier-1 claim, "cannot fail", about a value the
        verifier never held.  Measured at that head: the artifact trapped 2
        runs in 24, because codegen guards the store from the site table
        whatever the verifier concluded.

        `OPAQUE_SHADOW` is what forbids it: the shadowed outer is replaced
        by a tracked opaque const, so the predicate can no longer be
        discharged from a bound that belongs to a different value.  Switch
        the descent's policy to `SKIP` and this cell goes back to
        `verified`, which is the mutation that proves the policy argument is
        load-bearing rather than decorative.

        The answer is Tier 3 and NOT a refusal.  An opaque placeholder is
        not a value the program can produce, so a Z3 countermodel over it
        names nothing reachable — `_is_opaque_shadow`'s own contract is
        "neither proven safe nor treated as a real counterexample".  Both
        halves are asserted: the soundness one (never `verified`) and the
        precision one (never `violated`), because an earlier shape of this
        fix satisfied the first by refusing everything.
        """
        obs, envelope = _obligations(
            tmp_path, _BLOCK_TAIL_OPAQUE_SHADOW, name="blockopaque.vera")
        status = _store_status(obs)
        assert ("verified", None) not in status, (
            f"a `random_int(0, 9)` that can be 0 was PROVED to satisfy "
            f"`> 0` — the outer parameter's `requires` discharging another "
            f"value's obligation: {obs}"
        )
        assert status == [("tier3", "E506")], (
            f"the rebinding is opaque, so the predicate is neither provable "
            f"nor refutable and the store is Tier 3: {obs}"
        )
        _assert_partition(envelope)


_DESTR_LITERAL = _PRELUDE + """\
private fn mk(@Int -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = Tuple(5, 7);
  map_insert(map_new(), "a", @Int.0)
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Pos> = mk(@Int.0);
  7
}
"""

_DESTR_OPAQUE = _PRELUDE + """\
private fn src(@Int -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{
  Tuple(0 - @Int.0, 0 - @Int.0)
}

private fn mk(@Int -> @Map<String, Pos>)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = src(@Int.0);
  map_insert(map_new(), "a", @Int.0)
}

public fn f(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{
  let @Map<String, Pos> = mk(@Int.0);
  7
}
"""


_HALT_HARVEST = """\
public fn g(@Int -> @Int)
  requires(true)
  ensures(@Int.0 > 0)
  effects(<Random>)
{
  let @Int = Random.random_int(0 - 9, 0 - 1);
  assert(@Int.0 > 0);
  7
}
"""


def test_a_fact_past_an_uncertain_binding_is_not_harvested(
    tmp_path: Path,
) -> None:
    """HALT: stop reading a block once its env is uncertain (R-1412 N1).

    `_collect_top_level_assert_facts` harvests `assert` / `assume`
    predicates and pushes them as path conditions over the POSTCONDITION
    and the refined return.  That consumer is what makes this policy
    observable, and it is why two earlier attempts to pin HALT failed:
    both varied the fixture while aiming at construction stores and call
    preconditions, which never read these facts at all.  The discriminator
    has to be chosen from the consumer backwards.

    Here the block rebinds `@Int` to a value the SMT layer cannot
    translate and which is always negative, then asserts `@Int.0 > 0`
    about that LOCAL.  Under `SKIP` the uncertain binding leaves the
    parameter visible, so the assert is harvested as a fact about the
    PARAMETER and discharges `ensures(@Int.0 > 0)` on the return —
    `verified`, for a postcondition the program never established, with
    `vera run --fn g -- -3` reaching an `unreachable` instruction against
    that Tier-1 claim.  `HALT` refuses to read past the uncertainty, so
    the postcondition is refuted instead.

    The ENSURES status is the assertion: the `assert` itself is Tier 3
    either way, so a cell watching it — or watching `ok` alone — would
    pass under both policies.
    """
    obs, envelope = _obligations(
        tmp_path, _HALT_HARVEST, name="haltharvest.vera")
    ensures = [o["status"] for o in obs if o["kind"] == "ensures"]
    assert ensures == ["violated"], (
        f"a fact about the block-local was harvested as a fact about the "
        f"parameter it shadowed, and discharged the postcondition from it: "
        f"{obs}"
    )
    assert envelope["ok"] is False
    _assert_partition(envelope)


_DESTR_POSITIVE = _PRELUDE + """\
private fn src(@Unit -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{
  Tuple(5, 7)
}

private fn ins(@Unit -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = src(());
  map_insert(map_new(), "a", @Int.0)
}

public fn f(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  map_size(ins(()))
}
"""


_DESTR_SELF_SUB = _PRELUDE + """\
private fn src(@Unit -> @Tuple<Int, Int>)
  requires(true) ensures(true) effects(pure)
{
  Tuple(5, 7)
}

private fn ins(@Unit -> @Map<String, Pos>)
  requires(true) ensures(true) effects(pure)
{
  let Tuple<@Int, @Int> = src(());
  map_insert(map_new(), "a", @Int.0 - @Int.0)
}

public fn f(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  map_size(ins(()))
}
"""


class TestAStoreAfterADestructureIsStillRecorded:
    """A destructuring `let` must not silence the tail's store.

    The descent first DECLINED to descend past a `let Ctor<...> = ...`,
    which was fail-closed against proving anything but left the store with
    no record at all — while codegen guards it from the site table either
    way.  Measured at that point: 1, 1 and 2 `contract_fail` in the module
    against zero obligations, which is the guard-WITHOUT-record desync this
    PR closes everywhere else.  So the descent shadows each binder and
    keeps going, and these cells hold the two directions apart.
    """

    def test_a_literal_component_still_proves_the_predicate(
        self, tmp_path: Path,
    ) -> None:
        """A projected literal binder is Tier 1, not a refusal.

        `Tuple(5, 7)` binds a `5` that proves `> 0`.  Shadowing every
        binder unconditionally — the first shape of this fix — recorded
        `violated` / E505 here for a program that runs clean, which is the
        same false refusal the block-tail fix had just removed one
        statement over.  Literal components are therefore translated in the
        pre-destructure env; only what does not translate goes opaque.
        """
        obs, envelope = _obligations(
            tmp_path, _DESTR_LITERAL, name="destrlit.vera")
        assert _store_status(obs) == [("verified", None)], (
            f"the binder is the literal `5`, which proves the predicate: "
            f"{obs}"
        )
        assert envelope["ok"] is True
        _assert_partition(envelope)

    def test_a_positive_source_is_not_refused(self, tmp_path: Path) -> None:
        """The cell that would have caught the over-shoot (R-1412).

        `src` returns `Tuple(5, 7)` and the tail stores a component into a
        `Pos` map value.  The program is CORRECT and runs clean, and the
        first shape of the destructure fix reported `violated` / E505 for
        it — because rebinding pushed a translatable fresh var, so Z3 was
        handed a real unconstrained term and duly produced a countermodel
        that names no value `src` can return.

        Every other destructure cell here uses a source that genuinely
        violates, which is precisely why none of them could see it:
        "correctly refuted" and "unconditionally refused" are the same
        observation on a negative source.  The discriminator is a positive
        one, and the tell was that a negative source produced a
        byte-identical stream.  The store runs, so the cell asserts the run
        as well as the status.
        """
        obs, envelope = _obligations(
            tmp_path, _DESTR_POSITIVE, name="destrpos.vera")
        status = _store_status(obs)
        assert ("violated", "E505") not in status, (
            f"a program whose source returns `Tuple(5, 7)` was refused: "
            f"{obs}"
        )
        assert status == [("tier3", "E506")], (
            f"the component is opaque to the translator, so the store is "
            f"Tier 3 — the same answer the plain-`let` path gives: {obs}"
        )
        assert envelope["ok"] is True
        out = _run(tmp_path, _DESTR_POSITIVE, "--fn", "f",
                   name="destrposrun.vera")
        assert "1" in out, (
            f"the fixture must actually run, or its status proves nothing "
            f"about a correct program:\n{out}"
        )
        _assert_partition(envelope)

    def test_a_violation_that_holds_for_every_value_still_refutes(
        self, tmp_path: Path,
    ) -> None:
        """Embedding a placeholder is not the same as depending on it.

        `@Int.0 - @Int.0` over an opaque component is 0 whatever the
        component turns out to be, so `> 0` fails for EVERY assignment and
        the refutation is real — the program traps.  Withdrawing it would
        lose a refusal the compiler can make on a program it can prove
        wrong, which is what a discharge keyed on "does this term embed a
        shadow" did (R-1412 N6).

        So the discharge is keyed on the narrower question: is the
        predicate satisfiable for SOME value the placeholder could take?
        Satisfiable means the countermodel picked one particular
        unreachable value and Tier 3 is right; unsatisfiable means it holds
        of all of them.  This cell is the second half of that pair — its
        sibling above is a correct program that must NOT be refused, and
        only the two together distinguish the criterion from either blanket
        answer.
        """
        obs, envelope = _obligations(
            tmp_path, _DESTR_SELF_SUB, name="destrselfsub.vera")
        store = [(o["status"], o.get("error_code")) for o in obs
                 if o["kind"] == "refine_bind"
                 and o["description"] == "@Int.0 - @Int.0"]
        assert store == [("violated", "E505")], (
            f"`@Int.0 - @Int.0` is 0 for every value of an opaque "
            f"component, so the violation holds always and is not a "
            f"spurious countermodel: {obs}"
        )
        assert envelope["ok"] is False
        out = _run(tmp_path, _DESTR_SELF_SUB, "--fn", "f",
                   name="destrselfsubrun.vera")
        assert _REFINE_TRAP in out, (
            f"the refuted program must actually trap, or the refusal is "
            f"the verifier being wrong in the other direction:\n{out}"
        )
        _assert_partition(envelope)

    def test_an_opaque_binder_does_not_inherit_the_outers_bound(
        self, tmp_path: Path,
    ) -> None:
        """A non-literal source is opaque, and opaque must not prove.

        `mk` carries `requires(@Int.0 > 0)` and the destructure rebinds
        `@Int` from a CALL, which the projection cannot see into.  If the
        binder were left resolving to the parameter, the outer's bound
        would discharge the store's predicate — a Tier-1 claim about a
        value the destructure replaced.  It is refuted instead, and the
        program really does trap: `src` returns `0 - @Int.0`, negative for
        every positive input.

        Skipping the shadow reds this cell, which is what makes the
        placeholder load-bearing rather than decorative.

        Tier 3, not a refusal: see
        :py:meth:`TestAStoreAfterADestructureIsStillRecorded.test_a_positive_source_is_not_refused`
        for the program this distinction protects.
        """
        obs, envelope = _obligations(
            tmp_path, _DESTR_OPAQUE, name="destropaque.vera")
        status = _store_status(obs)
        assert ("verified", None) not in status, (
            f"the outer `requires` discharged a predicate about a value the "
            f"destructure rebound: {obs}"
        )
        assert status == [("tier3", "E506")], (
            f"the binder is opaque, so the predicate is neither provable "
            f"nor refutable and the store is Tier 3: {obs}"
        )
        _assert_partition(envelope)

    @pytest.mark.parametrize(
        ("label", "source"),
        [("literal", _DESTR_LITERAL), ("opaque", _DESTR_OPAQUE)],
        ids=["literal", "opaque"],
    )
    def test_the_store_is_recorded_wherever_it_is_guarded(
        self, tmp_path: Path, label: str, source: str,
    ) -> None:
        """Guard parity at the site: a guarded store carries a record.

        The desync this arm fixes is one-sided — codegen emitted the
        §2.6.5 guard while the verifier recorded nothing — so the cell
        asserts the pairing rather than either side alone: the module
        guards the store, and the obligation stream has an entry for it.
        A future change that silences the descent again reds here even if
        every status above still reads plausibly.
        """
        obs, _ = _obligations(tmp_path, source, name=f"parity_{label}.vera")
        assert _store_status(obs), (
            f"the store past a destructure carries no record at all: {obs}"
        )
        wat = _cli("compile", "--wat",
                   str(_write(tmp_path, source, f"parity_{label}w.vera")))
        assert wat.returncode == 0, wat.stderr[-400:]
        body = wat.stdout.split("(func $mk")[1].split("(func ")[0]
        assert "call $vera.contract_fail" in body, (
            f"the verifier recorded a store the module does not guard — "
            f"the parity this PR exists to hold:\n{body[:400]}"
        )


def test_a_call_pre_is_reported_once_per_call_site(tmp_path: Path) -> None:
    """One call site, one `call_pre` record and one E532 (#1459).

    `_report_call_demotions` runs TWICE per function, so a call appearing
    only in a later clause is not lost, and each run DRAINS the demotion
    list — so no key applied inside that list can see across the two, and a
    call TRANSLATED a second time in a later phase arrives looking like a
    new one.  Two routes reach that: the construction descent asks an arm's
    scrutinee for its path fact, and #1420's call-argument walk
    re-translates the call (bisected: `35ff4def` is where this program's
    duplicate appears).

    The record double-counts in `tier3_runtime` and the warning is shown to
    the user twice, so this is not an internal accounting detail.  Both
    halves are asserted, because a fix that deduped only the obligation
    would leave the doubled warning on screen.
    """
    obs, envelope = _obligations(
        tmp_path, _1459_GENERIC_CALLEE, name="dupe1459.vera")
    assert len(_call_pre_lines(obs)) == 1, (
        f"the precondition of one call site is recorded more than once: "
        f"{_call_pre_lines(obs)}"
    )
    codes = [w.get("error_code") for w in envelope.get("warnings", [])]
    assert codes.count("E532") == 1, (
        f"the E532 demotion is user-visible, so a second copy is a second "
        f"warning on the same line: {codes}"
    )
    tier3_call_pre = [o for o in obs
                      if o.get("kind") == "call_pre"
                      and o.get("status") == "tier3"]
    assert len(tier3_call_pre) == 1, (
        f"a duplicated Tier-3 call_pre inflates the runtime-check count a "
        f"consumer reads: {tier3_call_pre}"
    )
    _assert_partition(envelope)


def test_two_call_sites_of_one_generic_keep_two_records(
    tmp_path: Path,
) -> None:
    """The non-merge direction: dedup must not collapse distinct sites.

    A dedup keyed on the call site is only correct if it still tells two
    sites apart, so this asserts the shape the fix must NOT reach — two
    calls to the same `forall` callee, which stay two records.

    It also pins what one call site under TWO monomorphic instances does.
    `wrap` is instantiated at `Int` and at `String`, and the single `head`
    call inside it records ONCE, not once per instance — measured
    identically on this PR's base, so it is the aggregation's long-standing
    behaviour and not something the dedup here introduced.  That is the
    answer to "can two instances at one site legitimately differ": they do
    not reach the stream separately at all, so there is no such shape to
    preserve.
    """
    obs, envelope = _obligations(
        tmp_path, _1459_TWO_INSTANCES, name="twoinst1459.vera")
    sites = [((o.get("location") or {}).get("line"),
              (o.get("location") or {}).get("column"))
             for o in obs if o.get("kind") == "call_pre"]
    # Positions are read from the stream rather than written in, so the
    # cell keeps meaning if the fixture moves a line.
    assert len(set(sites)) == len(sites), (
        f"a call site is recorded twice: {sites}"
    )
    assert len(sites) == 3, (
        f"expected the `head` call plus BOTH `wrap` calls: {sites}"
    )
    caller_line = max(ln for ln, _ in sites)
    assert sum(1 for ln, _ in sites if ln == caller_line) == 2, (
        f"the two DISTINCT `wrap` call sites must keep two records — a "
        f"site-keyed dedup that merged them would lose one: {sites}"
    )
    inner = [s for s in sites if s[0] != caller_line]
    assert len(inner) == 1, (
        f"the one `head` call under two instantiations records once, as it "
        f"does on this PR's base: {sites}"
    )
    codes = [w.get("error_code") for w in envelope.get("warnings", [])]
    assert codes.count("E532") == 3, (
        f"one warning per recorded site, no more: {codes}"
    )
    _assert_partition(envelope)


def test_a_match_arm_binder_is_not_the_outer_parameter(
    tmp_path: Path,
) -> None:
    """The arm's ENV has to reach the store, and this direction is the unsound one.

    `@Int.0` inside `Some(@Int) ->` is the pattern-bound payload, not the
    parameter one frame out.  Descending with the OUTER env reattributes it
    silently: `requires(@Int.0 > 0)` then discharges a payload carrying no
    such bound and the obligation records `verified` — a Tier 1 claim for a
    predicate `Some(0 - 5)` refutes at run time.  Measured when the descent
    first reached match arms: `verified`, while the artifact trapped on that
    input, because codegen guards the store from the site table whatever the
    verifier concluded.  That gap is the #680 misattribution class one
    container level in, and it is the reason this cell asserts the STATUS
    and not just the presence of a record: silence was the old bug, but a
    wrong `verified` is worse than silence.
    """
    obs, envelope = _obligations(
        tmp_path, _CR_MATCH_BINDER_IS_NOT_THE_PARAMETER,
        name="binderenv.vera")
    stores = [(o["status"], o.get("error_code")) for o in obs
              if o["kind"] == "refine_bind" and o["description"] == "@Int.0"]
    assert stores == [("violated", "E505")], (
        f"the arm's `@Int.0` is the `Some` payload, which carries no bound; "
        f"a `verified` here is the outer parameter's `requires` discharging "
        f"another slot's obligation: {obs}"
    )
    _assert_partition(envelope)
