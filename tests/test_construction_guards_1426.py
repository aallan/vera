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

_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

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
