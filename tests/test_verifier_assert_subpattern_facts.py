"""Every obligation in a match arm reads the facts that arm establishes (#1403).

Three walks descend a `match` arm and each one wants the same thing: the
declared-type facts a constructor sub-pattern's bindings carry.  The narrowing
walk (`_obligate_subpattern_narrowings`) seeds them, so a downstream `@Nat`
narrowing of a bound payload discharges.  `SmtContext._arm_source_facts` —
reached from `_translate_match` through the sub-pattern fact hook, and NOT
`_walk_for_calls`, whose own match descent seeds only path conditions and
whose sole caller serves `decreases` — seeds them, so a call precondition in
the arm body discharges.  The primitive-operation walk, which discharges every
§6.4.3 safety obligation AND every body `assert(P)`, never did.

So an assertion that follows directly from a bound payload's declared type
could not be proved and always fell to a runtime check (`tier3` + E535), and
`Some(@PosInt) -> 100 / @PosInt.0` was refused E526 although the payload's own
type says the divisor is positive.  The reach of the fix is every obligation
the walk discharges, deliberately: one arm establishes one set of facts, and a
`/`, an `arr[i]` and an `assert` in it are all discharged from the same
context.  A safety obligation demoted because the producer was disclosed
carries E534 and its warning — a `tier3` that no diagnostic surfaces would
break the accounting `verify --json` documents, and that was the shape of the
regression the review of PR #1415 found.

Completeness, not soundness: E535 is the honest conservative answer, and the
§11.14.1 `unreachable` trap really does back it.  The cost was an unnecessary
Tier-3 on an assertion the run had everything it needed to discharge — and,
secondarily, that the assert's verdict in the disclosed case was right by
coincidence rather than by the rule.

The fix seeds the SAME pure helper the other two walks use, which is what
makes the disclosure rule reach the assert for free: where the callee's own
obligation was disclosed, the helper routes its facts to `_tainted_facts` and
returns none, so `check_valid` withholds them and the honest E535 stays.

Four quadrants, and only two of them are red-first.  `clean` x {one file,
imported} flip `tier3`/E535 -> `verified`; `disclosed` x {one file, imported}
are CONTROLS that read the same before and after, and they earn their place by
failing the over-reach mutation (a fix that seeded facts without the taint
check turns both green-to-red).  The imported quadrants depend on #1399's
manifest, which is why this branch stacks on that one: without it the imported
disclosed callee's facts are not withheld at all and the fourth quadrant
becomes a false Tier-1.
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


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=600,
    )


def _tree(tmp_path: Path, files: dict[str, str]) -> dict[str, Path]:
    tmp_path.mkdir(parents=True, exist_ok=True)
    out: dict[str, Path] = {}
    for name, text in files.items():
        p = tmp_path / f"{name}.vera"
        p.write_text(text, encoding="utf-8")
        out[name] = p
    return out


def _verify(path: Path) -> dict:
    proc = _cli("verify", "--json", str(path))
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope for {path.name} "
            f"(exit {proc.returncode})\n{proc.stdout[:400]}\n"
            f"{proc.stderr[-800:]}"
        ) from None
    # A bare call to a name that does not resolve is E200, a WARNING — so a
    # fixture with a typo in a callee still verifies, and every assertion
    # below is then made about a program that does not do what it reads as
    # doing.  One such typo (`int_to_nat_or`) survived a first draft of this
    # file and made the three-consumers cell measure nothing.
    unresolved = [
        w for w in result.get("warnings", [])
        if w.get("error_code") == "E200"
    ]
    assert not unresolved, (
        f"{path.name}: fixture names a function that does not resolve — "
        f"{[w['description'] for w in unresolved]}"
    )
    return result


def _triples(result: dict) -> list[tuple[str, str, str | None]]:
    return [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ]


def _asserts(result: dict) -> list[tuple[str, str | None]]:
    return [
        (o["status"], o.get("error_code"))
        for o in result["obligations"] if o["kind"] == "assert"
    ]


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

#: `mk`'s `@Nat` handler-clause binder is unguarded, so this module's own run
#: reports `nat_bind` / `tier3_unguarded` / E504 — the disclosure the two
#: control quadrants rest on.
_DISCLOSING_MK = """\
{vis} fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  int_to_nat(handle[Exn<Int>] {{
    throw(@Nat) -> {{ nat_to_int(@Nat.0) }}
  }} in {{
    throw(@Int.0)
  }})
}}
"""

_CLEAN_MK = """\
{vis} fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  int_to_nat(@Int.0)
}}
"""

#: The assertion follows directly from the bound payload's declared type: the
#: field is `Nat`, and `nat_to_int` of a `Nat` is `>= 0`.
_USE_ASSERT = """\
public fn use_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match {call}(@Int.0) {{
    Some(@Nat) -> {{
      assert(nat_to_int(@Nat.0) >= 0);
      1
    }},
    None -> 0
  }}
}}
"""


def _one_file(kind: str) -> dict[str, str]:
    body = _DISCLOSING_MK if kind == "disclosed" else _CLEAN_MK
    return {
        "single": body.format(vis="private") + "\n"
        + _USE_ASSERT.format(call="mk"),
    }


def _imported(kind: str) -> dict[str, str]:
    body = _DISCLOSING_MK if kind == "disclosed" else _CLEAN_MK
    return {
        "lib": body.format(vis="public"),
        "main": "import lib;\n\n" + _USE_ASSERT.format(call="lib::mk"),
    }


# ---------------------------------------------------------------------------
# The four quadrants
# ---------------------------------------------------------------------------

def test_1403_one_file_clean_callee_proves_the_assert(tmp_path: Path) -> None:
    """RED before: the assertion the arm's own type establishes must prove.

    `@Nat` is bound off an `Option<Nat>` field, so `nat_to_int(@Nat.0) >= 0`
    is exactly what that field's declared type says. Reported runtime-checked,
    it costs a Tier-3 and a trap for a fact the run already had.
    """
    result = _verify(_tree(tmp_path, _one_file("clean"))["single"])
    assert _asserts(result) == [("verified", None)], _triples(result)


def test_1403_imported_clean_callee_proves_the_assert(tmp_path: Path) -> None:
    """RED before, and the import must not change the answer.

    The field's declared type is the callee's contract surface, which crosses
    an import intact — so the same program split in two has to prove the same
    assertion.
    """
    result = _verify(_tree(tmp_path, _imported("clean"))["main"])
    assert _asserts(result) == [("verified", None)], _triples(result)


def test_1403_one_file_disclosed_callee_keeps_the_runtime_check(
    tmp_path: Path,
) -> None:
    """CONTROL: a fact the run could neither prove nor guard stays withheld.

    Green before and after — before because the assert read nothing at all,
    after because the helper routes a disclosed callee's facts to
    `_tainted_facts` and returns none. The status is the same; the reason is
    not, which is the point. It earns its keep against the over-reach
    mutation: a fix that seeded the facts directly, bypassing the taint check,
    turns this cell red.
    """
    result = _verify(_tree(tmp_path, _one_file("disclosed"))["single"])
    assert _asserts(result) == [("tier3", "E535")], _triples(result)
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(result), (
        "the fixture stopped disclosing, so this control is vacuous"
    )


def test_1403_imported_disclosed_callee_keeps_the_runtime_check(
    tmp_path: Path,
) -> None:
    """CONTROL, and the reason this branch stacks on #1399's manifest.

    Without that manifest the imported disclosure is invisible, the facts are
    handed over, and this assert proves — a Tier-1 claim resting on a fact
    `vera verify lib.vera` reports as `tier3_unguarded`/E504. Measured on
    `release/v0.2.0` + this change alone, it reads `verified`; on this stack
    it reads `tier3`/E535.
    """
    paths = _tree(tmp_path, _imported("disclosed"))
    lib = _verify(paths["lib"])
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(lib), (
        "the library stopped disclosing, so this control is vacuous"
    )
    result = _verify(paths["main"])
    assert _asserts(result) == [("tier3", "E535")], _triples(result)


# ---------------------------------------------------------------------------
# Over-acceptance controls: the arm establishes SOME facts, not any fact
# ---------------------------------------------------------------------------

_ASSERT_TOO_STRONG = """\
private fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(@Int.0)
}

public fn use_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Nat) -> {
      assert(nat_to_int(@Nat.0) > 5);
      1
    },
    None -> 0
  }
}
"""


def test_1403_a_fact_the_declared_type_does_not_give_still_falls_back(
    tmp_path: Path,
) -> None:
    """The arm establishes `>= 0`, and `> 5` does not follow from it.

    Without this, "seed the arm's facts" could be read as "assume whatever the
    assert says", which would make every assertion Tier-1 and the construct
    meaningless.
    """
    result = _verify(_tree(tmp_path, {"strong": _ASSERT_TOO_STRONG})["strong"])
    assert _asserts(result) == [("tier3", "E535")], _triples(result)


_ASSERT_REFUTED = """\
private fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(@Int.0)
}

public fn use_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Nat) -> {
      assert(nat_to_int(@Nat.0) < 0);
      1
    },
    None -> 0
  }
}
"""


def test_1403_a_refuted_assert_is_still_loud(tmp_path: Path) -> None:
    """An assertion the new facts REFUTE must stay an error, not soften.

    `nat_to_int(@Nat.0) < 0` is false in every reachable state once the arm's
    fact is in scope, which is exactly the E507 case — and the new facts make
    it MORE refutable, not less. A fix that only ever added assumptions to the
    positive check would leave this Tier-3.
    """
    result = _verify(_tree(tmp_path, {"refuted": _ASSERT_REFUTED})["refuted"])
    codes = [d.get("error_code") for d in result["diagnostics"]]
    assert "E507" in codes, (codes, _triples(result))
    assert ("assert", "violated", "E507") in _triples(result), _triples(result)


_ASSERT_BINDING_ARM = """\
private fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(@Int.0)
}

public fn use_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    _ -> {
      assert(@Int.0 == @Int.0);
      1
    }
  }
}
"""


def test_1403_a_non_constructor_arm_is_unaffected(tmp_path: Path) -> None:
    """A wildcard arm binds no sub-pattern, so there are no facts to seed.

    The seeding is guarded on the arm's pattern being a constructor pattern;
    this pins that the guard holds rather than throwing on the other shapes.
    """
    result = _verify(_tree(tmp_path, {"bind": _ASSERT_BINDING_ARM})["bind"])
    assert result["ok"] is True, result["diagnostics"]
    assert _asserts(result) == [("verified", None)], _triples(result)


# ---------------------------------------------------------------------------
# One derivation, three consumers
# ---------------------------------------------------------------------------

_TWO_CONSUMERS = """\
{vis} fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}

private fn needs_nonneg(@Int -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  effects(pure)
{{
  @Int.0
}}

public fn via_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@Nat) -> {{
      assert(nat_to_int(@Nat.0) >= 0);
      1
    }},
    None -> 0
  }}
}}

public fn via_call(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@Nat) -> needs_nonneg(nat_to_int(@Nat.0)),
    None -> 0
  }}
}}
"""

_DISCLOSING_BODY = (
    "int_to_nat(handle[Exn<Int>] {\n"
    "    throw(@Nat) -> { nat_to_int(@Nat.0) }\n"
    "  } in {\n"
    "    throw(@Int.0)\n"
    "  })"
)


def test_1403_the_assert_and_the_call_precondition_now_agree(
    tmp_path: Path,
) -> None:
    """The two consumers of one derivation must move together.

    An `assert(P)` and a call precondition `requires(P)` over the same bound
    payload are the same question asked twice.  Before this change they
    disagreed: the precondition discharged at Tier 1 from the arm's facts
    while the assert fell to a runtime check, because only one of the two
    walks had been wired to the source.  Both polarities are asserted, so a
    fix that made them agree by making the precondition WORSE fails too.

    In SEPARATE functions, deliberately.  Put the assert before the call in
    one body and §6.4.1's rule takes over — a prior `assert` strengthens the
    context for what follows, so the precondition discharges from the assert
    rather than from the arm, and the disclosed leg measures nothing.  (That
    is how a first draft of this cell passed while proving nothing.)

    A discharged precondition records no obligation — the stream carries
    `call_pre` only when it is demoted — so the clean leg is the ABSENCE of a
    demoted `call_pre` beside a verified assert, and the disclosed leg is the
    presence of both demotions together.
    """
    clean = _verify(_tree(tmp_path / "c", {
        "p": _TWO_CONSUMERS.format(vis="private", body="int_to_nat(@Int.0)"),
    })["p"])
    assert _asserts(clean) == [("verified", None)], _triples(clean)
    assert not [
        o for o in clean["obligations"] if o["kind"] == "call_pre"
    ], _triples(clean)

    disclosed = _verify(_tree(tmp_path / "d", {
        "p": _TWO_CONSUMERS.format(vis="private", body=_DISCLOSING_BODY),
    })["p"])
    assert _asserts(disclosed) == [("tier3", "E535")], _triples(disclosed)
    assert ("call_pre", "tier3", "E532") in _triples(disclosed), (
        f"the precondition site is not live in the disclosed fixture, so the "
        f"agreement this cell claims is unmeasured: {_triples(disclosed)}"
    )


# ---------------------------------------------------------------------------
# The accounting identity, on the programs whose statuses this change moves
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "files,entry",
    [
        pytest.param(_one_file("clean"), "single", id="one-file-clean"),
        pytest.param(_one_file("disclosed"), "single", id="one-file-disclosed"),
        pytest.param(_imported("clean"), "main", id="imported-clean"),
        pytest.param(_imported("disclosed"), "main", id="imported-disclosed"),
    ],
)
def test_1403_json_accounting_identity(
    tmp_path: Path, files: dict[str, str], entry: str,
) -> None:
    """`len(obligations) == total + violated + tier3_unguarded`, per CLAUDE.md.

    This change moves an obligation from `tier3` to `verified`, which shifts
    it between summary buckets; the partition is re-asserted on exactly the
    programs it moves, over the `verify --json` envelope a consumer reads.
    """
    result = _verify(_tree(tmp_path, files)[entry])
    v = result["verification"]
    obls = result["obligations"]
    uncounted = sum(
        1 for o in obls if o["status"] in ("violated", "tier3_unguarded")
    )
    assert v["total"] == v["tier1_verified"] + v["tier3_runtime"], v
    assert len(obls) == v["total"] + uncounted, (
        f"{len(obls)} != total={v['total']} + {uncounted}: {_triples(result)}"
    )


# ---------------------------------------------------------------------------
# The rule is about the arm's OBLIGATIONS, not only its assertions
# ---------------------------------------------------------------------------

#: A refined payload whose predicate is exactly what a `/` needs.
_DIV_PROGRAM = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

private fn mk(@Int -> @Option<PosInt>)
  requires({req})
  ensures(true)
  effects(pure)
{{
  {body}
}}

public fn use_op(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@PosInt) -> 100 / @PosInt.0,
    None -> 0
  }}
}}
"""

#: ... and one whose predicate is exactly what an index needs.
_IDX_PROGRAM = """\
type Small = {{ @Nat | @Nat.0 < 3 }};

private fn mk(@Nat -> @Option<Small>)
  requires({req})
  ensures(true)
  effects(pure)
{{
  {body}
}}

public fn use_op(@Nat -> @Int)
  requires(@Nat.0 < 3)
  ensures(true)
  effects(pure)
{{
  match mk(@Nat.0) {{
    Some(@Small) -> [10, 20, 30][@Small.0],
    None -> 0
  }}
}}
"""

_CLEAN_PRODUCER = "Some(@{slot}.0)"
_DISCLOSED_PRODUCER = (
    "Some(handle[Exn<{base}>] {{ throw(@{ty}) -> {{ @{ty}.0 }} }} "
    "in {{ throw(@{base}.0) }})"
)


def _op_program(template: str, *, ty: str, base: str, disclosed: bool) -> str:
    if disclosed:
        return template.format(
            req="true",
            body=_DISCLOSED_PRODUCER.format(ty=ty, base=base),
        )
    guard = "@Int.0 > 0" if base == "Int" else "@Nat.0 < 3"
    return template.format(
        req=guard, body=_CLEAN_PRODUCER.format(slot=base),
    )


@pytest.mark.parametrize(
    "template,ty,base,kind",
    [
        pytest.param(_DIV_PROGRAM, "PosInt", "Int", "div_zero", id="div-zero"),
        pytest.param(_IDX_PROGRAM, "Small", "Nat", "index_bounds", id="index"),
    ],
)
def test_1403_a_clean_arm_discharges_a_primitive_op_obligation(
    tmp_path: Path, template: str, ty: str, base: str, kind: str,
) -> None:
    """The reach is deliberate: EVERY obligation in the arm reads its facts.

    `assert` is not a special case — a `/` or an `arr[i]` in the same arm is
    discharged from the same context, and the arm's declared-type facts are
    part of it.  `100 / @PosInt.0` where the payload's type says `> 0` is a
    *false positive* until the divisor's own type is in scope: `release/v0.2.0`
    refuses this program with `E526`.
    """
    source = _op_program(template, ty=ty, base=base, disclosed=False)
    result = _verify(_tree(tmp_path, {"p": source})["p"])
    assert result["ok"] is True, result["diagnostics"]
    ops = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == kind
    ]
    assert ops == [("verified", None)], _triples(result)


@pytest.mark.parametrize(
    "template,ty,base,kind",
    [
        pytest.param(_DIV_PROGRAM, "PosInt", "Int", "div_zero", id="div-zero"),
        pytest.param(_IDX_PROGRAM, "Small", "Nat", "index_bounds", id="index"),
    ],
)
def test_1403_a_disclosed_arm_demotes_it_and_says_so(
    tmp_path: Path, template: str, ty: str, base: str, kind: str,
) -> None:
    """... and a demoted safety obligation must carry its code and a warning.

    This is the regression the review found (F1).  With a disclosed producer
    the divisor really can be zero — the payload's `refine_bind` is
    `tier3_unguarded`/E506, so nothing guards it — and the program went from
    a refused `E526` to `ok: true` carrying a `div_zero`/`tier3` with **no
    error code and no warning of its own**.  A `tier3` nothing surfaces also
    breaks the `verify --json` partition table's own contract.

    Both halves are asserted: the obligation carries E534, and the warning
    stream carries it too — a code recorded on the obligation but never
    emitted would still leave the reader with a silent runtime check.
    """
    source = _op_program(template, ty=ty, base=base, disclosed=True)
    result = _verify(_tree(tmp_path, {"p": source})["p"])
    ops = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == kind
    ]
    assert ops == [("tier3", "E534")], _triples(result)
    codes = [w.get("error_code") for w in result["warnings"]]
    assert "E534" in codes, codes
    # The producer's own disclosure is in the same stream: this is the
    # unguarded case, which is why the demotion is the honest answer.
    assert ("refine_bind", "tier3_unguarded", "E506") in _triples(result), (
        _triples(result)
    )


def test_1403_the_demotion_names_the_operation_not_a_contract(
    tmp_path: Path,
) -> None:
    """The E534 text says which obligation moved.

    One emitter serves the contract and safety paths, so the subject has to
    come from the caller; a shared message reading "Postcondition in …" over
    a division would send the reader to the wrong line.
    """
    source = _op_program(_DIV_PROGRAM, ty="PosInt", base="Int", disclosed=True)
    result = _verify(_tree(tmp_path, {"p": source})["p"])
    e534 = [w for w in result["warnings"] if w.get("error_code") == "E534"]
    assert len(e534) == 1, [w.get("error_code") for w in result["warnings"]]
    text = e534[0]["description"]
    assert text.startswith("Division in 'use_op'"), text
    assert "runtime trap" in text, text
    assert "Postcondition" not in text, text


# ---------------------------------------------------------------------------
# What holds the new Tier-1 up, and where that support runs out
# ---------------------------------------------------------------------------

_NESTED = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

private fn mk(@Int -> @Option<Option<PosInt>>)
  requires({req})
  ensures(true)
  effects(pure)
{{
  {body}
}}

public fn use_nested(@Int -> @Int)
  requires({req})
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(Some(@PosInt)) -> {arm},
    Some(None) -> 1,
    None -> 1
  }}
}}
"""

_NESTED_CLEAN = ("@Int.0 > 0", "Some(Some(@Int.0))")
_NESTED_DISCLOSED = ("true", (
    "Some(Some(handle[Exn<Int>] { throw(@PosInt) -> { @PosInt.0 } } "
    "in { throw(@Int.0) }))"
))


@pytest.mark.parametrize(
    "arm,kind,clean_code,disclosed_code",
    [
        pytest.param("{ assert(@PosInt.0 > 0); 1 }", "assert", None, "E535",
                     id="assert"),
        pytest.param("100 / @PosInt.0", "div_zero", None, "E534", id="div"),
    ],
)
def test_1403_a_nested_bind_carries_its_fact_in_both_polarities(
    tmp_path: Path, arm: str, kind: str, clean_code: str | None,
    disclosed_code: str,
) -> None:
    """`Some(Some(@PosInt))` — the shape with no codegen guard behind it.

    For a DIRECT sub-pattern bind codegen emits its own payload guard, so the
    arm's fact is true whenever the arm runs whatever the verifier recorded.
    For a NESTED bind that guard is not emitted — `_extract_constructor_fields`
    binds direct sub-patterns only, a #758-class deferral still open as #765 —
    so this change makes the nested fact a Tier-1 assumption with nothing
    behind it but the producer's own construction obligation (review of
    PR #1415, F3).

    Both polarities are pinned because the shape deserves to fail loudly if
    either half moves; the companion cell below shows why the clean half is
    sound rather than lucky.
    """
    req, body = _NESTED_CLEAN
    clean = _verify(_tree(tmp_path / "c", {
        "p": _NESTED.format(req=req, body=body, arm=arm)}
    )["p"])
    got = [
        (o["status"], o.get("error_code")) for o in clean["obligations"]
        if o["kind"] == kind
    ]
    assert got == [("verified", clean_code)], _triples(clean)

    req, body = _NESTED_DISCLOSED
    disclosed = _verify(_tree(tmp_path / "d", {
        "p": _NESTED.format(req=req, body=body, arm=arm)}
    )["p"])
    got = [
        (o["status"], o.get("error_code")) for o in disclosed["obligations"]
        if o["kind"] == kind
    ]
    assert got == [("tier3", disclosed_code)], _triples(disclosed)


def test_1403_a_nested_tier1_rests_on_the_producers_own_obligation(
    tmp_path: Path,
) -> None:
    """... and that obligation is enforced, so no false Tier 1 is reachable.

    The support for the nested Tier-1 is the producer's construction
    obligation, not a codegen guard.  This walks the whole route rather than
    asserting the claim: a producer that CANNOT discharge that obligation is
    refused outright (E505), so there is no verify-green path to a violating
    runtime value, and the one that can discharge it verifies and RUNS
    correctly.

    `vera run` rather than `vera verify` for the second leg deliberately —
    a Tier-1 claim about a value is only worth as much as the value the
    compiled program actually produces.
    """
    program = _NESTED.format(
        req="@Int.0 > 0", body="Some(Some(@Int.0))", arm="100 / @PosInt.0",
    ).replace("fn use_nested", "fn main")

    # Leg 1: the producer cannot discharge its own construction obligation.
    undischarged = program.replace(
        "requires(@Int.0 > 0)\n  ensures(true)\n  effects(pure)\n{\n  "
        "Some(Some(@Int.0))",
        "requires(true)\n  ensures(true)\n  effects(pure)\n{\n  "
        "Some(Some(@Int.0))", 1,
    )
    refused = _verify(_tree(tmp_path / "u", {"p": undischarged})["p"])
    assert refused["ok"] is False, _triples(refused)
    assert "E505" in [d.get("error_code") for d in refused["diagnostics"]], (
        refused["diagnostics"]
    )

    # Leg 2: the one that can, verifies AND produces the right value.
    path = _tree(tmp_path / "r", {"p": program})["p"]
    ok = _verify(path)
    assert ok["ok"] is True, ok["diagnostics"]
    proc = _cli("run", str(path), "--fn", "main", "--", "4")
    assert proc.returncode == 0, (proc.stdout, proc.stderr)
    assert proc.stdout.strip().endswith("25"), proc.stdout


# ---------------------------------------------------------------------------
# The boundary the four quadrants do NOT cover
# ---------------------------------------------------------------------------

_INDIRECT_MK = """\
private fn mk(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  int_to_nat(handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  })
}
"""

_LET_BOUND = _INDIRECT_MK + """
public fn use_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Nat> = mk(@Int.0);
  match @Option<Nat>.0 {
    Some(@Nat) -> { assert(nat_to_int(@Nat.0) >= 0); 1 },
    None -> 0
  }
}
"""

_WRAPPED = _INDIRECT_MK + """
private fn fwd(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(@Int.0)
}

public fn use_assert(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match fwd(@Int.0) {
    Some(@Nat) -> { assert(nat_to_int(@Nat.0) >= 0); 1 },
    None -> 0
  }
}
"""


@pytest.mark.parametrize(
    "source", [pytest.param(_LET_BOUND, id="let-bound"),
               pytest.param(_WRAPPED, id="wrapper")],
)
def test_1403_an_indirect_scrutinee_is_not_withheld_yet(
    tmp_path: Path, source: str,
) -> None:
    """PINNED AT TODAY'S BEHAVIOUR, and today's behaviour is not the rule.

    `_scrutinee_is_disclosed_call` recognises a literally spelled
    `FnCall`/`ModuleCall`.  Bind the same call to a `let`, or route it through
    a forwarding wrapper, and the disclosure does not reach the arm — so the
    facts are handed over and the assertion proves, beside a
    `nat_bind`/`tier3_unguarded`/E504 for the very fact it just assumed.

    Before this change the assert read no facts at all and was accidentally
    immune, so the four quadrants pin "the assert does not assume anything"
    only for the direct spelling (review of PR #1415, F2).  That gap is
    [#1406](https://github.com/aallan/vera/issues/1406) /
    [#1407](https://github.com/aallan/vera/issues/1407), being closed by
    #1418; when it lands these two flip to `tier3`/E535 and this cell should
    be rewritten to assert the demotion.  Until then it exists so the change
    cannot happen silently in either direction.
    """
    result = _verify(_tree(tmp_path / "pos", {"p": source})["p"])
    assert _asserts(result) == [("verified", None)], _triples(result)
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(result), (
        f"the producer stopped disclosing, so this pin is vacuous: "
        f"{_triples(result)}"
    )

    # BOTH polarities, because only one of them changes the exit code and a
    # one-sided pin would let the other flip in silence: with the predicate
    # negated, the same handed-over fact turns a runtime-checked assertion
    # into a refuted one — `ok: true` + `tier3`/E535 before this change,
    # `ok: false` + E507 after.  When #1418 withholds the fact for these
    # spellings this leg returns to `tier3`/E535, and that is the change the
    # cell exists to make visible.
    negated = source.replace("nat_to_int(@Nat.0) >= 0", "nat_to_int(@Nat.0) < 0")
    assert negated != source, "the negated variant must actually differ"
    neg = _verify(_tree(tmp_path / "neg", {"p": negated})["p"])
    assert neg["ok"] is False, _triples(neg)
    assert _asserts(neg) == [("violated", "E507")], _triples(neg)


# ---------------------------------------------------------------------------
# The remaining two sites the widened reach touches
# ---------------------------------------------------------------------------

_SUB = """\
type Big = {{ @Nat | @Nat.0 >= 10 }};

private fn mk(@Nat -> @Option<Big>)
  requires({req})
  ensures(true)
  effects(pure)
{{
  {body}
}}

public fn use_sub(@Nat, @Nat -> @Nat)
  requires(@Nat.0 <= 5 && @Nat.1 >= 10)
  ensures(true)
  effects(pure)
{{
  match mk(@Nat.1) {{
    Some(@Big) -> @Big.0 - @Nat.0,
    None -> 0
  }}
}}
"""

_OVF = """\
type Small = {{ @Int | @Int.0 > 0 && @Int.0 < 100 }};

private fn mk(@Int -> @Option<Small>)
  requires({req})
  ensures(true)
  effects(pure)
{{
  {body}
}}

public fn use_mul(@Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 100)
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@Small) -> @Small.0 * @Small.0,
    None -> 0
  }}
}}
"""

_SUB_CLEAN = ("@Nat.0 >= 10", "Some(@Nat.0)")
_SUB_DISCLOSED = ("true", (
    "Some(handle[Exn<Nat>] { throw(@Big) -> { @Big.0 } } in { throw(@Nat.0) })"
))
_OVF_CLEAN = ("@Int.0 > 0 && @Int.0 < 100", "Some(@Int.0)")
_OVF_DISCLOSED = ("true", (
    "Some(handle[Exn<Int>] { throw(@Small) -> { @Small.0 } } "
    "in { throw(@Int.0) })"
))


@pytest.mark.parametrize(
    "template,clean,disclosed,kind",
    [
        pytest.param(_SUB, _SUB_CLEAN, _SUB_DISCLOSED, "nat_sub", id="nat-sub"),
        pytest.param(_OVF, _OVF_CLEAN, _OVF_DISCLOSED, "int_overflow",
                     id="int-overflow"),
    ],
)
def test_1403_the_other_two_safety_sites_move_together(
    tmp_path: Path, template: str, clean: tuple[str, str],
    disclosed: tuple[str, str], kind: str,
) -> None:
    """`nat_sub` and `int_overflow`, the two sites the first round left unpinned.

    I claimed `nat_sub` was unreachable arm-scoped and was wrong: subtracting
    a SLOT rather than a literal reaches it, and on `release/v0.2.0` the clean
    shape is a false `('nat_sub','violated','E502')` — the arm's own
    `>= 10` versus `<= 5` decides it. `int_overflow` is `tier3` on base for
    both polarities and becomes Tier-1 for the clean one.

    Pinned in both polarities like `div_zero` and `index_bounds`, so all four
    sites `_record_undecided_safety` routes are covered by a cell rather than
    by the argument that they share a helper.
    """
    req, body = clean
    ok = _verify(_tree(tmp_path / "c", {
        "p": template.format(req=req, body=body)})["p"])
    assert ok["ok"] is True, ok["diagnostics"]
    assert [
        (o["status"], o.get("error_code")) for o in ok["obligations"]
        if o["kind"] == kind
    ] == [("verified", None)], _triples(ok)

    req, body = disclosed
    bad = _verify(_tree(tmp_path / "d", {
        "p": template.format(req=req, body=body)})["p"])
    assert [
        (o["status"], o.get("error_code")) for o in bad["obligations"]
        if o["kind"] == kind
    ] == [("tier3", "E534")], _triples(bad)
    assert "E534" in [w.get("error_code") for w in bad["warnings"]]


# ---------------------------------------------------------------------------
# A refuted premise is withheld too
# ---------------------------------------------------------------------------

_REFUTED = """\
type PosInt = {{ @Int | @Int.0 > 0 }};

private fn mk(@Int -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{{
  Some(@Int.0)
}}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@PosInt) -> {arm},
    None -> 1
  }}
}}
"""


def test_1403_a_refuted_premise_is_withheld_like_a_disclosed_one(
    tmp_path: Path,
) -> None:
    """The withholding keys on "not established", not on "disclosed".

    `mk` cannot discharge its own construction obligation — `refine_bind` is
    `violated`/E505, the run PROVED the payload need not be positive — and the
    arm was still handed the fact, so `100 / @PosInt.0` read `verified` beside
    a premise the same run disproved (review of PR #1415, G2).  "Could not
    establish" and "established the opposite" are different messages and the
    same decision: neither is a fact a caller may assume.

    The program is `ok: false` either way, which is why this hid — the E505
    dominates the exit code.  What must not happen is the obligation reading
    `verified`, and the message must not claim the run could neither prove nor
    guard something it refuted outright.
    """
    result = _verify(_tree(tmp_path, {
        "p": _REFUTED.format(arm="100 / @PosInt.0")})["p"])
    assert ("refine_bind", "violated", "E505") in _triples(result), (
        _triples(result)
    )
    assert ("div_zero", "tier3", "E534") in _triples(result), _triples(result)
    e534 = [w for w in result["warnings"] if w.get("error_code") == "E534"]
    assert len(e534) == 1, [w.get("error_code") for w in result["warnings"]]
    assert "proved FALSE" in e534[0]["description"], e534[0]["description"]


def test_1403_a_refuted_premise_does_not_prove_an_assert_either(
    tmp_path: Path,
) -> None:
    """... and the same for the assert, which is the other consumer."""
    result = _verify(_tree(tmp_path, {
        "p": _REFUTED.format(
            arm="{ assert(@PosInt.0 > 0); 1 }")})["p"])
    assert ("refine_bind", "violated", "E505") in _triples(result), (
        _triples(result)
    )
    assert ("assert", "tier3", "E535") in _triples(result), _triples(result)
