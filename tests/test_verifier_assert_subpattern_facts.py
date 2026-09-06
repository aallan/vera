"""A match arm's `assert` reads the facts the arm establishes (#1403).

Three walks descend a `match` arm and each one wants the same thing: the
declared-type facts a constructor sub-pattern's bindings carry.  The narrowing
walk seeds them, so a downstream `@Nat` narrowing of a bound payload
discharges.  `_walk_for_calls` seeds them, so a call precondition in the arm
body discharges.  The primitive-op walk — which is where a body `assert(P)` is
proved — never did, so an assertion that follows directly from a bound
payload's declared type could not be proved and always fell to a runtime check
(`tier3` + E535), whatever the callee did.

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
