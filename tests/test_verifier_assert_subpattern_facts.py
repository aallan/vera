"""One derivation of what a `match` arm means, read by every walk (#1403).

Four walks descend a `match` arm, and each needs three things from it: the
slot env its pattern binds, the fact that this arm was taken, and the facts
the pattern ESTABLISHES — the declared-type guarantees its constructor
sub-pattern bindings carry.  Each walk assembled that context inline out of
the same three single derivations, so the four copies disagreed, and #1403 is
one disagreement out of that grid: the primitive-operation walk, which
discharges every §6.4.3 safety obligation AND every body `assert(P)`, asked
for the env and the discriminant and never for the facts, while a call
precondition in the same arm had them.

So an assertion that follows directly from a bound payload's declared type
could not be proved and always fell to a runtime check (`tier3` + E535), and
`Some(@PosInt) -> 100 / @PosInt.0` was refused E526 although the payload's own
type says the divisor is positive.  The reach of the fix is every obligation
in the arm, deliberately: one arm establishes one set of facts, and a `/`, an
`arr[i]` and an `assert` in it are all discharged from the same context.  A
safety obligation demoted because the producer was disclosed carries E534 and
its warning — a `tier3` that no diagnostic surfaces would break the accounting
`verify --json` documents, and that was the shape of the regression the review
of PR #1415 found.

`ContractVerifier._enter_match_arm` is now that one derivation, and closing
the class turned up two more of its cells, both shipped in v0.1.13 and
neither reported:

* the recursive-call walk behind `decreases` kept the ENCLOSING env when the
  scrutinee could not be translated, so a measure was proved against the
  parameter a binder shadows — a false Tier 1 its own runtime guard refutes
  on the first call; and
* the narrowing walk minted an untranslatable arm's binders UNTRACKED, so the
  gate that filters refutations over unreadable values never engaged and a
  correct program was refused E505.

Completeness, not soundness, for #1403 itself: E535 is the honest
conservative answer and the §11.14.1 `unreachable` trap really does back it.
The cost was an unnecessary Tier-3 on an assertion the run had everything it
needed to discharge — and, secondarily, that the assert's verdict in the
disclosed case was right by coincidence rather than by the rule.  The two
cells above are soundness and over-rejection respectively.

THE CLASS INSTRUMENT is at the end of this file: a (pattern shape x consumer)
grid asserted as one map, a monotonicity grid saying an untranslatable
scrutinee never buys a better verdict, and a pattern-kind axis held to
`ast.Pattern`'s own subclasses.  The hand-written cells above it are the
instance demonstrations and the disclosure controls, which the grid does not
replace: they pin the WORDING and the warning stream, which a status map
cannot see.

Four quadrants open the file, and only two are red-first.  `clean` x {one
file, imported} flip `tier3`/E535 -> `verified`; `disclosed` x {one file,
imported} are CONTROLS that read the same before and after, and they earn
their place by failing the over-reach mutation (a fix that seeded facts
without the taint check turns both green-to-red).
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

#: The producer's payload is built CLEANLY and it is disclosed anyway, by an
#: unguarded `@Nat` narrowing elsewhere in its body.
#:
#: The disclosed set is per-FUNCTION (`disclosed_fn_names`): any obligation
#: that leaves a fact unestablished puts the whole function in it, because a
#: caller reading any of its declared-type facts is reading the run's word
#: for them.  Separating the two halves is what makes these cells measure
#: that rule rather than one shape of it.
#:
#: It is also the only shape that still discloses.  Every
#: `refinement_predicate` binder position is now GUARDED
#: (`vera.binders.GUARD_SITES`, closed across #1426/#1439/#1440/#1445/#1448),
#: so a refinement narrowing records `tier3` rather than `tier3_unguarded`
#: and a guard makes the declared type true at run time — which is exactly
#: what a consumer may lean on, so it must NOT withhold.  A refined payload
#: built through a handler clause binder used to disclose and no longer
#: does; the root disclosure left is an unguarded `@Nat` narrowing into a
#: builtin that plants no check (#1362), which is `nat_bind` /
#: `tier3_unguarded` / **E504**.
_DISCLOSING_STMT = (
    "let @Option<Nat> = int_to_nat(handle[Exn<Int>] "
    "{{ throw(@Nat) -> {{ nat_to_int(@Nat.0) }} }} in {{ throw({int_expr}) }});"
)


def _op_program(template: str, *, ty: str, base: str, disclosed: bool) -> str:
    guard = "@Int.0 > 0" if base == "Int" else "@Nat.0 < 3"
    payload = _CLEAN_PRODUCER.format(slot=base)
    if disclosed:
        int_expr = "@Int.0" if base == "Int" else "nat_to_int(@Nat.0)"
        payload = (
            _DISCLOSING_STMT.format(int_expr=int_expr) + "\n  " + payload
        )
    return template.format(req=guard, body=payload)


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
    the run has no word for the payload, so the divisor really can be zero,
    and the program went from a refused `E526` to `ok: true` carrying a
    `div_zero`/`tier3` with **no error code and no warning of its own**.  A
    `tier3` nothing surfaces also breaks the `verify --json` partition
    table's own contract.

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
    # The PREMISE, asserted rather than assumed: the producer really is
    # disclosed in this same stream, by an unguarded `@Nat` narrowing.
    # Without this the cell would pass for a producer that stopped
    # disclosing and a `verified` that had become correct — which is what
    # happened to its previous premise (`refine_bind`/`tier3_unguarded`
    # /E506), now unreachable because every refinement binder position is
    # guarded.  The payload's own obligation is `verified` beside it, so
    # the cell measures the per-function rule and not one shape of it.
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(result), (
        f"the producer stopped disclosing, so this cell is vacuous: "
        f"{_triples(result)}"
    )
    assert ("refine_bind", "verified", None) in _triples(result), (
        f"the payload is meant to be built cleanly: {_triples(result)}"
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
#: Same shape as `_op_program`'s disclosed half: a cleanly built payload
#: beside an unguarded `@Nat` narrowing, which is the only route that still
#: discloses (see `_DISCLOSING_STMT`).
_NESTED_DISCLOSED = ("@Int.0 > 0", (
    _DISCLOSING_STMT.format(int_expr="@Int.0") + "\n  Some(Some(@Int.0))"
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
def test_1403_an_indirect_scrutinee_is_withheld_too(
    tmp_path: Path, source: str,
) -> None:
    """The withholding follows the VALUE, not the spelling of the call.

    `_scrutinee_is_disclosed_call` recognises a literally spelled
    `FnCall`/`ModuleCall`.  Bind the same call to a `let`, or route it
    through a forwarding wrapper, and for a while the disclosure did not
    reach the arm: the facts were handed over and the assertion proved,
    beside a `nat_bind`/`tier3_unguarded`/E504 for the very fact it had just
    assumed.  Before this change the assert read no facts at all and so was
    accidentally immune, which is why the four quadrants alone pinned "the
    assert does not assume anything" for the direct spelling only (review of
    PR #1415, F2; CodeRabbit raised the same gap).

    [#1406](https://github.com/aallan/vera/issues/1406) /
    [#1407](https://github.com/aallan/vera/issues/1407) closed it, by
    recording the disclosed call's RESULT TERM and following the taint into
    every binding, projection and branch that value reaches
    (`_disclosed_call_hook`).  So both indirect spellings now read
    `tier3`/E535, and this cell asserts the demotion rather than pinning the
    gap.

    Both polarities, because only one of them changes the exit code and a
    one-sided assertion would let the other flip in silence.  With the
    predicate negated the assertion is equally undecidable — the fact is
    withheld either way — so it too stays `tier3`/E535 with `ok: true`,
    instead of the `ok: false`/E507 it read while the fact was being handed
    over.  That difference is the whole content of the fix, so it is the
    thing asserted.
    """
    result = _verify(_tree(tmp_path / "pos", {"p": source})["p"])
    assert _asserts(result) == [("tier3", "E535")], _triples(result)
    assert ("nat_bind", "tier3_unguarded", "E504") in _triples(result), (
        f"the producer stopped disclosing, so this cell is vacuous: "
        f"{_triples(result)}"
    )

    negated = source.replace("nat_to_int(@Nat.0) >= 0", "nat_to_int(@Nat.0) < 0")
    assert negated != source, "the negated variant must actually differ"
    neg = _verify(_tree(tmp_path / "neg", {"p": negated})["p"])
    assert neg["ok"] is True, _triples(neg)
    assert _asserts(neg) == [("tier3", "E535")], _triples(neg)


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
_SUB_DISCLOSED = ("@Nat.0 >= 10", (
    _DISCLOSING_STMT.format(int_expr="nat_to_int(@Nat.0)")
    + "\n  Some(@Nat.0)"
))
_OVF_CLEAN = ("@Int.0 > 0 && @Int.0 < 100", "Some(@Int.0)")
_OVF_DISCLOSED = ("@Int.0 > 0 && @Int.0 < 100", (
    _DISCLOSING_STMT.format(int_expr="@Int.0") + "\n  Some(@Int.0)"
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


# ---------------------------------------------------------------------------
# The third way a fact can be unestablished, and the reason crossing an import
# ---------------------------------------------------------------------------

def test_1403_the_predicate_covers_every_unestablished_status() -> None:
    """`verified` establishes a fact; every other status does not.

    The vocabulary is READ FROM `ObligationStatus`, not restated here.  A cell
    that lists the five statuses it knows about passes unchanged when a sixth
    is added to the `Literal` — it installs no guard at all, it just asserts
    today's five — which is what the first version of this did (review of
    PR #1415, I1).  Deriving the list means a new member fails here until
    someone classifies it, and the generous default is the dangerous one:
    an unclassified status would count as "established" and hand a caller a
    fact nobody proved.

    SCOPE.  This pins the classification of a status, and the cell below pins
    everything downstream of it.  Neither exercises the link that PRODUCES a
    `timeout` at a producer's own site — a solver `unknown` mapped to
    `timeout` by the `otherwise` argument at each `_record_undecided_safety`
    call — because no goal I could write makes Z3 return `unknown` inside a
    budget a test can rely on.  That mapping remains unexercised, and the
    coverage claimed here stops at the status, not at how it arises.
    """
    from typing import get_args

    from vera.obligations.core import ObligationStatus, ProofObligation
    from vera.verifier import fact_not_established, unestablished_reason

    #: The classification every status must have.  `None` means the status
    #: ESTABLISHES the fact, so nothing is withheld.
    expected: dict[str, str | None] = {
        "verified": None,
        # A guarded `tier3` is established at run time — the guard makes it so.
        "tier3": None,
        "tier3_unguarded": "disclosed",
        "violated": "refuted",
        "timeout": "undecided",
    }
    vocabulary = set(get_args(ObligationStatus))
    assert vocabulary == set(expected), (
        f"`ObligationStatus` has members this cell does not classify: "
        f"{sorted(vocabulary - set(expected))}; and classifies members it no "
        f"longer has: {sorted(set(expected) - vocabulary)}. Decide whether a "
        f"new status establishes a fact — defaulting to 'yes' hands a caller "
        f"a fact nobody proved."
    )

    def obl(status: str, code: str = "") -> ProofObligation:
        return ProofObligation(
            fn_name="f", kind="refine_bind", status=status,  # type: ignore[arg-type]
            expr_text="x", line=1, column=1, error_code=code,
        )

    # `tier3` splits on its code: plain is guarded, E534 is this mechanism's
    # own demotion and is NOT established.
    assert unestablished_reason(obl("tier3", "E534")) == "disclosed"
    assert fact_not_established(obl("tier3", "E534"))

    for status, reason in expected.items():
        code = {"tier3_unguarded": "E504", "violated": "E505",
                "timeout": "E524"}.get(status, "")
        assert unestablished_reason(obl(status, code)) == reason, status
        assert fact_not_established(obl(status, code)) is (
            reason is not None
        ), status


def test_1403_a_timed_out_premise_is_withheld_too(tmp_path: Path) -> None:
    """A budget that ran out is not a fact either.

    The predicate admitted `tier3_unguarded`, `tier3`+E534 and `violated`, but
    not `timeout` — so a producer whose establishing obligation the solver
    never settled still handed its fact to the arm (review of PR #1415, H2).

    The timeout is INJECTED rather than raced.  Every nonlinear goal I tried
    — `x*x+1 > 0`, a quartic, a product of two such, `x*x*x != 7` — Z3 settles
    inside a 1 ms budget, and a query slow enough to time out reliably would
    make the cell depend on machine load, which is exactly why
    `DischargeCache` refuses to replay timeout outcomes at all.  So the
    solver's verdict for the producer's own obligation is replaced at the
    point it is recorded, and everything downstream — the predicate, the
    reason, the taint, the wording — is the real pipeline.
    """
    from vera import verifier as vmod

    source = _REFUTED.format(arm="100 / @PosInt.0").replace(
        "Some(@Int.0)", "Some(@Int.0 * @Int.0 + 1)",
    ).replace("fn main", "fn use_it")
    path = _tree(tmp_path, {"p": source})["p"]

    original = vmod.ContractVerifier._record_obligation

    def injecting(self, fn_name, kind, node, status, **kw):  # type: ignore[no-untyped-def]
        if fn_name == "mk" and kind == "refine_bind":
            status, kw = "timeout", {**kw, "error_code": "E524"}
        return original(self, fn_name, kind, node, status, **kw)

    vmod.ContractVerifier._record_obligation = injecting
    try:
        from vera.checker import typecheck_with_artifacts
        from vera.parser import parse
        from vera.resolver import ModuleResolver
        from vera.transform import transform

        text = path.read_text(encoding="utf-8")
        program = transform(parse(text, file=str(path)))
        resolver = ModuleResolver(_root=path.parent)
        resolved = resolver.resolve_imports(program, path)
        _d, artifacts = typecheck_with_artifacts(
            program, text, file=str(path), resolved_modules=resolved,
        )
        result = vmod.verify(
            program, text, file=str(path), resolved_modules=resolved,
            expr_types=artifacts.expr_semantic_types,
            expr_target_types=artifacts.expr_target_types,
        )
    finally:
        vmod.ContractVerifier._record_obligation = original

    seen = [
        (o.kind, o.status, o.error_code) for o in result.obligations
    ]
    assert ("refine_bind", "timeout", "E524") in seen, seen
    div = [(o.status, o.error_code) for o in result.obligations
           if o.kind == "div_zero"]
    assert div == [("tier3", "E534")], (
        f"a timed-out premise still proved the consumer: {seen}"
    )
    texts = [
        d.description for d in result.diagnostics
        if d.error_code == "E534"
    ]
    assert len(texts) == 1, texts
    assert "could not decide within the budget" in texts[0], texts[0]


def test_1403_a_refuted_import_is_cited_as_refuted(tmp_path: Path) -> None:
    """The reason has to cross the import, not just the name.

    `_tainted_refuted` was set only on the local branch, so a library whose
    obligation the run REFUTED was cited with "disclosed at …" and a sentence
    claiming the run could neither prove nor guard it — untrue of both runs
    (review of PR #1415, H1).  The reason now travels in the manifest's
    `DisclosureSite`, so the citation says the true thing and points at the
    library's own E505.
    """
    paths = _tree(tmp_path, {
        "rlib": """\
type Pos = { @Int | @Int.0 > 0 };

public fn mk(@Int -> @Option<Pos>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}
""",
        "rmain": """\
import rlib;

type Pos = { @Int | @Int.0 > 0 };

public fn use_it(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match rlib::mk(@Int.0) {
    Some(@Pos) -> 100 / @Pos.0,
    None -> 1
  }
}
""",
    })
    lib = _verify(paths["rlib"])
    assert ("refine_bind", "violated", "E505") in _triples(lib), _triples(lib)

    result = _verify(paths["rmain"])
    assert ("div_zero", "tier3", "E534") in _triples(result), _triples(result)
    e534 = [w for w in result["warnings"] if w.get("error_code") == "E534"]
    assert len(e534) == 1, [w.get("error_code") for w in result["warnings"]]
    text = e534[0]["description"]
    assert "rlib::mk" in text and "refuted at" in text, text
    assert "E505" in text, text
    assert "proved FALSE" in text, text
    assert "could neither prove nor guard" not in text, text


# ===========================================================================
# THE CLASS INSTRUMENT — four grids, each asserted as one map
# ===========================================================================
#
# The class is: the context a `match` arm is verified under.  Four walks
# descend an arm and each one needs three things from it — the slot env its
# pattern binds, the fact that the arm was taken, and the facts the pattern
# ESTABLISHES.  Each assembled that context inline, so the four disagreed,
# and #1403 is one disagreement out of the grid.  What closes the class is
# ONE derivation (`ContractVerifier._enter_match_arm`); what MEASURES it is
# the products below, each asserted as a single map rather than as a list of
# cells that grew one per bug.
#
# The grids, and which component of the context each holds to account:
#
# 1. pattern SHAPE x CONSUMER — the facts the arm establishes;
# 2. the same shapes with an UNTRANSLATABLE scrutinee, asserted whole and
#    then as a monotonicity relation against grid 1 — the env's rejected
#    alternatives;
# 3. pattern KIND, held to `ast.Pattern`'s own subclasses — the env, in the
#    direction where a binder must TAKE a slot away;
# 4. the DISCRIMINANT, over arms that bind nothing at all.
#
# The dimensions come from the code that makes the decision:
#
# * the CONSUMERS are the places an obligation inside an arm is discharged,
#   one per caller of the seam plus the translation route — an `assert` and
#   the §6.4.3 safety obligations (`_walk_for_primitive_op_obligations`), a
#   postcondition reached through the arm (`_translate_match`), a refined
#   construction store (`_descend_construction_container`), and a call
#   precondition;
# * the SHAPES are the ways a pattern can carry a payload fact, plus the two
#   contexts in which it must NOT: a genuine narrowing (the source type says
#   nothing) and a disclosed producer (the run has no word for it).
#
# Every product that is not a cell is stated with its reason: the
# `disclosed` shape has no untranslatable twin, because an untranslatable
# scrutinee is an effect operation's result rather than a call, so there is
# no producer for the disclosure to come from.

_MATRIX_TYPES = """\
type Pos = { @Int | @Int.0 > 0 };
type NonNeg = { @Int | @Int.0 >= 0 };
type Small = { @Pos | @Pos.0 < 10 };
"""

_MATRIX_NEEDS = """\
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  1
}
"""

#: shape -> the scrutinee's type, how the producer builds it, the arm's
#: pattern, the payload the consumer reads, the other arms, and the value a
#: `State` cell of that type is initialised with for the untranslatable twin.
_MATRIX_SHAPES: dict[str, dict] = {
    "direct": dict(
        sty="Option<Pos>", mk_body="Some(@Int.0)",
        pattern="Some(@Pos)", payload="@Pos.0",
        others=["None"], init="Some(5)",
    ),
    "nested": dict(
        sty="Option<Option<Pos>>", mk_body="Some(Some(@Int.0))",
        pattern="Some(Some(@Pos))", payload="@Pos.0",
        others=["Some(None)", "None"], init="Some(Some(5))",
    ),
    "tuple": dict(
        sty="Option<Tuple<Pos, Int>>", mk_body="Some(Tuple(@Int.0, 7))",
        pattern="Some(Tuple(@Pos, @Int))", payload="@Pos.0",
        others=["None"], init="Some(Tuple(5, 7))",
    ),
    "chain": dict(
        sty="Option<Tuple<Small, Int>>", mk_body="Some(Tuple(@Int.0, 7))",
        pattern="Some(Tuple(@Small, @Int))", payload="@Small.0",
        others=["None"], init="Some(Tuple(5, 7))",
    ),
    # The two shapes that establish NOTHING, for opposite reasons.
    "narrowing": dict(
        sty="Option<Int>", mk_body="Some(@Int.0)",
        pattern="Some(@Pos)", payload="@Pos.0",
        others=["None"], init="Some(5)",
    ),
    "disclosed": dict(
        sty="Option<Pos>",
        mk_body=_DISCLOSING_STMT.format(int_expr="@Int.0") + "\n  Some(@Int.0)",
        pattern="Some(@Pos)", payload="@Pos.0",
        others=["None"], init=None,
    ),
}

#: consumer -> how the arm body spends the payload, the function's return
#: type and postcondition, the fallback the other arms return, and the
#: obligation kind that carries this consumer's verdict.
_MATRIX_CONSUMERS: dict[str, dict] = {
    "assert": dict(body="{{ assert({p} > 0); 1 }}", ret="@Int",
                   fallback="0", post="true", kind="assert"),
    "ensures": dict(body="{p}", ret="@Int",
                    fallback="1", post="@Int.result > 0", kind="ensures"),
    "store": dict(body="Some({p})", ret="@Option<NonNeg>",
                  fallback="None", post="true", kind="refine_bind"),
    "call_pre": dict(body="needs_pos({p})", ret="@Int",
                     fallback="0", post="true", kind="call_pre"),
}


def _matrix_program(shape: str, consumer: str, *, untranslatable: bool) -> str:
    """One cell's program: the same arm, spent by one consumer."""
    s, c = _MATRIX_SHAPES[shape], _MATRIX_CONSUMERS[consumer]
    arms = [f"{s['pattern']} -> {c['body'].format(p=s['payload'])}"]
    arms += [f"{o} -> {c['fallback']}" for o in s["others"]]
    arm_text = ",\n    ".join(arms)
    parts = [_MATRIX_TYPES, "\n", _MATRIX_NEEDS, "\n"]
    if untranslatable:
        # The scrutinee is an effect operation's result, which the SMT layer
        # cannot translate.  The arm still BINDS, so the seam shadows each
        # binder with a tracked opaque const.
        body = (
            f"handle[State<{s['sty']}>](@{s['sty']} = {s['init']}) {{\n"
            f"    get(@Unit) -> {{ resume(@{s['sty']}.0) }},\n"
            f"    put(@{s['sty']}) -> {{ resume(()) }}\n"
            f"  }} in {{\n"
            f"    match get(()) {{\n    {arm_text}\n    }}\n"
            f"  }}"
        )
    else:
        parts.append(
            f"private fn mk(@Int -> @{s['sty']})\n"
            f"  requires(@Int.0 > 0 && @Int.0 < 10)\n  ensures(true)\n"
            f"  effects(pure)\n{{\n  {s['mk_body']}\n}}\n\n"
        )
        body = f"match mk(@Int.0) {{\n    {arm_text}\n  }}"
    parts.append(
        f"public fn use_it(@Int -> {c['ret']})\n"
        f"  requires(@Int.0 > 0 && @Int.0 < 10)\n"
        f"  ensures({c['post']})\n  effects(pure)\n"
        f"{{\n  {body}\n}}\n"
    )
    return "".join(parts)


def _matrix_cell(tmp_path: Path, shape: str, consumer: str, *,
                 untranslatable: bool) -> tuple[bool, list]:
    src = _matrix_program(shape, consumer, untranslatable=untranslatable)
    tag = ("u" if untranslatable else "t") + f"_{shape}_{consumer}"
    result = _verify(_tree(tmp_path / tag, {"p": src})["p"])
    kind = _MATRIX_CONSUMERS[consumer]["kind"]
    return result["ok"], [
        (o["status"], o.get("error_code"))
        for o in result["obligations"] if o["kind"] == kind
    ]


#: The whole map, and the reason each entry is what it is.
#:
#: A `call_pre` entry of `[]` is the ABSENCE of an unproved precondition: a
#: discharged one records no obligation, so the rows that make this
#: non-vacuous are `narrowing` (`violated`/E501) and `disclosed`
#: (`tier3`/E532) — the same cell, same consumer, showing what a failure
#: looks like.
#:
#: `ensures` carries one entry per function in the program (`needs_pos`,
#: `mk`, `use_it`), so the list is read whole rather than filtered; the last
#: entry is `use_it`'s.
_MATRIX_EXPECTED: dict[tuple[str, str], tuple[bool, list]] = {
    # --- the arm ESTABLISHES the payload's fact: every consumer proves ----
    ("direct", "assert"): (True, [("verified", None)]),
    ("direct", "ensures"): (True, [("verified", None)] * 3),
    ("direct", "store"): (True, [("verified", None)] * 2),
    ("direct", "call_pre"): (True, []),
    ("nested", "assert"): (True, [("verified", None)]),
    ("nested", "ensures"): (True, [("verified", None)] * 3),
    ("nested", "store"): (True, [("verified", None)] * 2),
    ("nested", "call_pre"): (True, []),
    ("tuple", "assert"): (True, [("verified", None)]),
    ("tuple", "ensures"): (True, [("verified", None)] * 3),
    ("tuple", "store"): (True, [("verified", None)] * 2),
    ("tuple", "call_pre"): (True, []),
    ("chain", "assert"): (True, [("verified", None)]),
    ("chain", "ensures"): (True, [("verified", None)] * 3),
    ("chain", "store"): (True, [("verified", None)] * 2),
    ("chain", "call_pre"): (True, []),
    # --- a genuine NARROWING establishes nothing: the bind stays obligated,
    #     and each consumer answers with its own refusal.  The payload's
    #     declared type is `Int`, so no fact exists to hand over, and the
    #     countermodel names a value the type really permits.
    ("narrowing", "assert"): (False, [("tier3", "E535")]),
    ("narrowing", "ensures"): (
        False, [("verified", None), ("verified", None), ("violated", None)]),
    ("narrowing", "store"): (False, [("violated", "E505")] * 2),
    ("narrowing", "call_pre"): (False, [("violated", "E501")]),
    # --- a DISCLOSED producer: the fact exists but the run has no word for
    #     it, so every consumer demotes, and says so.  Each says so in its
    #     OWN code, which is deliberate and worth reading off the table
    #     rather than smoothing over: E535 for an assertion, E534 for the
    #     postcondition and for a §6.4.3 safety obligation (the codes spec
    #     §6.2.5 names), E532 for a call precondition, and the construction
    #     store's pre-existing E506.  The store is the one that does not
    #     name the disclosure as its reason — it reports that the predicate
    #     could not be verified statically, which is true but says less.
    #     It is within the rule §6.2.5 states, since a construction bind is
    #     neither a contract nor a safety obligation, and it is not silent;
    #     widening E534 to cover it would change what a reader is told at
    #     every unproved construction store in the language, which is a
    #     bigger question than this class.
    ("disclosed", "assert"): (True, [("tier3", "E535")]),
    ("disclosed", "ensures"): (
        True, [("verified", None), ("verified", None), ("tier3", "E534")]),
    ("disclosed", "store"): (
        True, [("verified", None), ("tier3", "E506")]),
    ("disclosed", "call_pre"): (True, [("tier3", "E532")]),
}


def test_1403_the_class_instrument_shape_x_consumer(tmp_path: Path) -> None:
    """Every consumer of an arm agrees about what that arm establishes.

    Asserted as ONE map, so a cell that moves is reported beside every cell
    that did not, and a shape or consumer the code has and this table does
    not shows up as a KeyError rather than as silence.  Before #1403 the
    four `assert` and safety cells in the establishing rows read
    `tier3`/E535 (and `100 / @Pos.0` was refused E526) while the `ensures`
    and `call_pre` cells beside them read `verified` — the disagreement is
    the bug, and the map is what makes disagreement visible.

    Each row is labelled by what it can hold to account.  The establishing
    rows are the proof direction; `narrowing` and `disclosed` are the two
    ways an arm establishes nothing, and they are not controls in the weak
    sense — each has a DIFFERENT right answer (a refutation versus a
    demotion), so a fix that withheld everything or assumed everything moves
    them in opposite directions.
    """
    measured = {
        (shape, consumer): _matrix_cell(
            tmp_path, shape, consumer, untranslatable=False)
        for shape in _MATRIX_SHAPES
        for consumer in _MATRIX_CONSUMERS
    }
    expected = {k: (v[0], list(v[1])) for k, v in _MATRIX_EXPECTED.items()}
    assert measured == expected, "\n".join(
        f"{k}: expected {expected.get(k)!r} got {v!r}"
        for k, v in sorted(measured.items(), key=repr)
        if expected.get(k) != v
    )


#: The same grid with the scrutinee produced by an effect operation, which
#: the SMT layer cannot translate.  `disclosed` has no twin here: an
#: untranslatable scrutinee is an operation's result rather than a call, so
#: there is no producer for a disclosure to come from.
#:
#: The extra `refine_bind` entries are the `State` cell's own initialiser
#: (`Some(5)` at `Option<Pos>`), which is the wrapper's and not the arm's;
#: the arm's is the LAST entry, which is what `_payload_entry` reads.
_MATRIX_EXPECTED_UNTRANSLATABLE: dict[tuple[str, str], tuple[bool, list]] = {
    **{
        (shape, consumer): verdict
        for shape in ("direct", "nested", "tuple", "chain")
        for consumer, verdict in (
            ("assert", (True, [("tier3", "E535")])),
            ("ensures", (True, [("verified", None), ("tier3", "E522")])),
            ("store", (True, [("verified", None),
                              ("tier3_unguarded", "E506"),
                              ("tier3_unguarded", "E506")])),
            ("call_pre", (True, [("tier3", "E532")])),
        )
    },
    ("narrowing", "assert"): (True, [("tier3", "E535")]),
    ("narrowing", "ensures"): (
        True, [("verified", None), ("tier3", "E522")]),
    ("narrowing", "store"): (
        True, [("tier3", "E506"), ("tier3_unguarded", "E506")]),
    ("narrowing", "call_pre"): (True, [("tier3", "E532")]),
}


def _payload_entry(obls: list) -> tuple | None:
    """The verdict of the obligation that reads the arm's PAYLOAD.

    Last in every consumer's list: an `assert` and a `call_pre` have only
    that one, a postcondition list ends with `use_it`'s, and a store list
    ends with the arm's after the producer's or the `State` cell's own.
    Reading one entry is what makes the monotonicity comparison below a
    statement about the arm rather than about the fixture's scaffolding.
    """
    return obls[-1] if obls else None


def test_1403_an_untranslatable_scrutinee_is_never_more_permissive(
    tmp_path: Path,
) -> None:
    """MONOTONICITY, as a property of the whole grid rather than one cell.

    Whether a `match` scrutinee happens to translate is an accident of how
    the value is produced, so it must never buy a program a better verdict.
    The grid is asserted whole first — so no cell is vacuous — and the
    relation between the two grids is then asserted over the payload entry
    of each:

    1. nothing that reads the payload is `verified` here.  That is the
       direction that used to fail: the call walk kept the OUTER env under
       an untranslatable scrutinee, so a recursive call's argument
       translated against the enclosing parameter and a `decreases` measure
       was proved about a value the arm never binds — `verified` for a
       function whose runtime measure guard traps on its first call.
    2. a refutation the translatable twin reports is either still refuted or
       DEMOTED WITH A DIAGNOSTIC.  `narrowing`/`store` demotes
       `violated`/E505 to `tier3_unguarded`/E506, which is a disclosure
       rather than silence.

    `call_pre` is the second kind: where its twin records `violated`/E501,
    it records `tier3`/E532.  The walk reaches the call in the arm whatever
    the scrutinee (#1480), and a precondition over the arm's placeholder is
    a check the run cannot make, never a refutation, so the call-site check
    demotes it (`SmtContext.opaque_term`).  Before #1480 it recorded
    nothing, because the obligation was a side effect of translating the
    enclosing expression and `_translate_match` bails at the scrutinee.
    """
    measured = {
        (shape, consumer): _matrix_cell(
            tmp_path, shape, consumer, untranslatable=True)
        for shape in _MATRIX_SHAPES
        if _MATRIX_SHAPES[shape]["init"] is not None
        for consumer in _MATRIX_CONSUMERS
    }
    expected = {
        k: (v[0], list(v[1]))
        for k, v in _MATRIX_EXPECTED_UNTRANSLATABLE.items()
    }
    assert measured == expected, "\n".join(
        f"{k}: expected {expected.get(k)!r} got {v!r}"
        for k, v in sorted(measured.items(), key=repr)
        if expected.get(k) != v
    )

    verified_here = {
        k for k, (_ok, obls) in measured.items()
        if _payload_entry(obls) == ("verified", None)
    }
    refutation_lost = {
        k for k, (_ok, obls) in measured.items()
        if (_MATRIX_EXPECTED[k][1][-1:] or [("", "")])[0][0] == "violated"
        and _payload_entry(obls) is None
    }
    assert (verified_here, refutation_lost) == (set(), set()), (
        f"an untranslatable scrutinee bought a better verdict:\n"
        f"  verified: {sorted(verified_here)}\n"
        f"  refutation lost with no record: {sorted(refutation_lost)}\n"
        f"  measured: {measured}"
    )


# ---------------------------------------------------------------------------
# ... and the PATTERN-KIND axis: every kind the grammar has, classified
# ---------------------------------------------------------------------------

_KIND_PRELUDE = """\
type Pos = { @Int | @Int.0 > 0 };

private fn mk(@Int -> @Option<Pos>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

private fn tag(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  "a"
}

private fn flag(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

private fn ident(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

"""

#: kind -> the `match` that puts an arm of that kind around the assertion.
#:
#: The assertion is always `@Int.0 > 0`, which the function's own `requires`
#: gives and nothing else does — the scrutinee is a call result in every
#: case, so no arm's discriminant can prove it and the arm's own binder is
#: the only thing that could take it away.  That makes one cell per kind ask
#: exactly one question: does an arm of this kind still see the scope it sits
#: in?
_KIND_MATCHES: dict[str, str] = {
    "ConstructorPattern": """\
  match mk(@Int.0) {
    Some(@Pos) -> { assert(@Int.0 > 0); 0 },
    None -> 1
  }""",
    "NullaryPattern": """\
  match mk(@Int.0) {
    Some(@Pos) -> 1,
    None -> { assert(@Int.0 > 0); 0 }
  }""",
    "WildcardPattern": """\
  match mk(@Int.0) {
    _ -> { assert(@Int.0 > 0); 0 }
  }""",
    "IntPattern": """\
  match ident(@Int.0) {
    5 -> { assert(@Int.0 > 0); 0 },
    _ -> 1
  }""",
    "StringPattern": """\
  match tag(@Int.0) {
    "a" -> { assert(@Int.0 > 0); 0 },
    _ -> 1
  }""",
    "BoolPattern": """\
  match flag(@Int.0) {
    true -> { assert(@Int.0 > 0); 0 },
    false -> 1
  }""",
    # The one kind that SHADOWS the slot the assertion reads: `@Int` binds
    # the scrutinee, so `@Int.0` in the arm is the call's result and the
    # enclosing `requires(@Int.0 > 0)` must NOT discharge it.  This is the
    # #680 misattribution direction, and it is what makes the six cells
    # above mean something: without it "the arm sees its scope" would be
    # satisfied by an arm that binds nothing at all.
    "BindingPattern": """\
  match ident(@Int.0) {
    @Int -> { assert(@Int.0 > 0); 0 }
  }""",
}

#: The classification each kind's cell asserts.  `True` = the enclosing
#: scope's fact still discharges the assertion; `False` = the arm's own
#: binder shadows the slot, so it must not.
_KIND_KEEPS_OUTER_SCOPE: dict[str, bool] = {
    "ConstructorPattern": True,
    "NullaryPattern": True,
    "WildcardPattern": True,
    "IntPattern": True,
    "StringPattern": True,
    "BoolPattern": True,
    "BindingPattern": False,
}


def test_1403_every_pattern_kind_is_classified(tmp_path: Path) -> None:
    """The pattern-kind axis is held to the GRAMMAR, not to a list.

    The kinds come from `ast.Pattern`'s subclasses — the same enumeration
    the transformer builds and `vera/binders.py` registers as binder
    positions — so a kind the grammar gains fails here until someone decides
    whether an arm of that kind keeps the scope it sits in.  A table that
    listed the seven kinds it knew about would pass unchanged for an eighth,
    which is no guard at all.
    """
    from vera import ast

    def concrete(cls: type) -> set[str]:
        out: set[str] = set()
        for sub in cls.__subclasses__():
            kids = concrete(sub)
            out |= kids or {sub.__name__}
        return out

    grammar_kinds = concrete(ast.Pattern)
    assert grammar_kinds == set(_KIND_KEEPS_OUTER_SCOPE), (
        f"`ast.Pattern` has kinds this axis does not classify: "
        f"{sorted(grammar_kinds - set(_KIND_KEEPS_OUTER_SCOPE))}; and "
        f"classifies kinds it no longer has: "
        f"{sorted(set(_KIND_KEEPS_OUTER_SCOPE) - grammar_kinds)}.  Decide "
        f"whether an arm of the new kind keeps its enclosing scope — "
        f"answering 'yes' by default is how a binder came to read a stale "
        f"same-named outer."
    )
    assert set(_KIND_MATCHES) == set(_KIND_KEEPS_OUTER_SCOPE)


def test_1403_no_pattern_kind_loses_or_fabricates_the_arms_scope(
    tmp_path: Path,
) -> None:
    """One boolean over every pattern kind: the arm's scope is its own.

    Asserted as a whole map for the same reason as the shape x consumer
    grid: the interesting failure is a DISAGREEMENT between kinds, and a
    per-kind cell added as each bug arrived would never show one.  Six kinds
    bind nothing, so the enclosing `requires(@Int.0 > 0)` still discharges
    an `assert(@Int.0 > 0)` in the arm; the seventh binds `@Int` and must
    take it away.
    """
    measured = {}
    for kind, match_text in _KIND_MATCHES.items():
        src = (
            _KIND_PRELUDE
            + "public fn use_it(@Int -> @Int)\n"
              "  requires(@Int.0 > 0)\n  ensures(true)\n  effects(pure)\n"
              "{\n" + match_text + "\n}\n"
        )
        result = _verify(_tree(tmp_path / kind, {"p": src})["p"])
        measured[kind] = _asserts(result) == [("verified", None)]
    assert measured == _KIND_KEEPS_OUTER_SCOPE, "\n".join(
        f"{k}: expected keeps_outer_scope={_KIND_KEEPS_OUTER_SCOPE[k]} "
        f"got {v}"
        for k, v in sorted(measured.items())
        if _KIND_KEEPS_OUTER_SCOPE[k] != v
    )


# ---------------------------------------------------------------------------
# The two defects the one arm-context derivation closed, red-first
# ---------------------------------------------------------------------------

#: A termination measure read off a binder the arm shadows.  The scrutinee is
#: an effect operation's result, so the SMT layer cannot translate it; the
#: recursive call's argument is `@Nat.0 - 1` where `@Nat.0` is the PAYLOAD.
#: The `State` cell holds `Some(5)` forever, so the program recurses on 4 for
#: ever and cannot terminate.
_SHADOWED_MEASURE = """\
public fn countdown(@Nat -> @Nat)
  requires(@Nat.0 > 0)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  handle[State<Option<Nat>>](@Option<Nat> = Some(5)) {
    get(@Unit) -> { resume(@Option<Nat>.0) },
    put(@Option<Nat>) -> { resume(()) }
  } in {
    match get(()) {
      Some(@Nat) -> countdown(@Nat.0 - 1),
      None -> 0
    }
  }
}
"""

#: A refinement bind whose value is an arm placeholder.  The scrutinee is
#: again an effect operation's result, so `@Int.0` in the arm is a fresh
#: const; the cell really holds `Some(9)`, so the program runs and returns 9.
_PLACEHOLDER_BIND = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    match get(()) {
      Some(@Int) -> {
        let @PosInt = @Int.0;
        @PosInt.0
      },
      None -> 0
    }
  }
}
"""


def test_1403_a_measure_is_not_proved_against_a_shadowed_outer(
    tmp_path: Path,
) -> None:
    """RED before: a false Tier-1 termination proof, refuted by its own guard.

    The recursive-call walk behind `decreases` kept the ENCLOSING slot env
    when a `match` scrutinee could not be translated, so `@Nat.0` inside
    `Some(@Nat) ->` resolved to the function's PARAMETER rather than to the
    payload the arm binds.  The measure goal became `param - 1 < param`,
    which proves, and `vera verify` reported `decreases`/**verified** for a
    program that recurses on an effect operation's payload — 5 every time.

    The oracle is the runtime guard, not another proof: `vera run` traps on
    the very first call with "decreases() measure in 'countdown' failed to
    decrease".  A Tier-1 claim its own guard refutes is the definition of a
    false one (and this shipped in v0.1.13).

    The honest answer is `tier3`/E525 — the same verdict the TRANSLATABLE
    spelling of this program already gave, which is the monotonicity row one
    cell at a time.
    """
    path = _tree(tmp_path, {"p": _SHADOWED_MEASURE})["p"]
    result = _verify(path)
    measures = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == "decreases"
    ]
    assert measures == [("tier3", "E525")], _triples(result)

    # The oracle, so the cell cannot pass for a compiler that has stopped
    # emitting the guard: the program is genuinely non-terminating, and the
    # guard says so on the first call rather than after a deep recursion.
    run = _cli("run", str(path), "--fn", "countdown", "--", "5")
    assert run.returncode != 0, run.stdout
    assert "failed to decrease" in run.stderr, run.stderr


def test_1403_an_untracked_arm_placeholder_is_not_a_counterexample(
    tmp_path: Path,
) -> None:
    """RED before: a correct program refused, on a value nothing could read.

    The narrowing walk minted an untranslatable arm's binders as fresh vars
    but did not TRACK them, so `_contains_opaque_shadow` could not see them
    and the gate that filters refutations over unreadable values never
    engaged.  Z3 duly picked a negative value for an unconstrained const and
    `let @PosInt = @Int.0` was reported `refine_bind`/**violated**/E505 —
    a refusal of a program `vera run` returns 9 from.

    `tier3`/E506 is the honest answer: the value cannot be read, so it can
    be neither proved nor refuted, and the site's runtime guard backs it.
    The distinction that makes this a defect rather than a policy is that
    the countermodel named no value the program can produce — unlike the
    `narrowing` row of the grid above, where the payload's declared type
    really does permit the counterexample.
    """
    path = _tree(tmp_path, {"p": _PLACEHOLDER_BIND})["p"]
    result = _verify(path)
    assert result["ok"] is True, result["diagnostics"]
    binds = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == "refine_bind"
    ]
    assert binds == [("tier3", "E506")], _triples(result)

    run = _cli("run", str(path), "--fn", "probe")
    assert run.returncode == 0, run.stderr
    assert run.stdout.strip().endswith("9"), run.stdout


# ---------------------------------------------------------------------------
# ... and the DISCRIMINANT: an arm's obligations know which arm they are in
# ---------------------------------------------------------------------------
#
# The third component of an arm's context.  Where the facts come from
# BINDERS, these arms have none — so the arm's discriminant is the only thing
# that can distinguish them, which is what makes these cells the ones that
# hold `_under_arm`'s push to account.  Each reads `verified` with the
# discriminant on the path and moves without it, in one of the two directions
# a lost premise can go.

_DISC_ASSERT = """\
public fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(_) -> {
      assert(match @Option<Int>.0 { Some(_) -> true, None -> false });
      1
    },
    None -> 0
  }
}
"""

_DISC_DIV = """\
public fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(_) -> 100 / (match @Option<Int>.0 { Some(_) -> 1, None -> 0 }),
    None -> 0
  }
}
"""

_ZERO = """\
private fn zero(-> @Int)
  requires(true)
  ensures(@Int.result == 0)
  effects(pure)
{
  0
}

"""

#: A DEAD inner arm: the inner `None` leg is unreachable only because the
#: OUTER arm's condition is on the path.  Without it, its `100 / 0` is a
#: refutation of a program that cannot reach it.
_DISC_DEAD_ARM = _ZERO + """\
public fn f(@Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Int>.0 {
    Some(_) -> match @Option<Int>.0 { Some(_) -> 1, None -> 100 / zero() },
    None -> 0
  }
}
"""

#: The same, over an ADT whose constructors carry NO payload at all, so no
#: arm anywhere in the program has a binder.
_DISC_NULLARY_ONLY = """\
private data Light {
  Red,
  Green
}

""" + _ZERO + """\
public fn f(@Light -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Light.0 {
    Red -> match @Light.0 { Red -> 1, Green -> 100 / zero() },
    Green -> 0
  }
}
"""


@pytest.mark.parametrize(
    "source,kind",
    [
        pytest.param(_DISC_ASSERT, "assert", id="assert-reads-the-arm"),
        pytest.param(_DISC_DIV, "div_zero", id="divisor-reads-the-arm"),
        pytest.param(_DISC_DEAD_ARM, "div_zero", id="dead-inner-arm"),
        pytest.param(_DISC_NULLARY_ONLY, "div_zero", id="no-binder-anywhere"),
    ],
)
def test_1403_an_obligation_knows_which_arm_it_is_in(
    tmp_path: Path, source: str, kind: str,
) -> None:
    """The arm's discriminant is a premise of every obligation in the arm.

    The other two components of an arm's context are measured by the grids
    above; this is the third, and it needs arms with NO binders, because the
    established facts would otherwise carry the proof and the discriminant
    would be along for the ride.  With nothing bound, `is-Some(scrutinee)` is
    the only thing that tells one arm from another, so each of these reads
    `verified` only while `_under_arm` holds it on the path:

    * the assertion re-matches the scrutinee, so without the premise the
      solver may answer `None` inside the `Some` arm — measured `tier3`/E535;
    * the divisor does the same, and a solver free to pick `None` picks the
      zero — measured `violated`/**E526**, a refusal of a program that cannot
      divide by zero;
    * the dead-arm cells put the zero in an inner leg that is unreachable
      only because the OUTER arm matched, which is the same failure one level
      out, and the last of them uses an ADT with no payloads at all so that
      no binder exists anywhere in the program to supply the proof instead.

    All four verdicts are `verified` here and all four move under a mutant
    that drops the push, which is what makes this the cell for it rather than
    a restatement of the grids.
    """
    result = _verify(_tree(tmp_path, {"p": source})["p"])
    assert result["ok"] is True, result["diagnostics"]
    assert [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == kind
    ] == [("verified", None)], _triples(result)


# ---------------------------------------------------------------------------
# ... and the structural half: one assembly point, checked against the source
# ---------------------------------------------------------------------------

def test_1403_the_arm_context_has_one_assembly_point() -> None:
    """The three derivations are composed in ONE place, held by the AST.

    The grids above measure what the arm's context MEANS; this measures
    where it is BUILT, which is the part a green suite cannot see.  A fifth
    walk that assembles its own context out of `_bind_pattern`,
    `_pattern_condition` and `_subpattern_source_facts` would pass every
    cell above — it would simply be wrong in some way none of them reaches,
    which is how the four copies this PR removes came to exist, one review
    finding at a time.

    So: in `vera/verifier.py`, every call to any of those three, and to
    `_fresh_pattern_env`, sits inside `_enter_match_arm`.  Read from the
    AST rather than by grep, so a mention in a comment or a docstring is
    not a call and cannot make this pass or fail by accident.

    `_fresh_pattern_env`'s own recursion into sub-patterns is exempt by
    name — it is the derivation, not a second assembly of it.  The SMT
    layer's `_translate_match` composes the same three for a different job,
    building the arm's If-chain VALUE, and is deliberately outside this
    scan: it consumes each derivation once, so there is no second
    derivation there either, but it is not a walk that discharges
    obligations and the seam does not fit its shape.
    """
    import ast as py_ast
    from pathlib import Path

    import vera

    src = Path(vera.__file__).resolve().parent / "verifier.py"
    tree = py_ast.parse(src.read_text(encoding="utf-8"))

    watched = {
        "_bind_pattern", "_pattern_condition", "_subpattern_source_facts",
        "_fresh_pattern_env",
    }
    exempt_owners = {"_enter_match_arm", "_fresh_pattern_env"}

    stray: list[tuple[str, str, int]] = []
    for fn in py_ast.walk(tree):
        if not isinstance(fn, (py_ast.FunctionDef, py_ast.AsyncFunctionDef)):
            continue
        if fn.name in exempt_owners:
            continue
        for node in py_ast.walk(fn):
            if (isinstance(node, py_ast.Call)
                    and isinstance(node.func, py_ast.Attribute)
                    and node.func.attr in watched):
                stray.append((fn.name, node.func.attr, node.lineno))

    assert stray == [], (
        "a second assembly of the arm's context has appeared — route it "
        "through `_enter_match_arm` instead:\n"
        + "\n".join(f"  {owner} calls {attr} at verifier.py:{line}"
                    for owner, attr, line in stray)
    )

    # ... and the seam really does call all four, so the scan above is not
    # green because the names have been renamed out from under it.
    seam = next(
        fn for fn in py_ast.walk(tree)
        if isinstance(fn, py_ast.FunctionDef)
        and fn.name == "_enter_match_arm"
    )
    called = {
        node.func.attr for node in py_ast.walk(seam)
        if isinstance(node, py_ast.Call)
        and isinstance(node.func, py_ast.Attribute)
    }
    assert watched <= called, f"the seam stopped composing: {watched - called}"


# ---------------------------------------------------------------------------
# A refinement the solver cannot STATE is not modelled (review J1)
# ---------------------------------------------------------------------------

#: `L2`'s outer level calls `int_to_float`, which is outside the decidable
#: fragment, so `_translate_refined_predicate` declines the WHOLE chain —
#: spec §2.6.4 cause 3.  Its inner level still forbids 0.
_UNSTATABLE = """\
type L1 = {{ @Int | @Int.0 > 0 }};
type L2 = {{ @L1 | int_to_float(@L1.0) > 0.0 }};

private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{{
  1
}}

private fn mk(@Int -> @Option<L2>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{{
  Some(@Int.0)
}}

public fn use_it(@Int -> {ret})
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures({post})
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@L2) -> {body},
    None -> {fallback}
  }}
}}
"""

#: consumer -> (return type, postcondition, arm body, other arm, the kind
#: whose verdict this cell reads, the verdict it must read).
_UNSTATABLE_CASES = {
    "div": ("@Int", "true", "100 / @L2.0", "0", "div_zero", ("tier3", None)),
    "ensures": ("@Int", "@Int.result > 0", "@L2.0", "1", "ensures",
                ("tier3", "E522")),
    # The arm's payload is a value the walk cannot know, so its call's
    # precondition is a check the run cannot make: Tier 3, never refuted.
    "call_pre": ("@Int", "true", "needs_pos(@L2.0)", "0", "call_pre",
                 ("tier3", "E532")),
    # Two records here, and both are the tip's: the PRODUCER's own
    # construction (unguarded, E506) and the arm's store.
    "store": ("@Option<L1>", "true", "Some(@L2.0)", "None", "refine_bind",
              [("tier3_unguarded", "E506"), ("tier3", "E506")]),
}


@pytest.mark.parametrize("consumer", sorted(_UNSTATABLE_CASES))
def test_1403_an_unstatable_refinement_is_not_a_counterexample(
    tmp_path: Path, consumer: str,
) -> None:
    """RED before: modelling a refinement whose predicate cannot be stated.

    A refinement's Z3 sort is its base's and its predicate is carried
    separately, so unwrapping the carrier while the predicate stays
    untranslated leaves a term with NOTHING said about the value it holds.
    The solver is then free to choose a value the type forbids, and it does:
    with the whole-chain unwrap and no statability question, all four
    consumers below refused this program — `100 / @L2.0` with the divisor 0,
    which `L1` excludes and `vera run` never produces (review of PR #1415,
    J1).

    The cure is not to filter such a counterexample at each site that might
    produce one, but not to create the term: the question "does this
    refinement's whole predicate translate, at every depth?" is asked once
    and the SORT derivation reads it, so an unstatable refinement keeps the
    `?` key and the `None` sort it had before a chain could be unwrapped at
    all.  A chain whose levels all translate still unwraps — that is what the
    `chain` row of the grid above measures, and it is why this is not a
    revert.

    Every cell is the verdict `release/v0.2.0` gives, because the program was
    always accepted; what changed is that this head no longer refuses it.
    """
    ret, post, body, fallback, kind, verdict = _UNSTATABLE_CASES[consumer]
    src = _UNSTATABLE.format(
        ret=ret, post=post, body=body, fallback=fallback)
    path = _tree(tmp_path, {"p": src})["p"]
    result = _verify(path)
    assert result["ok"] is True, result["diagnostics"]
    hits = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == kind and o["status"] != "verified"
    ]
    expected = ([] if verdict is None
                else verdict if isinstance(verdict, list) else [verdict])
    assert hits == expected, _triples(result)


def test_1403_an_unstatable_refinement_still_runs_and_still_refuses(
    tmp_path: Path,
) -> None:
    """The two directions that keep the cells above from being a free pass.

    Not modelling a value costs precision, so the pair that matters is: the
    program the head refused RUNS and returns what the refutation said was
    impossible, and an `ensures` over such a value does NOT prove.
    """
    ret, post, body, fallback, _kind, _v = _UNSTATABLE_CASES["div"]
    path = _tree(tmp_path / "run", {"p": _UNSTATABLE.format(
        ret=ret, post=post, body=body, fallback=fallback)})["p"]
    run = _cli("run", str(path), "--fn", "use_it", "--", "4")
    assert run.returncode == 0, run.stderr
    assert run.stdout.strip().endswith("25"), run.stdout

    # ... and the false-proof direction: an `ensures` the value cannot
    # support must not be proved by the absence of a model for it.
    false_post = _UNSTATABLE.format(
        ret="@Int", post="@Int.result > 5", body="@L2.0", fallback="6")
    bad = _verify(_tree(tmp_path / "neg", {"p": false_post})["p"])
    tail = [
        (o["status"], o.get("error_code")) for o in bad["obligations"]
        if o["kind"] == "ensures"
    ]
    assert ("verified", None) != tail[-1], _triples(bad)


# ---------------------------------------------------------------------------
# The unestablished REASON reaches every route that withholds (review J2/J3)
# ---------------------------------------------------------------------------

_REFUTING_HELPER = """\
type Pos = {{ @Int | @Int.0 > 0 }};

{top}public fn caller(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{{
  match helper(@Int.0) {{
    Some(@Pos) -> 100 / @Pos.0,
    None -> 1
  }}
}}
{where}"""

_HELPER_BODY = """  fn helper(@Int -> @Option<Pos>)
    requires(true)
    ensures(true)
    effects(pure)
  {
    Some(0 - 5)
  }
"""


@pytest.mark.parametrize(
    "spelling", ["where-helper", "top-level"],
)
def test_1403_the_withheld_reason_reaches_the_where_helper_route(
    tmp_path: Path, spelling: str,
) -> None:
    """The same refuted producer earns the same wording either way it is spelt.

    `_scrutinee_is_disclosed_call` has three routes to "yes, withheld" — the
    bare name, the module manifest, and a `where` helper this run found to be
    forwarding.  Two of them stamped the REASON; the third answered yes
    without one, so `_withheld_phrase` fell back to its "disclosed" default
    and a producer whose own obligation the run PROVED FALSE was described as
    one it "could neither prove nor guard" — but only when it was written as
    a helper (review of PR #1415, J2).

    Both spellings are one cell because the top-level one is the control:
    it is the wording the helper one has to match, and it passed throughout.

    This is also the only reader of `unestablished_reasons`' owner-keyed
    spelling (J3): the entry for a helper is keyed by `disclosed_key(name,
    owner)`, the same key this route tests membership with, so reverting
    that keying to the bare name makes the lookup miss and this cell reds.
    """
    if spelling == "where-helper":
        src = _REFUTING_HELPER.format(
            top="", where="where {\n" + _HELPER_BODY + "}\n")
    else:
        src = _REFUTING_HELPER.format(
            top=_HELPER_BODY.replace("  fn ", "private fn ").replace(
                "\n    ", "\n  ").replace("\n  {", "\n{").replace(
                "\n  }", "\n}") + "\n",
            where="")
    result = _verify(_tree(tmp_path / spelling, {"p": src})["p"])
    assert ("refine_bind", "violated", "E505") in _triples(result), (
        f"the producer stopped being refuted, so this cell is vacuous: "
        f"{_triples(result)}"
    )
    assert ("div_zero", "tier3", "E534") in _triples(result), _triples(result)
    e534 = [w for w in result["warnings"] if w.get("error_code") == "E534"]
    assert len(e534) == 1, [w.get("error_code") for w in result["warnings"]]
    assert "proved FALSE" in e534[0]["description"], e534[0]["description"]
    assert "could neither prove nor guard" not in e534[0]["description"], (
        e534[0]["description"]
    )


def test_1403_the_reason_map_is_keyed_the_way_the_set_is() -> None:
    """`unestablished_reasons` spells its keys the way `disclosed_fn_names`
    does, because the two are read together.

    The set answers "is this producer withheld" and the map answers "and
    why"; a key spelled two ways makes the second question miss for exactly
    the names the first one finds — a `where` helper, whose bare name means a
    different function under every owner.  Stated as a unit equality so the
    pairing is asserted rather than inferred from one program.
    """
    from vera.obligations.core import ProofObligation
    from vera.verifier import (
        disclosed_fn_names, disclosed_key, unestablished_reasons,
    )

    obls = [
        ProofObligation(
            fn_name="helper", kind="refine_bind", status="violated",
            expr_text="x", line=1, column=1, error_code="E505",
            owner="caller",
        ),
        ProofObligation(
            fn_name="mk", kind="nat_bind", status="tier3_unguarded",
            expr_text="y", line=2, column=1, error_code="E504",
        ),
    ]
    reasons = unestablished_reasons(obls)
    assert set(reasons) == set(disclosed_fn_names(obls)), (
        f"the map and the set disagree about how a name is spelled: "
        f"{sorted(reasons)} vs {sorted(disclosed_fn_names(obls))}"
    )
    assert reasons[disclosed_key("helper", "caller")] == "refuted"
    assert reasons[disclosed_key("mk", "")] == "disclosed"


# ---------------------------------------------------------------------------
# Where the refutation gate is NOT consulted, and why that is not reachable
# ---------------------------------------------------------------------------

_PLACEHOLDER_ENSURES = """\
public fn probe(@Unit -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    match get(()) {
      Some(@Int) -> @Int.0,
      None -> 1
    }
  }
}
"""

_PLACEHOLDER_CALL_PRE = """\
private fn needs_pos(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  1
}

public fn probe(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Option<Int>>](@Option<Int> = Some(9)) {
    get(@Unit) -> { resume(@Option<Int>.0) },
    put(@Option<Int>) -> { resume(()) }
  } in {
    match get(()) {
      Some(@Int) -> needs_pos(@Int.0),
      None -> 0
    }
  }
}
"""


@pytest.mark.parametrize(
    "source,kind,verdict",
    [
        pytest.param(_PLACEHOLDER_ENSURES, "ensures", ("tier3", "E522"),
                     id="postcondition-demotes-first"),
        pytest.param(_PLACEHOLDER_CALL_PRE, "call_pre", ("tier3", "E532"),
                     id="call-precondition-is-never-reached"),
    ],
)
def test_1403_a_placeholder_never_becomes_a_counterexample(
    tmp_path: Path, source: str, kind: str, verdict: tuple | None,
) -> None:
    """The two refutation sites with no gate, pinned at WHY they are safe.

    `_contains_opaque_shadow` and the satisfiability re-ask behind it are
    consulted at the `refine_bind` and primitive-operation sites, and NOT at
    the postcondition's `violated` branch or at the call-precondition
    violation the SMT layer drains.  That unevenness would matter if a
    tracked placeholder could reach either as a counterexample.  Measured,
    neither can, and for two different reasons — which is the thing worth
    pinning, since "no cell fails" would otherwise be the only evidence:

    * the postcondition path has its own opaque detection and demotes to
      `tier3`/**E522** ("the function body binds an effect-operation value
      the verifier models opaquely") before any refutation is attempted; and
    * the arm's call precondition is recorded `tier3`/**E532**: the walk
      reaches the call (#1480), and the call-site check demotes a
      precondition over a value the walk cannot know rather than refuting
      it (`SmtContext.opaque_term`) — the gate at that site.

    If either verdict ever becomes `violated`, the gate is needed at that
    site and the question is no longer local to this class.
    """
    result = _verify(_tree(tmp_path, {"p": source})["p"])
    assert result["ok"] is True, result["diagnostics"]
    hits = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == kind and o["status"] != "verified"
    ]
    assert hits == ([verdict] if verdict is not None else []), _triples(result)


# ---------------------------------------------------------------------------
# The gate decides CHAINS, and decides nothing else (review L1/L2)
# ---------------------------------------------------------------------------

_ORDER = """\
type C1 = {{ @Int | @Int.0 > 0 }};
type C2 = {{ @C1 | Some(@C1.0) == None }};

private fn mk(@Int -> @Option<C2>)
  requires(true)
  ensures(true)
  effects(pure)
{{
{pre}  Some(@Int.0)
}}

public fn use_it(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match mk(@Int.0) {{
    Some(@C2) -> @C2.0,
    None -> 0
  }}
}}
"""

#: A SINGLE refinement whose predicate cannot be stated.  Its carrier is
#: modelled without it, which is a false refusal — and deliberately left
#: alone here; see the cell.
_SINGLE_UNSTATABLE = """\
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


def test_1403_the_statability_gate_decides_chains_only(tmp_path: Path) -> None:
    """The gate's boundary, in the two directions that could over-reach.

    It decides ONE thing: whether to unwrap a CHAIN.  Two neighbours are
    deliberately outside it, and this cell is what stops the boundary
    drifting:

    * a SINGLE refinement whose predicate cannot be stated keeps the
      behaviour it has on `release/v0.2.0` and on `main` — its carrier is
      modelled without its predicate and `100 / @U.0` is refused E526 with
      the divisor 0, on a program that runs and returns 25.  That is a real
      defect and it is [#1470](https://github.com/aallan/vera/issues/1470),
      whose fix is one under-constrained gate consulted by every refutation
      site.  Closing it HERE would trade that false refusal for lost Tier-1
      proofs at every parameter and result of such a type, on obligations
      that never needed the predicate — a trade this change is not designed
      for and the corpus cannot measure, since it declares no such
      refinement.
    * the ORDER sensitivity of predicate translation is also outside it.  A
      chain whose predicate names a constructor translates only once that
      constructor's sort exists, so an unrelated earlier `let` changes the
      verdict — `tier3_unguarded`/E506 without it, `violated`/E505 with it.
      That is true on `release/v0.2.0` too, unchanged here: the gate asks
      the same question the predicate translation already answered, and a
      NO is never memoised, so the gate adds no order sensitivity of its own
      and removes none.  Asserting both variants pins that.
    """
    plain = _verify(_tree(tmp_path / "plain", {
        "p": _ORDER.format(pre="")})["p"])
    letfirst = _verify(_tree(tmp_path / "letfirst", {
        "p": _ORDER.format(pre="  let @Option<Int> = Some(@Int.0);\n")})["p"])
    binds = [
        [(o["status"], o.get("error_code")) for o in r["obligations"]
         if o["kind"] == "refine_bind" and o["status"] != "verified"]
        for r in (plain, letfirst)
    ]
    assert binds == [[("tier3_unguarded", "E506")], [("violated", "E505")]], (
        f"the pre-existing order sensitivity of predicate translation moved. "
        f"If the accepted variant is now refused like its twin, #1470 has "
        f"been fixed and this half of the cell should be rewritten to assert "
        f"order independence rather than pin its absence: {binds}"
    )

    single = _verify(_tree(tmp_path / "single", {"p": _SINGLE_UNSTATABLE})["p"])
    assert single["ok"] is False, _triples(single)
    assert [
        (o["status"], o.get("error_code")) for o in single["obligations"]
        if o["kind"] == "div_zero"
    ] == [("violated", "E526")], _triples(single)
    run = _cli("run", str(_tree(tmp_path / "single", {
        "p": _SINGLE_UNSTATABLE})["p"]), "--fn", "use_it", "--", "4")
    assert run.returncode == 0 and run.stdout.strip().endswith("25"), (
        f"#1470's program stopped running clean, so the refusal may no "
        f"longer be false: {run.stdout} {run.stderr}"
    )
