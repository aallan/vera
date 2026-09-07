"""One sort for a refined payload, wherever a term is rebuilt (#1421).

`_adt_sort_key` names the Z3 sort a Vera ADT gets.  It classified each type
argument as primitive, ADT, or un-nameable — and a REFINEMENT is none of those,
so `Option<{ @Int | @Int.0 > 0 }>` was keyed `Option<?>` while every route that
resolved the same payload to its base keyed `Option<Int>`.  Two Z3 sorts for one
Vera type, and Z3 raises rather than returning an error when they meet: the
arms of `match mk(x) { Some(@PosInt) -> Some(@PosInt.0), None -> None }` have to
join under a `z3.If`, and the raise escaped as an `[E699]` internal compiler
error on a program `vera check` accepts.

The fix is in the derivation, not in a catch: a refinement contributes its
BASE.  That rule is already stated in `_vera_type_to_z3_sort` — "a
refinement's Z3 SORT is its base's sort; the predicate constrains values, not
the carrier set, and is enforced separately" — so `Option<{ @Int | P }>` and
`Option<Int>` are one sort and the two routes agree by construction.  What was
missing was ONE implementation of it.

The unwrap is ONE LEVEL and a chain is left unmodelled by design: the
predicate half of that rule stops at a primitive base, so stripping a chain
would supply a sort without the predicates and turn valid code into a false
E526.  See `strip_refinements`.

Same family as #884 (two Vera types colliding on one sort NAME) and #1360 (two
routes deriving different sorts for a nested constructor).  #1360 made the
crash emit a parseable envelope; this makes the sorts agree so there is no
crash to wrap.  #1424 is the same defect reached from a single module and is
closed by the same fix.

Four shapes crash on `release/v0.2.0`; the fifth is the unrefined control,
which never crashed and must not move.  Every cell asserts a REAL VERDICT,
not merely the absence of the crash: a
verifier that answered `E699` for these programs was unusable on them, and one
that answered "no obligations" would be hiding them.
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
    """`vera verify --json`, refusing an internal error as an answer.

    E699 is the envelope the compiler emits when it crashed.  A cell that only
    asserted the obligations it wanted would pass vacuously on a crash — there
    are no obligations to contradict it — so the gate is here, once, for every
    cell in the file.
    """
    proc = _cli("verify", "--json", str(path))
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope for {path.name} "
            f"(exit {proc.returncode})\n{proc.stdout[:400]}\n"
            f"{proc.stderr[-800:]}"
        ) from None
    internal = [
        d for d in result.get("diagnostics", [])
        if d.get("error_code") == "E699"
    ]
    assert not internal, (
        f"{path.name}: the verifier reported an INTERNAL ERROR rather than a "
        f"verdict — {internal[0]['description'][:200]}"
    )
    return result


def _checks(path: Path) -> bool:
    return _cli("check", "--quiet", str(path)).returncode == 0


def _kinds(result: dict) -> list[tuple[str, str, str | None]]:
    return [
        (o["kind"], o["status"], o.get("error_code"))
        for o in result["obligations"]
    ]


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

_POS = "type Pos = { @Int | @Int.0 > 0 };\n\n"

#: #1421, verbatim: an imported `Option<Nat>` rebuilt as an `Option<Pos>`.
_XMOD_LIB = """\
public fn mk(@Int -> @Option<Nat>)
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

_XMOD_MAIN = "import cb;\n\n" + _POS + """\
public fn relay(@Int -> @Option<Pos>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match cb::mk(@Int.0) {
    Some(@Nat) -> Some(nat_to_int(@Nat.0)),
    None -> None
  }
}
"""

#: #1424, verbatim: the same defect reached from one module.
_SAME_MODULE = """\
type PosInt = { @Int | @Int.0 > 0 };

private fn mk(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(float_to_int(@Float64.0))
}

public fn f(@Float64 -> @Option<PosInt>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match mk(@Float64.0) {
    Some(@PosInt) -> Some(@PosInt.0),
    None -> None
  }
}
"""

#: The rewrap happens inside a helper the caller passes a value to.
_WRAPPER = _POS + """\
private fn mk(@Int -> @Option<Pos>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

private fn rewrap(@Option<Pos> -> @Option<Pos>)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Option<Pos>.0 {
    Some(@Pos) -> Some(@Pos.0),
    None -> None
  }
}

public fn f(@Int -> @Option<Pos>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  rewrap(mk(@Int.0))
}
"""

#: The refinement is a TUPLE COMPONENT, rebuilt on its own — the nested
#: position #1360 exercised, with a refinement where it had a `Tuple`.
_TUPLE_COMPONENT = _POS + """\
private fn mk(@Int -> @Option<Tuple<Pos, Int>>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  Some(Tuple(@Int.0, 7))
}

public fn f(@Int -> @Option<Pos>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(Tuple(@Pos, @Int)) -> Some(@Pos.0),
    None -> None
  }
}
"""

#: The same shape with NO refinement anywhere — the control.
_CLEAN_CONTROL = """\
private fn mk(@Int -> @Option<Nat>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  int_to_nat(@Int.0)
}

public fn f(@Int -> @Option<Nat>)
  requires(@Int.0 > 0)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(@Nat) -> Some(@Nat.0),
    None -> None
  }
}
"""


# ---------------------------------------------------------------------------
# The two reported reproducers
# ---------------------------------------------------------------------------

def test_1421_the_cross_module_rewrap_gets_a_verdict(tmp_path: Path) -> None:
    """#1421 verbatim: `check` accepts it, so `verify` must answer it.

    And the answer is a real one rather than merely non-crashing: rebuilding
    an `Option<Nat>`'s payload as a `Pos` (`> 0`) is genuinely unsound — a
    `Nat` can be 0 — so the honest verdict is a refuted refinement binding,
    E505, with the counterexample that names it.
    """
    paths = _tree(tmp_path, {"cb": _XMOD_LIB, "ca": _XMOD_MAIN})
    assert _checks(paths["ca"]), "the fixture must be check-clean to be #1421"
    result = _verify(paths["ca"])
    assert ("refine_bind", "violated", "E505") in _kinds(result), _kinds(result)
    assert "E505" in [d.get("error_code") for d in result["diagnostics"]]


def test_1424_the_same_module_rewrap_gets_a_verdict(tmp_path: Path) -> None:
    """#1424 verbatim — the same defect, reached without an import.

    Kept beside #1421 rather than folded into it: the issue records the
    cross-module split as what put the two derivations apart, and this shows
    the split was incidental.  One fix closes both.
    """
    paths = _tree(tmp_path, {"wr": _SAME_MODULE})
    assert _checks(paths["wr"])
    result = _verify(paths["wr"])
    assert result["ok"] is True, result["diagnostics"]
    assert ("refine_bind", "tier3_unguarded", "E506") in _kinds(result), (
        _kinds(result)
    )


# ---------------------------------------------------------------------------
# The same rebuild reached three other ways
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "source,expected",
    [
        pytest.param(_WRAPPER, ("refine_bind", "verified", None),
                     id="through-a-wrapper"),
        pytest.param(_TUPLE_COMPONENT, ("refine_bind", "verified", None),
                     id="tuple-component"),
    ],
)
def test_1421_other_rebuild_routes_get_a_verdict(
    tmp_path: Path, source: str, expected: tuple[str, str, str | None],
) -> None:
    """A refined payload rebuilt through a helper, and out of a tuple.

    Both crash on `release/v0.2.0` and both are Tier-1 clean once the sort
    agrees — so the defect was the key, not any of the three routes.  The
    tuple case is #1360's nested position with a refinement where that issue
    had a `Tuple`, which is what makes the two one family.
    """
    result = _verify(_tree(tmp_path, {"p": source})["p"])
    assert result["ok"] is True, result["diagnostics"]
    assert expected in _kinds(result), _kinds(result)


def test_1421_the_unrefined_shape_is_unchanged(tmp_path: Path) -> None:
    """The control: the same rebuild with no refinement never crashed.

    It verifies clean before and after, which is what makes the cells above
    measure the refinement rather than the rebuild.
    """
    result = _verify(_tree(tmp_path, {"p": _CLEAN_CONTROL})["p"])
    assert result["ok"] is True, result["diagnostics"]
    assert not [k for k in _kinds(result) if k[1] == "violated"], _kinds(result)


# ---------------------------------------------------------------------------
# The derivation itself
# ---------------------------------------------------------------------------

def test_1421_a_refinement_keys_to_its_base() -> None:
    """The unit statement of the rule, under the two routes that disagreed.

    Asserted on both routes rather than only through programs, because the
    property is an EQUALITY between two spellings of one type: a refinement
    and its base have to produce the same key AND the same sort, or somewhere
    a `z3.If` joins two sorts.
    """
    from vera import ast
    from vera.smt import SmtContext, _adt_sort_key
    from vera.types import INT, AdtType, RefinedType, TypeVar

    pred = ast.BoolLit(value=True)
    pos = RefinedType(base=INT, predicate=pred)
    chain = RefinedType(base=pos, predicate=pred)
    smt = SmtContext()

    assert _adt_sort_key("Option", (INT,)) == "Option<Int>"
    assert _adt_sort_key("Option", (pos,)) == "Option<Int>"
    # ... and inside a nested ADT argument, the position #1360 exercised.
    assert _adt_sort_key(
        "Option", (AdtType("Tuple", (pos, INT)),),
    ) == "Option<Tuple<Int, Int>>"

    # A CHAIN keys `?`, and that asserts a REFUSAL rather than a capability.
    # `_translate_refined_predicate` reads `{ @Base | P }` with a primitive
    # base, so neither predicate of `{ { @Int | P } | Q }` is translated;
    # naming the sort `Option<Int>` would model the value as an unconstrained
    # `Int` and report `violated`/E526 on code the chain proves safe (review
    # of PR #1431, F1 — measured, and the program cell below is the witness).
    assert _adt_sort_key("Option", (chain,)) == "Option<?>"
    assert smt._vera_type_to_z3_sort(chain) is None
    # Both routes refuse TOGETHER, which is the agreement being bought here —
    # the single-refinement case is where they must both succeed.
    assert smt._vera_type_to_z3_sort(pos) is not None

    # A type variable is un-nameable for its own reason and stays so.
    assert "?" in _adt_sort_key("Option", (TypeVar("T"),))


def test_1421_an_unnameable_key_is_still_refused() -> None:
    """A PIN, not a mutation-killing cell — recorded as such.

    `_parse_adt_sort_key` refuses a key containing `?` rather than
    round-tripping it into a confident but wrong instantiation.  I could not
    construct a mutation of the fix that this cell kills and the others do
    not, so it earns its place by pinning a contract the fix leans on, not by
    discriminating (review of PR #1431, F5).  Removing the `?` guard makes
    `_parse_adt_sort_key` return an `AdtType` for a type it cannot name, which
    is what this refuses to let happen silently.
    """
    from vera.smt import SmtContext

    assert SmtContext._parse_adt_sort_key("Option<?>") is None
    assert SmtContext._parse_adt_sort_key("Option<Int>") is not None


# ---------------------------------------------------------------------------
# The chain is refused on BOTH routes, and that refusal is load-bearing
# ---------------------------------------------------------------------------

#: `Small` refines `Pos` refines `Int` — a refinement over a refinement, as a
#: nested type argument, with a division the chain's own predicates prove safe.
_TUPLE_CHAIN = """\
type Pos = { @Int | @Int.0 > 0 };
type Small = { @Pos | @Pos.0 < 10 };

private fn mk(@Int -> @Option<Tuple<Small, Int>>)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  Some(Tuple(@Int.0, 7))
}

public fn f(@Int -> @Int)
  requires(@Int.0 > 0 && @Int.0 < 10)
  ensures(true)
  effects(pure)
{
  match mk(@Int.0) {
    Some(Tuple(@Small, @Int)) -> 100 / @Small.0,
    None -> 1
  }
}
"""


def test_1421_a_refinement_chain_stays_unmodelled(tmp_path: Path) -> None:
    """Stripping the WHOLE chain would be a false E526 — this is the witness.

    The obvious reading of "a refinement contributes its base" is to strip the
    chain, and it is wrong.  The predicate half of the rule stops at a
    primitive base — `_translate_refined_predicate` reads `{ @Base | P }` with
    `@Base` primitive — so for `{ { @Int | P } | Q }` neither predicate is
    translated.  Strip the chain and the SORT succeeds while the predicates
    stay absent: the payload becomes an unconstrained `Int` and
    `100 / @Small.0` is reported `violated`/**E526** although `Small` proves
    the divisor lies in `(0, 10)`.  A false positive on valid code, which is
    the #854/#884 class this project treats as a defect.

    So both routes refuse a chain together, and this program is the
    discriminator: it reads `div_zero`/`tier3` on `release/v0.2.0` and on this
    branch, and flips to E526 the moment `strip_refinements` loops.  That is
    the mutation this cell exists to kill (review of PR #1431, F1/F4).

    Conjoining a chain's predicates so the strip becomes correct is #1434.
    """
    result = _verify(_tree(tmp_path, {"p": _TUPLE_CHAIN})["p"])
    assert result["ok"] is True, result["diagnostics"]
    div = [
        (o["status"], o.get("error_code")) for o in result["obligations"]
        if o["kind"] == "div_zero"
    ]
    assert div == [("tier3", None)], (
        f"a refinement chain stopped being refused — an E526 here is the "
        f"unconstrained-Int false positive: {_kinds(result)}"
    )
    # The chain's own binding is honestly disclosed rather than proved.
    assert ("refine_bind", "tier3_unguarded", "E506") in _kinds(result), (
        _kinds(result)
    )
