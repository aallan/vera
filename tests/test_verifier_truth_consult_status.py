"""Stream B — the verifier consults the statuses it computes.

An obligation's status is not a label; it is a claim about what the compiled
program does.  `tier3` says "a runtime guard covers this"; `tier3_unguarded`
says "nothing does, and here is the disclosure".  This file holds the cases
where a status was computed and then not consulted by the part that should
have acted on it.

#1362 — the call-argument site hardcoded `guarded=True` on the premise that a
concrete `@Nat` formal is guarded by codegen.  That is true of every user
function and false of `nat_to_int`, which is a representation identity (`Nat`
and `Int` are both `i64`) with no lowering step for a guard to attach to.  A
refutable argument hides the misclassification — the obligation is `violated`
either way — so it surfaces only when the value is OPAQUE, which is what a
handler-clause payload binder supplies.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from vera.environment import TypeEnv
from vera.verifier import _NAT_ARG_UNGUARDED_BUILTINS

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
        env=env, timeout=300,
    )


def _verify(tmp_path: Path, source: str, name: str = "p.vera") -> dict:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"verify emitted no envelope (exit {proc.returncode})\n"
            f"{proc.stdout[:400]}\n{proc.stderr[-600:]}"
        ) from None


def _wat(tmp_path: Path, source: str, name: str = "w.vera") -> str:
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("compile", "--wat", str(p))
    return proc.stdout


# The issue's own repro, verbatim.
_1362_REPRO = """\
public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Nat) -> { nat_to_int(@Nat.0) }
  } in {
    throw(@Int.0)
  }
}
"""


def test_1362_unguarded_narrowing_is_disclosed_not_claimed_guarded(
    tmp_path: Path,
) -> None:
    """The issue's repro: `tier3_unguarded` + E504, never plain `tier3`.

    `tier3` is counted in `tier3_runtime`, whose meaning is runtime-guarded.
    Claiming it here overcounts guarded obligations AND skips the disclosure
    machinery that exists for exactly this case.
    """
    result = _verify(tmp_path, _1362_REPRO)
    binds = [o for o in result["obligations"] if o["kind"] == "nat_bind"]
    assert len(binds) == 1, [(o["kind"], o["status"]) for o in result["obligations"]]
    assert binds[0]["status"] == "tier3_unguarded", (
        f"status {binds[0]['status']!r} claims a runtime guard; the emitted "
        f"module has none"
    )
    assert "E504" in [w.get("error_code") for w in result["warnings"]]


def test_1362_the_claim_and_the_module_agree(tmp_path: Path) -> None:
    """The claim is checked against the artifact, not against itself.

    `tier3_unguarded` asserts the emitted module plants no guard here — so the
    module is inspected.  Without this the status could be renamed without
    being made true.
    """
    wat = _wat(tmp_path, _1362_REPRO)
    assert wat.startswith("(module"), wat[:300]
    assert "unreachable" not in wat, (
        "the module DOES carry a guard — the obligation should then be "
        f"`tier3`, not disclosed:\n{wat}"
    )
    # And the value the guard would have caught flows through untrapped.
    p = tmp_path / "r.vera"
    p.write_text(_1362_REPRO, encoding="utf-8")
    run = _cli("run", str(p), "--fn", "f", "--", "-7")
    assert run.returncode == 0 and run.stdout.strip() == "-7", (
        f"expected the negative to pass through unguarded: {run.stdout!r} "
        f"{run.stderr[-300:]!r}"
    )


def test_1362_a_guarded_callee_is_still_tier3(tmp_path: Path) -> None:
    """The over-rejection control, and the axis the fix turns on.

    The SAME opaque clause binder passed to a USER function's `@Nat` formal is
    genuinely guarded, so it must stay `tier3`.  Without this cell the fix
    would be satisfied by disclosing every call argument.
    """
    source = """\
private fn takes(@Nat -> @Int)
  requires(true) ensures(true) effects(pure)
{
  nat_to_int(@Nat.0)
}

public fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[Exn<Int>] {
    throw(@Nat) -> { takes(@Nat.0) }
  } in {
    throw(@Int.0)
  }
}
"""
    result = _verify(tmp_path, source, name="g.vera")
    binds = [o for o in result["obligations"] if o["kind"] == "nat_bind"]
    assert binds and all(o["status"] == "tier3" for o in binds), (
        f"a guarded callee was disclosed as unguarded: "
        f"{[(o['kind'], o['status']) for o in binds]}"
    )
    wat = _wat(tmp_path, source, name="g2.vera")
    assert "unreachable" in wat, "control claims a guard the module lacks"


def _nat_param_builtins() -> list[tuple[str, int]]:
    """Every builtin with a `@Nat` parameter, from the LIVE registry.

    Enumerated rather than listed, so a builtin added tomorrow joins the
    differential by existing.
    """
    env = TypeEnv()
    out: list[tuple[str, int]] = []
    for name, info in sorted(env.functions.items()):
        params = getattr(info, "param_types", None) or ()
        for i, t in enumerate(params):
            if getattr(t, "name", "") == "Nat":
                out.append((name, i))
                break
    return out


def test_1362_the_nat_builtin_registry_is_covered() -> None:
    """The differential below is only as good as its enumeration.

    Guards against a vacuous pass: if the registry scan silently returned
    nothing, every parity assertion would hold for no reason.
    """
    found = _nat_param_builtins()
    assert len(found) >= 8, found
    names = {n for n, _ in found}
    assert "nat_to_int" in names
    assert _NAT_ARG_UNGUARDED_BUILTINS <= names, (
        f"the verifier's unguarded set names a builtin that no longer takes a "
        f"@Nat: {_NAT_ARG_UNGUARDED_BUILTINS - names}"
    )


# One narrowing call per `@Nat` builtin.  A builtin with no shape here fails
# the coverage assertion below rather than being silently skipped, so a new
# `@Nat` builtin cannot join the registry without joining the differential.
_NARROWING_CALL = {
    "nat_to_int": ("@Int", "nat_to_int(@Int.0)"),
    "nat_to_string": ("@Int", "string_length(nat_to_string(@Int.0))"),
    "string_from_char_code": (
        "@Int", "string_length(string_from_char_code(@Int.0))"),
    "string_pad_end": (
        "@Int", 'string_length(string_pad_end("ab", @Int.0, "x"))'),
    "string_pad_start": (
        "@Int", 'string_length(string_pad_start("ab", @Int.0, "x"))'),
    "string_repeat": ("@Int", 'string_length(string_repeat("ab", @Int.0))'),
    "string_slice": (
        "@Int", 'string_length(string_slice("abcdef", @Int.0, 2))'),
    "md_has_heading": (
        "@MdBlock, @Int",
        "if md_has_heading(@MdBlock.0, @Int.0) then { 1 } else { 0 }"),
}


def _guard_delta(tmp_path: Path, name: str) -> int:
    """Guards codegen plants for *name*'s narrowing argument.

    Measured as a DELTA against the same program with an already-`@Nat`
    argument: the module carries guards for other reasons, so an absolute
    count would not isolate this one.
    """
    params, call = _NARROWING_CALL[name]
    narrowing = (
        f"public fn f({params} -> @Int)\n"
        f"  requires(true) ensures(true) effects(pure)\n{{\n  {call}\n}}\n"
    )
    control = narrowing.replace("@Int.0", "@Nat.0").replace(
        params, params.replace("@Int", "@Nat"))
    a = _wat(tmp_path, narrowing, name=f"{name}_n.vera")
    b = _wat(tmp_path, control, name=f"{name}_c.vera")
    assert a.startswith("(module"), f"{name}: narrowing fixture failed:\n{a[:300]}"
    assert b.startswith("(module"), f"{name}: control fixture failed:\n{b[:300]}"
    return a.count("unreachable") - b.count("unreachable")


def test_1362_every_nat_builtin_has_a_differential_shape() -> None:
    """Coverage: the shape map matches the live registry.

    A builtin gaining a `@Nat` parameter must gain a fixture, or the parity
    differential below would quietly stop covering it.
    """
    registered = {n for n, _ in _nat_param_builtins()}
    missing = registered - set(_NARROWING_CALL)
    assert not missing, f"no differential shape for: {sorted(missing)}"


@pytest.mark.parametrize("name", sorted(_NARROWING_CALL))
def test_nat_arg_guard_inventory_matches_codegen(
    tmp_path: Path, name: str,
) -> None:
    """PARITY: the verifier's guard inventory equals codegen's behaviour.

    The classification of an undecided `@Nat` call argument turns on whether
    codegen plants a guard, and the two live in different components — a unit
    test on either side cannot see them disagree, which is what #1205's
    discipline is about.  So the truth is derived from the emitted WAT and
    compared against the set the verifier reads.
    """
    codegen_guards = _guard_delta(tmp_path, name) > 0
    verifier_says_guarded = name not in _NAT_ARG_UNGUARDED_BUILTINS
    assert codegen_guards == verifier_says_guarded, (
        f"{name}: codegen "
        f"{'guards' if codegen_guards else 'does NOT guard'} its @Nat "
        f"argument, but the verifier classifies it as "
        f"{'guarded' if verifier_says_guarded else 'unguarded'} — the two "
        f"sides have drifted"
    )
