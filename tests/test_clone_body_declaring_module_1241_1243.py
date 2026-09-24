"""#1241 + #1243: an imported clone's body calls its OWN module's functions.

A public generic in `glib` whose body calls `glib`'s private `need` is
cloned by the importer and compiled into the importer's flat module.  Both
consumers of that clone body then resolved the bare name `need` in the
IMPORTER's namespace:

* the verifier (#1241) — `_scoped_fn_lookup` falls through to
  `self.env.lookup_function`, and `_declaring_module_scope` swapped the
  naming env and the source buffer but not the function registry; and
* codegen (#1243) — the clone-emission door was the one door that did not
  thread the module's intra-rename map, so a bare sibling call landed on
  the importer's same-named function rather than the module's own `<path>::…`
  emission.

The checker's answer is the module's own (spec §8.5.1), proven by a
type-discriminating probe: `glib`'s `need(@Int -> @Int)` beside an
importer's `need(@Int -> @Bool)` checks clean, which only types if
`glib`'s is meant.

THE TWO HALVES CANNOT LAND APART, and the tests are written so that
neither passes alone.  Fixing the verifier alone converts today's
aligned-but-both-wrong state into a FALSE TIER-1: `vera verify` goes
clean while the compiled program still runs the importer's function and
traps on the postcondition it just proved.  Fixing codegen alone leaves a
false REJECTION: the run is right and `vera verify` still refuses a valid
program.  Every case below therefore asserts the verify verdict AND the
runtime value in one test.

The oracle is `glib` STANDALONE — the same module verified and run on its
own — so no expected value here is read off what the importer happens to
produce.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera

# The subprocess must run the SAME compiler this session imported.  A
# checkout that is not the one the editable install points at — a linked
# git worktree, say — otherwise has `python -m vera.cli` resolve the OTHER
# tree, and the cases below would report on a compiler nobody edited.  A
# no-op wherever the two coincide.
_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")
    return tmp_path


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    existing = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = (
        f"{_PKG_PARENT}{os.pathsep}{existing}" if existing else _PKG_PARENT
    )
    # A finite timeout: a hung CLI must fail this test rather than wedge the
    # suite.  Generous enough for a cold Z3 verify on a slow CI runner.
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, timeout=300,
    )


def _verify_codes(path: Path) -> list[str]:
    """The error codes `vera verify --json` reports for *path*.

    A crash or a non-JSON stdout is surfaced as itself rather than as a
    `JSONDecodeError` with no context: the whole point of these cases is
    which diagnostics appear, and "the CLI died" must not read as "no
    diagnostics".
    """
    proc = _cli("verify", "--json", str(path))
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        msg = (
            f"`vera verify --json` produced no JSON (exit {proc.returncode}): "
            f"{exc}\n--- stdout ---\n{proc.stdout[-600:]}"
            f"\n--- stderr ---\n{proc.stderr[-600:]}"
        )
        raise AssertionError(msg) from None
    return [d["error_code"] for d in payload["diagnostics"]]


def _run_value(path: Path, fn: str | None = None) -> str:
    """`vera run`'s last stdout line, or a marker naming how it failed.

    Every non-value outcome gets a distinct marker so an assertion failure
    says which one happened: a non-zero exit, and — separately — a zero exit
    that printed nothing, which would otherwise raise `IndexError` off the
    end of an empty `splitlines()` and hide the real story.
    """
    args = ["run", str(path)]
    if fn is not None:
        args += ["--fn", fn]
    proc = _cli(*args)
    if proc.returncode != 0:
        return f"FAILED: {(proc.stdout + proc.stderr).strip()[-400:]}"
    lines = proc.stdout.strip().splitlines()
    if not lines:
        return f"NO OUTPUT (exit 0); stderr: {proc.stderr.strip()[-200:]}"
    return lines[-1]


# --- the value shape -------------------------------------------------
# `glib.gen` promises 111 and its own `need` delivers it.  The importer
# declares a DIFFERENT `need` promising (and returning) 999, and calls it
# directly as well, so `main` is 111 + 999 = 1110 — a total that
# distinguishes the right routing (1110) from the wrong one (999 + 999 =
# 1998), rather than merely from a crash.
_GLIB_VALUE = """
private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  111
}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  need(0)
}

public fn glib_main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""

_APP_VALUE = """
import glib(gen);

private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 999)
  effects(pure)
{
  999
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1) + need(0)
}
"""

# --- the type-discriminating shape -----------------------------------
# The module is the SAME one the value shape uses — all the discrimination
# lives on the importer's side, so there is one definition of `glib` to
# keep correct rather than two that could drift apart.  The importer's
# `need` returns `@Bool` (i32) where `glib`'s returns `@Int` (i64).  The
# checker accepts the program, which by itself proves the clone body means
# glib's `need`; routing to the importer's instead emitted invalid WASM
# from that check-green source.
_APP_TYPED = """
import glib(gen);

private fn need(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  true
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if need(0) then { gen(1) } else { 0 }
}
"""

# --- the two-hop shape ------------------------------------------------
# The clone does not call the shadowed function directly: it calls `mid`,
# which calls `need`.  Both are top-level privates of the module, and the
# IMPORTER declares a same-named pair, so the routing has to hold for the
# call the clone makes AND for the one that call makes in turn.
_GLIB_CHAIN = """
private fn mid(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  need(0)
}

private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  111
}

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == 111)
  effects(pure)
{
  mid(0)
}

public fn glib_main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""

_APP_CHAIN = """
import glib(gen);

private fn need(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 999)
  effects(pure)
{
  999
}

private fn mid(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 999)
  effects(pure)
{
  999
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1) + need(0)
}
"""


def test_declaring_module_oracle_standalone(tmp_path: Path) -> None:
    """`glib` on its own: verify clean, `gen` returns 111.

    The oracle for every expectation below.  If this ever moves, the
    module's own meaning changed and the cross-module expectations are
    measuring the wrong thing.
    """
    _write(tmp_path, {"glib.vera": _GLIB_VALUE})
    assert _verify_codes(tmp_path / "glib.vera") == []
    assert _run_value(tmp_path / "glib.vera", "glib_main") == "111"


@pytest.mark.parametrize(
    ("glib_src", "app_src", "expected"),
    [
        pytest.param(_GLIB_VALUE, _APP_VALUE, "1110", id="private_callee"),
        pytest.param(_GLIB_CHAIN, _APP_CHAIN, "1110", id="two_hop_callee"),
    ],
)
def test_clone_body_resolves_in_its_own_module(
    tmp_path: Path, glib_src: str, app_src: str, expected: str,
) -> None:
    """Verify verdict AND runtime value, together — the pairing assertion.

    The verifier half alone makes the first assertion pass and leaves the
    second failing on a postcondition trap (a false Tier-1: proved clean,
    violated at run).  The codegen half alone makes the second pass and
    leaves the first refusing a valid program.  Only both together.
    """
    _write(tmp_path, {"glib.vera": glib_src, "app.vera": app_src})
    assert _verify_codes(tmp_path / "app.vera") == [], (
        "false rejection: the clone's contract was proved against the "
        "IMPORTER's same-named function"
    )
    assert _run_value(tmp_path / "app.vera") == expected, (
        "the compiled clone called the importer's function"
    )


def test_type_discriminating_callee_compiles(tmp_path: Path) -> None:
    """A DIFFERENTLY TYPED importer function of the same name.

    `glib`'s `need` returns `@Int` (i64) and the importer's returns
    `@Bool` (i32).  The checker accepts the program — which is itself the
    proof that the clone body means glib's `need` (§8.5.1) — so codegen
    must emit a module that loads and runs.  Routing to the importer's
    `@Bool` function instead emitted invalid WASM from that check-green
    source: `type mismatch: expected i64, found i32` at instantiation, so
    the failure is a trap on load rather than a wrong value.
    """
    _write(tmp_path, {"glib.vera": _GLIB_VALUE, "app.vera": _APP_TYPED})
    check = _cli("check", "--quiet", str(tmp_path / "app.vera"))
    assert check.returncode == 0, check.stdout + check.stderr
    assert _verify_codes(tmp_path / "app.vera") == []
    assert _run_value(tmp_path / "app.vera") == "111"


def test_unshadowed_callee_control(tmp_path: Path) -> None:
    """No same-named importer function: the bare emission was already right.

    This case worked before the fix and must keep working — it is what
    proves the defect is the SHADOWED name rather than cross-module calls
    in general, so a reroute that fired unconditionally (or a scope swap
    that lost the module's own registry) would show up here rather than
    passing either way.
    """
    app = """
import glib(gen);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gen(1)
}
"""
    _write(tmp_path, {"glib.vera": _GLIB_VALUE, "app.vera": app})
    assert _verify_codes(tmp_path / "app.vera") == []
    assert _run_value(tmp_path / "app.vera") == "111"
