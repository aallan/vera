"""#1360: a `Tuple` nested inside a constructor translates, and `--json` always envelopes.

`let @Option<Tuple<Nat, Int>> = Some(Tuple(@Nat.0, 1234));` is `vera check`-green
and used to kill `vera verify` with a raw `z3.z3types.Z3Exception: Sort mismatch`
— a Python traceback, exit 1 — while `vera compile` and `vera run` handled it
fine.  Under `--json` the process emitted NO envelope at all, so a machine
consumer got empty stdout where it expects a diagnostic object.

TWO HALVES, deliberately independent.

1. THE TRANSLATION DEFECT.  The two sorts are derived by different routes and
   disagree.  A nested `Tuple` argument is built by the variadic-tuple branch of
   `_translate_ctor_call`, which keys its synthesised sort on the arguments'
   Z3 sorts — and `Nat` reads back as `Int`, since both are one `IntSort` — so it
   always spells `Int`.  The enclosing `Some`'s sort is resolved through
   `_resolve_pinned_sort`, which prefers a cached instantiation equal to the pin
   MODULO `Nat`<->`Int`.  That preference is sound at a SCALAR position, where
   the two spellings share one Z3 sort, and unsound at a position that is itself
   a datatype: post-#884 `Tuple<Int, Nat>` and `Tuple<Int, Int>` are distinct
   injective sorts.  So the constructor's domain named one datatype and the
   argument term was built as the other.  Measured at the crash:

       arg sort   : Tuple_LInt_CInt_R      (what the term was built as)
       ctor domain: Tuple_LInt_CNat_R      (what the resolved sort expects)

   Note the `Nat` appears even in an all-`Int` program: the literal `1234` types
   as `Nat` on the Vera side, so the declared-side materialisation spells
   `Tuple<Int, Nat>` while the SMT side spells `Tuple<Int, Int>`.  That is why
   the all-`Int` spelling crashed too, and why the trigger is `Tuple` NESTED in a
   constructor rather than anything about `Nat`.

   The fix asks, before applying a resolved constructor, whether it can actually
   take the arguments that were built; if not it prefers the instantiation those
   arguments pin, and failing that returns None — an untranslatable ctor, the
   Tier-3 demotion every other `return None` on that path already means.

2. THE ENVELOPE GUARANTEE, which does not depend on part 1 being right.  Any
   exception escaping `cmd_verify` now becomes an `E699` envelope rather than
   empty stdout.  Its cell drives the failure by monkeypatching a translation
   function to raise, so the contract is pinned independently of this particular
   crash — a future translator bug is a diagnostic, not a traceback.

CONTROLS.  Same-ADT nesting (`Some(Some(...))`) did NOT crash before the fix —
measured, not assumed — so it pins that the repair is confined to the disagreeing
sorts rather than to nesting in general; a bare `Tuple` and a ctor over a slot
likewise verified before and must still.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

import vera
import z3
from vera.smt import SmtContext, _ctor_accepts

# Run the SAME compiler this session imported: in a linked worktree a bare
# `python -m vera.cli` would resolve whatever the editable install points at.
_PKG_PARENT = str(Path(vera.__file__).resolve().parents[1])

# The tuple's second component.  A positive literal, which is the detail that
# makes the declared side spell `Nat` where the SMT side spells `Int` — the
# disagreement under test.  Distinctive so a value read off the wrong component
# cannot pass for the right one.
_SECOND = 1234


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


def _verify_json(tmp_path: Path, source: str, name: str = "p.vera") -> dict:
    """`vera verify --json` for *source*.

    Surfaces a crash as itself: the whole point of these cells is that stdout
    is parseable JSON on every exit path, so a `JSONDecodeError` here IS the
    regression and must not be reported as a bare parser error.
    """
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    proc = _cli("verify", "--json", str(p))
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        raise AssertionError(
            f"`verify --json` emitted no parseable envelope (exit "
            f"{proc.returncode})\nstdout: {proc.stdout[:600]!r}\n"
            f"stderr: {proc.stderr[-900:]}"
        ) from None


def _program(param: str, declared: str, value: str) -> str:
    return textwrap.dedent(f"""\
        public fn f({param} -> @Int)
          requires(true) ensures(true) effects(pure)
        {{
          let {declared} = {value};
          0
        }}
        """)


# The issue's own repro.
_REPRO = _program("@Nat", "@Option<Tuple<Nat, Int>>",
                  f"Some(Tuple(@Nat.0, {_SECOND}))")


# ---------------------------------------------------------------------------
# 1. The crash is gone, and the program gets real verdicts
# ---------------------------------------------------------------------------

def test_tuple_nested_in_constructor_does_not_crash(tmp_path: Path) -> None:
    """The issue's repro verifies instead of raising a raw Z3 exception."""
    result = _verify_json(tmp_path, _REPRO)
    assert result["ok"] is True, (
        f"diagnostics: {[d.get('error_code') for d in result['diagnostics']]}"
    )
    assert "E699" not in [d.get("error_code") for d in result["diagnostics"]]


def test_the_repro_obligations_are_discharged(tmp_path: Path) -> None:
    """And the obligations get genuine statuses, not an empty stream.

    A translation that silently returned None everywhere would also stop the
    crash while proving nothing, so the statuses are the assertion: both
    contract obligations discharge at Tier 1 and none is left undischarged.
    """
    result = _verify_json(tmp_path, _REPRO)
    statuses = {o["kind"]: o["status"] for o in result["obligations"]}
    assert statuses == {"requires": "verified", "ensures": "verified"}, statuses
    assert result["verification"]["tier1_verified"] == 2
    assert result["verification"]["tier3_runtime"] == 0


def test_the_crashing_shape_still_compiles_and_runs(tmp_path: Path) -> None:
    """`compile`/`run` were always fine here; the fix must not disturb them."""
    p = tmp_path / "r.vera"
    p.write_text(_REPRO, encoding="utf-8")
    proc = _cli("run", str(p), "--fn", "f", "--", "3")
    assert proc.returncode == 0, f"{proc.stdout}\n{proc.stderr}"
    assert proc.stdout.strip() == "0"


@pytest.mark.parametrize("param,declared,value", [
    # All-`Int` spelling: crashed too, when the literal was typed `Nat` on the
    # declared side (before #1541).  Pins that the trigger is the nesting,
    # not `Nat`.
    ("@Int", "@Option<Tuple<Int, Int>>", f"Some(Tuple(@Int.0, {_SECOND}))"),
    # All-`Nat` spelling, the other end of the same axis.
    ("@Nat", "@Option<Tuple<Nat, Nat>>", "Some(Tuple(@Nat.0, @Nat.0))"),
])
def test_every_tuple_in_constructor_spelling_translates(
    tmp_path: Path, param: str, declared: str, value: str,
) -> None:
    """Each `Tuple`-in-constructor spelling verifies, whatever its components."""
    result = _verify_json(tmp_path, _program(param, declared, value))
    assert result["ok"] is True, (
        f"{declared}: {[d.get('error_code') for d in result['diagnostics']]}"
    )


# ---------------------------------------------------------------------------
# 2. Controls — shapes that were already correct
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("param,declared,value", [
    # Same-ADT nesting.  MEASURED as passing before the fix, so it marks the
    # boundary: the defect was the disagreeing sorts, not nesting as such.
    ("@Int", "@Option<Option<Int>>", "Some(Some(@Int.0))"),
    ("@Nat", "@Option<Option<Nat>>", "Some(Some(@Nat.0))"),
    # A bare tuple, and a constructor over a plain slot.
    ("@Nat", "@Tuple<Nat, Int>", f"Tuple(@Nat.0, {_SECOND})"),
    ("@Nat", "@Option<Nat>", "Some(@Nat.0)"),
])
def test_shapes_that_already_worked_are_unchanged(
    tmp_path: Path, param: str, declared: str, value: str,
) -> None:
    """Each verified cleanly before the fix and must still."""
    result = _verify_json(tmp_path, _program(param, declared, value))
    assert result["ok"] is True, (
        f"{declared}: {[d.get('error_code') for d in result['diagnostics']]}"
    )
    assert result["verification"]["tier1_verified"] == 2


# ---------------------------------------------------------------------------
# 3. The envelope guarantee, independent of the crash above
# ---------------------------------------------------------------------------

def _envelope_for_raising_translator(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture,
    *, as_json: bool,
) -> tuple[int, str, str]:
    """Run `cmd_verify` in-process with the SMT translator forced to raise.

    In-process rather than through the CLI subprocess because the point is to
    drive an ARBITRARY translator failure, not this one bug's: monkeypatching
    is what makes the guarantee independent of `#1360`'s particular exception.
    """
    from vera import smt as smt_mod
    from vera.cli import cmd_verify

    def boom(self, expr, env):
        raise RuntimeError("synthetic translator failure")

    monkeypatch.setattr(smt_mod.SmtContext, "translate_expr", boom)
    p = tmp_path / "e.vera"
    p.write_text(
        _program("@Int", "@Int", "@Int.0"), encoding="utf-8")
    capsys.readouterr()
    rc = cmd_verify(str(p), as_json=as_json)
    captured = capsys.readouterr()
    return rc, captured.out, captured.err


def test_json_envelope_survives_an_internal_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture,
) -> None:
    """`verify --json` emits a parseable E699 envelope, never empty stdout.

    The contract a machine consumer relies on: stdout is always a JSON object,
    so a crash is distinguishable from a clean run.  Empty stdout is the
    regression this pins.
    """
    rc, out, _ = _envelope_for_raising_translator(
        tmp_path, monkeypatch, capsys, as_json=True)
    assert rc == 1
    assert out.strip(), "stdout was EMPTY — no envelope on the failing path"
    payload = json.loads(out)          # must parse
    assert payload["ok"] is False
    assert payload["file"].endswith("e.vera")
    codes = [d.get("error_code") for d in payload["diagnostics"]]
    assert "E699" in codes, payload["diagnostics"]
    diag = next(d for d in payload["diagnostics"] if d.get("error_code") == "E699")
    assert "synthetic translator failure" in diag["description"]
    assert diag["severity"] == "error"
    assert diag["rationale"] and diag["fix"]


def test_text_mode_reports_the_internal_error_without_a_traceback(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture,
) -> None:
    """The human path is a message, not a Python stack trace."""
    rc, _, err = _envelope_for_raising_translator(
        tmp_path, monkeypatch, capsys, as_json=False)
    assert rc == 1
    assert "Internal compiler error" in err
    assert "synthetic translator failure" in err
    assert "Traceback (most recent call last)" not in err


# ---------------------------------------------------------------------------
# 4. The guard predicate answers rather than raises
# ---------------------------------------------------------------------------
#
# `_ctor_accepts` exists to intercept Z3's raise-instead-of-error behaviour, so
# a predicate that can itself raise defeats its own purpose: the traceback the
# envelope above catches would be coming from the very code written to stop it.
# Its sibling `_sorts_agree` already wraps the identical accessors.  `False` —
# "does not accept" — is the conservative answer, and routes to the decline
# path rather than to an application that would raise.

class _HostileCtor:
    """A constructor-like object whose accessors raise, as Z3's can.

    Each accessor `_ctor_accepts` touches gets its own instance, so a cell
    names exactly which unguarded call it is about.
    """

    def __init__(self, raise_on: str, arity: int = 1) -> None:
        self._raise_on = raise_on
        self._arity = arity

    def arity(self) -> int:
        if self._raise_on == "arity":
            raise z3.Z3Exception("hostile arity")
        return self._arity

    def domain(self, i: int) -> object:
        if self._raise_on == "domain":
            raise z3.Z3Exception("hostile domain")
        return _HostileSort(raise_on=None)


class _HostileSort:
    def __init__(self, raise_on: str | None) -> None:
        self._raise_on = raise_on

    def eq(self, other: object) -> bool:
        return False


class _HostileArg:
    """An argument whose `sort()` raises."""

    def sort(self) -> object:
        raise z3.Z3Exception("hostile sort")


@pytest.mark.parametrize("raise_on", ["arity", "domain"])
def test_ctor_accepts_answers_false_when_the_ctor_raises(raise_on: str) -> None:
    """A raising `arity()` / `domain()` is answered, not propagated.

    Red against the unguarded predicate: the `z3.Z3Exception` escapes
    `_ctor_accepts` and unwinds into `_translate_ctor_call`, which is exactly
    the shape this helper was added to prevent.
    """
    ctor = _HostileCtor(raise_on=raise_on)
    assert _ctor_accepts(ctor, [_ok_arg()]) is False


def test_ctor_accepts_answers_false_when_an_arg_sort_raises() -> None:
    """The third accessor: a raising `a.sort()` is answered too."""
    assert _ctor_accepts(_HostileCtor(raise_on=None), [_HostileArg()]) is False


def test_ctor_accepts_still_discriminates_on_real_terms() -> None:
    """The guard must not answer `False` to everything.

    Without this the cells above are satisfied by a predicate that swallowed
    its body entirely — and a guard that always declines would demote every
    constructor translation to Tier 3 while still passing them.
    """
    ctx = SmtContext()
    sort = z3.Datatype("Pair")
    sort.declare("mk", ("fst", z3.IntSort()), ("snd", z3.IntSort()))
    pair = sort.create()
    mk = pair.constructor(0)
    assert _ctor_accepts(mk, [z3.IntVal(1), z3.IntVal(2)]) is True
    assert _ctor_accepts(mk, [z3.IntVal(1)]) is False           # wrong arity
    assert _ctor_accepts(mk, [z3.IntVal(1), z3.BoolVal(True)]) is False
    del ctx


def _ok_arg() -> z3.ExprRef:
    return z3.IntVal(0)


# ---------------------------------------------------------------------------
# 5. The envelope holds on every route into and out of the command
# ---------------------------------------------------------------------------

def _run_cmd(cmd, path: Path, **kw) -> tuple[int, str, str]:
    import io
    import contextlib
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = cmd(str(path), **kw)
    return rc, out.getvalue(), err.getvalue()


def test_a_failing_import_is_enveloped(tmp_path: Path,
                                       monkeypatch: pytest.MonkeyPatch) -> None:
    """A function-scope import that raises still yields an envelope.

    `cmd_verify` imports `vera.verifier` (and with it `z3`) inside the
    function.  Those imports used to sit OUTSIDE the try, so a broken or
    missing wheel produced empty stdout and a raw traceback — precisely the
    failure the envelope claims to have eliminated, reachable on any machine
    whose `z3` install is broken.  Red before the imports moved inside.
    """
    import builtins
    from vera.cli import cmd_verify

    real_import = builtins.__import__

    def hostile(name, *a, **k):
        if name == "vera.verifier":
            raise ImportError("libz3.so: cannot open shared object file")
        return real_import(name, *a, **k)

    monkeypatch.setattr(builtins, "__import__", hostile)
    src = tmp_path / "i.vera"
    src.write_text(_program("@Int", "@Int", "@Int.0"), encoding="utf-8")
    rc, out, _ = _run_cmd(cmd_verify, src, as_json=True)

    assert rc == 1
    assert out.strip(), "stdout was EMPTY — the import bypassed the envelope"
    payload = json.loads(out)
    assert payload["ok"] is False
    assert "E699" in [d.get("error_code") for d in payload["diagnostics"]]
    assert "cannot open shared object file" in payload["diagnostics"][0]["description"]


def test_a_failing_sibling_handler_is_enveloped(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The `VeraError` handler's own raise becomes an envelope too.

    An unenveloped handler that fails mid-report emits the same empty stdout
    as no handler at all, so the sibling handlers are inside the backstop's
    reach.  Driven by a diagnostic whose `to_dict` raises — the helper builds
    its OWN diagnostic, so it is unaffected and can still report.
    """
    from vera.cli import cmd_verify
    from vera.errors import VeraError

    class _BadDiagnostic:
        def to_dict(self):
            raise RuntimeError("diagnostic will not serialise")

        def format(self) -> str:
            raise RuntimeError("diagnostic will not format")

    err = VeraError.__new__(VeraError)
    err.diagnostic = _BadDiagnostic()

    def boom(_path):
        raise err

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    src = tmp_path / "h.vera"
    src.write_text("x", encoding="utf-8")
    rc, out, _ = _run_cmd(cmd_verify, src, as_json=True)

    assert rc == 1
    assert out.strip(), "stdout was EMPTY — the handler's own raise escaped"
    payload = json.loads(out)
    assert "E699" in [d.get("error_code") for d in payload["diagnostics"]]
    assert "will not serialise" in payload["diagnostics"][0]["description"]


@pytest.mark.parametrize("cmd_name,doing", [
    ("cmd_check", "checking"),
    ("cmd_verify", "verifying"),
    ("cmd_test", "testing"),
])
def test_every_json_command_envelopes_an_internal_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    cmd_name: str, doing: str,
) -> None:
    """`check`, `verify` and `test` all keep the `--json` contract.

    `verify` had the only backstop; the other two produced empty stdout on an
    internal error.  They now share one helper — but NOT, as an earlier version
    of this docstring claimed, because they already shared one shape: `check`
    and `test` kept their imports outside the protected region and their
    sibling handlers bare long after `verify` did not, and this cell could not
    see that.  It injects at `_load_and_parse`, which is INSIDE the try for all
    three, so it is structurally incapable of reaching either gap — the same
    can-this-fixture-produce-a-positive trap as the arm-reading probe, twice in
    one commit.  The import and handler routes are covered by their own cells
    below, which inject where the gaps actually were.
    """
    import vera.cli as cli_mod

    def boom(_path):
        raise RuntimeError("synthetic internal failure")

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    src = tmp_path / "e.vera"
    src.write_text(_program("@Int", "@Int", "@Int.0"), encoding="utf-8")
    rc, out, _ = _run_cmd(getattr(cli_mod, cmd_name), src, as_json=True)

    assert rc == 1
    assert out.strip(), f"{cmd_name}: stdout was EMPTY"
    payload = json.loads(out)
    assert payload["ok"] is False
    diag = next(d for d in payload["diagnostics"] if d.get("error_code") == "E699")
    assert doing in diag["description"], (
        f"{cmd_name}: envelope names the wrong phase: {diag['description']!r}"
    )
    assert "synthetic internal failure" in diag["description"]


# Spec 0.5.1's required fields, written out from the SPECIFICATION rather than
# read off the implementation.  A list built from what the envelope happens to
# emit can only ever confirm itself; this one can fail.  `source_line` is not
# here: 0.5.1 asks for the offending source line to be quoted, and an internal
# error has no source position, so the envelope omits it deliberately — the
# claim that it carried one is what this list replaced.
_CONTRACT_FIELDS = ("severity", "error_code", "description", "location",
                    "rationale", "fix", "spec_ref")


def test_the_envelope_carries_the_full_diagnostic_contract(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """It is a real `Diagnostic`, so spec 0.5.1's fields are all present.

    A hand-built dict carried description/location/rationale/fix only, leaving
    `spec_ref` and the location's `file` absent — the envelope would have been
    the one diagnostic in the compiler that the field contract did not reach.
    """
    from vera.cli import cmd_verify

    def boom(_path):
        raise RuntimeError("synthetic")

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    src = tmp_path / "f.vera"
    src.write_text("x", encoding="utf-8")
    _rc, out, _ = _run_cmd(cmd_verify, src, as_json=True)
    diag = json.loads(out)["diagnostics"][0]

    missing = [f for f in _CONTRACT_FIELDS if not diag.get(f)]
    assert not missing, f"envelope omits contract fields: {missing}"
    assert diag["severity"] == "error"
    assert diag["error_code"] == "E699"
    assert diag["location"]["file"] == str(src), (
        "the location names no file — a consumer cannot join it to anything"
    )
    assert "source_line" not in diag, (
        "an internal error has no source position; a quoted line here would be "
        "invented"
    )


def test_the_text_path_formats_like_any_other_diagnostic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """And without `--json` the user gets a formatted diagnostic, not a trace."""
    from vera.cli import cmd_verify

    def boom(_path):
        raise RuntimeError("synthetic")

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    src = tmp_path / "g.vera"
    src.write_text("x", encoding="utf-8")
    rc, _out, err = _run_cmd(cmd_verify, src, as_json=False)
    assert rc == 1
    assert "E699" in err
    assert "Traceback (most recent call last)" not in err


@pytest.mark.parametrize("cmd_name,mod", [
    ("cmd_check", "vera.checker"),
    ("cmd_verify", "vera.verifier"),
    ("cmd_test", "vera.tester"),
])
def test_every_command_envelopes_a_failing_import(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    cmd_name: str, mod: str,
) -> None:
    """Each command's own function-scope imports are inside its guarded region.

    `verify`'s moved first; `check` and `test` still imported before their
    `try`, so a broken wheel bypassed the very envelopes they had just been
    given.  Red for `check` and `test` before this change.
    """
    import builtins

    import vera.cli as cli_mod

    real_import = builtins.__import__

    def hostile(name, *a, **k):
        if name == mod:
            raise ImportError(f"{mod}: simulated broken wheel")
        return real_import(name, *a, **k)

    monkeypatch.setattr(builtins, "__import__", hostile)
    src = tmp_path / "imp.vera"
    src.write_text(_program("@Int", "@Int", "@Int.0"), encoding="utf-8")
    rc, out, _ = _run_cmd(getattr(cli_mod, cmd_name), src, as_json=True)

    assert rc == 1
    assert out.strip(), f"{cmd_name}: stdout was EMPTY — the import bypassed it"
    payload = json.loads(out)
    assert "E699" in [d.get("error_code") for d in payload["diagnostics"]]
    assert "simulated broken wheel" in payload["diagnostics"][0]["description"]


def test_the_last_resort_fallback_engages(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """When the REPORTING path itself raises, a minimal envelope still lands.

    The envelope is worth nothing if the code emitting it can raise, so the
    helper's own `Diagnostic` route has a hand-built fallback underneath.
    Driven by breaking `Diagnostic.to_dict` for every diagnostic — including
    the one the helper builds — which is the only way to reach it.
    """
    from vera.cli import cmd_verify
    from vera.errors import Diagnostic

    def boom(_path):
        raise RuntimeError("primary failure")

    def bad_to_dict(self):
        raise RuntimeError("serialisation is broken too")

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    monkeypatch.setattr(Diagnostic, "to_dict", bad_to_dict)
    src = tmp_path / "lr.vera"
    src.write_text("x", encoding="utf-8")
    rc, out, _ = _run_cmd(cmd_verify, src, as_json=True)

    assert rc == 1
    assert out.strip(), "stdout was EMPTY — the fallback did not engage"
    payload = json.loads(out)          # must still parse
    assert payload["ok"] is False
    assert payload["diagnostics"][0]["error_code"] == "E699"


def test_the_last_resort_fallback_engages_on_the_text_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Its text sibling: a broken `.format()` still yields a message."""
    from vera.cli import cmd_verify
    from vera.errors import Diagnostic

    def boom(_path):
        raise RuntimeError("primary failure")

    def bad_format(self):
        raise RuntimeError("formatting is broken too")

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    monkeypatch.setattr(Diagnostic, "format", bad_format)
    src = tmp_path / "lt.vera"
    src.write_text("x", encoding="utf-8")
    rc, _out, err = _run_cmd(cmd_verify, src, as_json=False)

    assert rc == 1
    assert "E699" in err
    assert "Traceback (most recent call last)" not in err


@pytest.mark.parametrize("cmd_name,doing", [
    ("cmd_check", "checking"),
    ("cmd_verify", "verifying"),
    ("cmd_test", "testing"),
])
def test_every_command_envelopes_a_failing_sibling_handler(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    cmd_name: str, doing: str,
) -> None:
    """Each command's own `VeraError` handler is inside the backstop's reach.

    Injects INSIDE the handler rather than inside the try, which is the only
    place that can see this gap: `check` and `test` kept bare handler bodies
    after `verify`'s were wrapped, and a cell driving `_load_and_parse` sees
    none of it because that is inside the protected region for all three.
    """
    import vera.cli as cli_mod
    from vera.errors import VeraError

    class _BadDiagnostic:
        def to_dict(self):
            raise RuntimeError("diagnostic will not serialise")

        def format(self) -> str:
            raise RuntimeError("diagnostic will not format")

    err = VeraError.__new__(VeraError)
    err.diagnostic = _BadDiagnostic()

    def boom(_path):
        raise err

    monkeypatch.setattr("vera.cli._load_and_parse", boom)
    src = tmp_path / "sib.vera"
    src.write_text("x", encoding="utf-8")
    rc, out, _ = _run_cmd(getattr(cli_mod, cmd_name), src, as_json=True)

    assert rc == 1
    assert out.strip(), f"{cmd_name}: stdout was EMPTY — the handler's raise escaped"
    payload = json.loads(out)
    diag = next(d for d in payload["diagnostics"] if d.get("error_code") == "E699")
    assert doing in diag["description"]
    assert "will not serialise" in diag["description"]
