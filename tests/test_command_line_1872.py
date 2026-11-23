"""The command line takes what each command lists, and refuses the rest (#1872).

`vera.cli.main` used to strip one shared set of flags from every command
line, read each flag by membership anywhere in the arguments, and take the
first token left as the file.  So a flag a command does not take was
ignored, an unknown one standing first was read as the file, a flag after
`--` was read as the command's own, `--help` was a missing file, and every
file after the first was dropped: `vera check good.vera bad.vera` exited 0
without reading `bad.vera`.

The class is every command line: each command by each flag any command
takes (and `--help`, `-h`, an unknown one), by where the flag stands (before
the file, after it, after `--`), by how many files it names, and a valued
flag with no value or given twice.  `TestMatrix` runs every cell through
`vera.cli.main` with each `cmd_*` replaced by a recorder, so a cell reads
what the command line hands the command, or the refusal it prints, against
an oracle written here from the documents (`TAKES`), not from the table the
fix reads.  The recorders cannot see the real dispatch, so the `repro`
tests beside it run the issue's own lines, the benchmark harness's lines and
one cell of each refusal kind through the real entry point with real files.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/cli.py", "vera/command_line.py", "vera/command_errors.py",
    "vera/smt.py",
])

# =====================================================================
# The oracle: what the documents say each command takes
# =====================================================================

COMMANDS = ("parse", "check", "typecheck", "verify", "test", "compile",
            "serve", "run", "ast", "fmt", "lsp", "builtins", "effects",
            "errors", "version")
FILELESS = frozenset({"lsp", "builtins", "effects", "errors", "version"})
FLAGS = ("--json", "--quiet", "--wat", "--write", "--check",
         "--explain-slots", "--distrust", "--reconcile", "--no-reconcile",
         "--stdio", "--help", "-h", "--bogus")
VALUED = ("--fn", "-o", "--trials", "--target", "--port", "--host",
          "--world", "--timeout-ms")

#: The options each command takes: USAGE, CLAUDE.md § Key commands and
#: TOOLCHAIN.md.  `--help` and `-h` belong to every command.
TAKES: dict[str, frozenset[str]] = {
    "parse": frozenset(),
    "check": frozenset({"--json", "--quiet", "--explain-slots"}),
    "verify": frozenset({"--json", "--quiet", "--timeout-ms", "--reconcile",
                         "--no-reconcile"}),
    "test": frozenset({"--json", "--trials", "--fn", "--distrust"}),
    "compile": frozenset({"--json", "--wat", "-o", "--target", "--world"}),
    "run": frozenset({"--json", "--fn", "--target", "--world"}),
    "serve": frozenset({"--port", "--host"}),
    "ast": frozenset({"--json"}),
    "fmt": frozenset({"--write", "--check"}),
    # Editors pass `--stdio` by habit; stdio is the server's one transport
    # (LSP_SERVER.md), so the option states what happens.
    "lsp": frozenset({"--stdio"}),
    "builtins": frozenset({"--json"}),
    "effects": frozenset({"--json"}),
    "errors": frozenset({"--json"}),
    "version": frozenset(),
}
TAKES["typecheck"] = TAKES["check"]

#: The handler each command dispatches to.
HANDLER = {c: ("check" if c == "typecheck" else c) for c in COMMANDS}


def _value(command: str, flag: str) -> str:
    """A value the flag takes on *command*, none of them a default."""
    return {"--fn": "f", "-o": "out.wasm", "--trials": "5",
            "--target": "wasi-p2" if command == "run" else "browser",
            "--port": "8080", "--host": "0.0.0.0", "--world": "server",
            "--timeout-ms": "5000"}[flag]


#: What a taken option hands its command: the keyword and its value.
def _honoured(flag: str, value: str | None) -> tuple[str, Any]:
    return {
        "--json": ("as_json", True), "--quiet": ("quiet", True),
        "--wat": ("wat", True), "--write": ("write", True),
        "--check": ("check", True), "--explain-slots": ("explain_slots", True),
        "--distrust": ("distrust", True), "--no-reconcile": ("reconcile", False),
        "--fn": ("fn_name", value), "-o": ("output", value),
        "--trials": ("trials", 5), "--target": ("target", value),
        "--port": ("port", 8080), "--host": ("host", value),
        "--world": ("world", value), "--timeout-ms": ("timeout_ms", 5000),
    }[flag]


def _cells() -> list[Any]:
    """Every cell: (command, argv after the command, expected outcome).

    An outcome is ``("honoured", kw, value)``, ``("moved", {kw: value})``,
    ``("default",)``, ``("help",)``, ``("program", [args])`` or
    ``("refused", code)``, with the text the refusal must hold after it."""
    cells: list[Any] = []

    def add(cmd: str, argv: list[str], outcome: tuple[Any, ...]) -> None:
        cells.append(pytest.param(cmd, argv, outcome,
                                  id=f"{cmd} {' '.join(argv)}".strip()))

    for cmd in COMMANDS:
        takes = TAKES[cmd]
        for flag in FLAGS + VALUED:
            toks = [flag] + ([_value(cmd, flag)] if flag in VALUED else [])
            if flag in ("--help", "-h"):
                taken: tuple[Any, ...] = ("help",)
            elif flag not in takes:
                taken = ("refused", "E901")
            elif flag in ("--reconcile", "--stdio"):
                taken = ("default",)
            else:
                taken = ("honoured", *_honoured(flag, toks[-1]))
            files_refused = ("refused", "E904")
            # A refusal of an option comes before a refusal of the files.
            when_files_wrong = (taken if taken[0] in ("help", "refused")
                                else files_refused)
            if cmd in FILELESS:
                add(cmd, toks, taken)
                add(cmd, ["a.vera", *toks], when_files_wrong)
                add(cmd, ["--", *toks], ("refused", "E901"))
                continue
            add(cmd, toks, when_files_wrong)
            add(cmd, [*toks, "a.vera"], taken)
            add(cmd, ["a.vera", *toks], taken)
            add(cmd, [*toks, "a.vera", "b.vera"], when_files_wrong)
            add(cmd, ["a.vera", "--", *toks],
                ("program", toks) if cmd == "run" else ("refused", "E901"))
        for flag in VALUED:
            if flag not in takes:
                continue
            value = _value(cmd, flag)
            add(cmd, ["a.vera", flag], ("refused", "E903"))
            add(cmd, [flag, value, flag, value, "a.vera"], ("refused", "E902"))
        if cmd not in FILELESS:
            add(cmd, [], ("refused", "E904"))
            add(cmd, ["a.vera", "b.vera"], ("refused", "E904"))
    # After `--` on `run`, every token is the program's, whatever it looks like.
    for args in (["-1"], ["-1", "-5"], ["--5"], ["-"], ["--"], ["--help"],
                 ["--json", "-o"]):
        add("run", ["a.vera", "--fn", "f", "--", *args], ("program", args))
    # A value `vera run` does not take, though `vera compile` does.
    add("run", ["--target", "browser", "a.vera"], ("refused", "E903"))

    # Each valued option's domain: zero, negative, non-numeric, empty and far
    # too large, on each command that takes it.  A count of trials has no
    # ceiling (a large one is slow, not wrong); a port is 0 to 65535 (0 lets
    # the system pick); a budget is 1 to 2**32 - 1 ms, Z3's unsigned limit,
    # above which it would wrap; a function's name is an identifier.
    huge = "1" + "0" * 30
    ok_any = {"0": True, "-5": True, "abc": True, "": False, huge: True}
    domains = {
        "--trials": ({"0": False, "-5": False, "abc": False, "": False, huge: True},
                     int),
        "--port": ({"0": True, "-5": False, "abc": False, "": False, huge: False},
                   int),
        "--timeout-ms": ({v: False for v in ok_any}, int),
        "--fn": ({"0": False, "-5": False, "abc": True, "": False, huge: False}, str),
        "-o": (ok_any, str), "--host": (ok_any, str),
        "--target": ({v: False for v in ok_any}, str),
        "--world": ({v: False for v in ok_any}, str),
    }
    for cmd in COMMANDS:
        for flag, (accepts, kind) in domains.items():
            if flag not in TAKES[cmd] or cmd == "typecheck":
                continue
            for value, accepted in accepts.items():
                kw = _honoured(flag, value)[0]
                add(cmd, [flag, value, "a.vera"],
                    ("honoured", kw, kind(value)) if accepted else ("refused", "E903"))
            # The next token is an option, not a value: a missing value.
            add(cmd, ["a.vera", flag, "--json"], ("refused", "E903"))
            # The equals form, refused with a fix that writes it with a space.
            value = _value(cmd, flag)
            add(cmd, ["a.vera", f"{flag}={value}"],
                ("refused", "E901", f"{flag} {value}"))
    # A flag written with `=` takes no value.
    add("check", ["a.vera", "--json=1"], ("refused", "E901", "takes no value"))
    # An option another command takes, written with `=`, names its owners.
    add("check", ["a.vera", "--trials=5"], ("refused", "E901", "`vera test`"))

    # A repeat is E902 whatever its values, a bad one in either place included.
    for cmd in COMMANDS:
        for flag, (accepts, _kind) in domains.items():
            if flag not in TAKES[cmd] or cmd == "typecheck":
                continue
            good = _value(cmd, flag)
            bad = next(v for v, ok in accepts.items() if not ok)
            add(cmd, [flag, good, flag, bad, "a.vera"], ("refused", "E902"))
            add(cmd, [flag, bad, flag, good, "a.vera"], ("refused", "E902"))

    # The pairs a command refuses together, and their nearest neighbours.
    add("fmt", ["--check", "--write", "a.vera"], ("refused", "E902"))
    add("fmt", ["--write", "--check", "a.vera"], ("refused", "E902"))
    add("verify", ["--reconcile", "--no-reconcile", "a.vera"], ("refused", "E902"))
    add("verify", ["--no-reconcile", "--reconcile", "a.vera"], ("refused", "E902"))
    add("compile", ["--wat", "-o", "x.wasm", "a.vera"], ("refused", "E902"))
    add("compile", ["-o", "x.wasm", "--wat", "a.vera"], ("refused", "E902"))
    add("compile", ["--wat", "--target", "browser", "a.vera"], ("refused", "E902"))
    add("compile", ["--wat", "--target", "wasi-p2", "a.vera"],
        ("moved", {"wat": True, "target": "wasi-p2"}))
    add("compile", ["-o", "x", "--target", "browser", "a.vera"],
        ("moved", {"output": "x", "target": "browser"}))
    add("verify", ["--json", "--quiet", "a.vera"],
        ("moved", {"as_json": True, "quiet": True}))
    return cells


# =====================================================================
# The recorders
# =====================================================================


class _Recorder:
    def __init__(self, monkeypatch: pytest.MonkeyPatch) -> None:
        import vera.cli as cli

        self.calls: list[tuple[str, tuple[Any, ...], dict[str, Any]]] = []
        for name in ("parse", "check", "verify", "test", "compile", "serve",
                     "run", "ast", "fmt", "lsp", "builtins", "effects",
                     "errors", "version"):
            monkeypatch.setattr(cli, f"cmd_{name}", self._record(name))

    def _record(self, name: str) -> Any:
        def record(*args: Any, **kwargs: Any) -> int:
            self.calls.append((name, args, kwargs))
            return 0
        return record

    def invoke(self, *argv: str) -> tuple[pipeline.CliResult, list[Any]]:
        self.calls.clear()
        run = pipeline.cli(*argv)
        return run, list(self.calls)


def _code(run: pipeline.CliResult, as_json: bool) -> str:
    """The E9xx code a refusal printed, on the stream the rule names: the
    envelope on stdout under `--json`, the diagnostic on stderr otherwise."""
    if as_json:
        assert run.stderr == "", run.stderr
        envelope = json.loads(run.stdout)
        assert envelope["ok"] is False and envelope["file"] == "", envelope
        (diag,) = envelope["diagnostics"]
        return str(diag["error_code"])
    assert run.stdout == "", run.stdout
    match = re.match(r"\[(E9\d\d)\] ", run.stderr)
    assert match, run.stderr
    return match.group(1)


class TestMatrix:
    """Every cell of the class, against the documents' oracle."""

    @pytest.mark.parametrize(("cmd", "argv", "outcome"), _cells())
    def test_cell(self, cmd: str, argv: list[str], outcome: tuple[Any, ...],
                  monkeypatch: pytest.MonkeyPatch) -> None:
        rec = _Recorder(monkeypatch)
        base_argv = [cmd] if cmd in FILELESS else [cmd, "a.vera"]
        _, base = rec.invoke(*base_argv)
        assert len(base) == 1, base
        run, calls = rec.invoke(cmd, *argv)
        own = argv[:argv.index("--")] if "--" in argv else argv
        kind = outcome[0]
        if kind == "refused":
            assert calls == [], calls
            assert run.returncode == 1, run
            assert _code(run, "--json" in own) == outcome[1]
            if len(outcome) > 2:
                assert outcome[2] in run.stdout + run.stderr, run
            return
        if kind == "help":
            assert calls == [], calls
            assert run.returncode == 0, run
            assert run.stderr == ""
            assert run.stdout.startswith(f"Usage: vera {cmd}"), run.stdout
            return
        assert run.returncode == 0, run
        assert len(calls) == 1, calls
        name, args, kwargs = calls[0]
        _, base_args, base_kwargs = base[0]
        assert name == HANDLER[cmd]
        assert args == base_args, (args, base_args)
        moved = {k: v for k, v in kwargs.items() if base_kwargs.get(k) != v}
        if kind == "default":
            assert moved == {}
        elif kind == "honoured":
            assert moved == {outcome[1]: outcome[2]}
        elif kind == "moved":
            assert moved == outcome[1]
        else:
            assert moved == {"raw_fn_args": outcome[1]} or (
                "--fn" in own and moved == {"raw_fn_args": outcome[1],
                                            "fn_name": "f"}), moved


# =====================================================================
# The real entry point, with real files
# =====================================================================

GOOD = ("public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  1\n}\n")
BAD = ("public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
       "  effects(pure)\n{\n  true\n}\n")
UGLY = ("public fn main(@Unit -> @Int)\n  requires(true) ensures(true) "
        "effects(pure)\n{\n  1\n}\n")
MIN_OF_TWO = (
    "public fn min_of_two(@Int, @Int -> @Int)\n  requires(true)\n"
    "  ensures(@Int.result <= @Int.0 && @Int.result <= @Int.1)\n"
    "  effects(pure)\n{\n  if @Int.1 <= @Int.0 then { @Int.1 } else { @Int.0 }\n}\n"
    "\n"
    "public fn minus(@Int, @Int -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{\n  @Int.1 - @Int.0\n}\n"
    "\n"
    "public fn width(@String -> @Int)\n  requires(true)\n"
    "  ensures(@Int.result >= 0)\n  effects(pure)\n{\n  string_length(@String.0)\n}\n"
)


def _files(tmp_path: Path) -> dict[str, str]:
    paths = {}
    for name, text in (("good", GOOD), ("bad", BAD), ("ugly", UGLY),
                       ("min", MIN_OF_TWO)):
        p = tmp_path / f"{name}.vera"
        p.write_text(text, encoding="utf-8")
        paths[name] = p.as_posix()
    return paths


@pytest.mark.parametrize("command", [("check",), ("verify",), ("fmt", "--check")],
                         ids=["check", "verify", "fmt-check"])
@pytest.mark.parametrize("order", ["good-bad", "bad-good"])
def test_repro_a_second_file_is_refused_not_dropped(
        tmp_path: Path, command: tuple[str, ...], order: str) -> None:
    """The issue's soundness member: a gate named two files read one and
    exited 0 when the first was good.  Now either order is E904, before
    either file is read, and the Fix says to run the command once a file."""
    f = _files(tmp_path)
    second = f["ugly"] if command[0] == "fmt" else f["bad"]
    files = [f["good"], second] if order == "good-bad" else [second, f["good"]]
    run = pipeline.cli(*command, *files)
    assert run.returncode == 1, run
    assert run.stdout == ""
    assert run.stderr.startswith("[E904] "), run.stderr
    assert "once for each file" in run.stderr


@pytest.mark.parametrize("command", COMMANDS)
@pytest.mark.parametrize("flag", ["--help", "-h"])
def test_repro_help_prints_the_command_s_usage(command: str, flag: str) -> None:
    """`vera <command> --help` was `E900 file not found: --help`: now the
    command's usage, on stdout, exit 0, naming each option it takes."""
    run = pipeline.cli(command, flag)
    assert run.returncode == 0, run
    assert run.stderr == ""
    assert run.stdout.startswith(f"Usage: vera {command}")
    for option in TAKES[command]:
        assert option in run.stdout, (command, option)


@pytest.mark.parametrize("flag", ["--help", "-h"])
def test_repro_top_level_help(flag: str) -> None:
    """`vera --help` was E904 `Unknown command: --help`: now the usage on
    stdout, exit 0, listing every command."""
    from vera.cli import USAGE

    run = pipeline.cli(flag)
    assert (run.returncode, run.stdout, run.stderr) == (0, USAGE + "\n", "")
    for command in COMMANDS:
        assert re.search(rf"^\s+{command}\b", USAGE, re.M), command


def test_repro_no_arguments_prints_the_usage_and_fails() -> None:
    """`vera` alone prints the usage on stderr and exits 1, as before."""
    from vera.cli import USAGE

    run = pipeline.cli()
    assert (run.returncode, run.stdout, run.stderr) == (1, "", USAGE + "\n")


@pytest.mark.parametrize(("argv", "code"), [
    (("parse", "--json", "{good}"), "E901"),
    (("fmt", "--json", "{good}"), "E901"),
    (("check", "--write", "{good}"), "E901"),
    (("check", "--wat", "{good}"), "E901"),
    (("check", "--trials", "5", "{good}"), "E901"),
    (("verify", "--fn", "nosuch", "{good}"), "E901"),
    (("parse", "--quiet", "{good}"), "E901"),
    (("check", "{good}", "--bogus"), "E901"),
    (("check", "--bogus", "{good}"), "E901"),
    (("check", "{good}", "--", "--json"), "E901"),
    (("compile", "{good}", "-o"), "E903"),
    (("run", "--target", "browser", "{good}"), "E903"),
    (("check", "--json", "--json", "{good}"), "E902"),
    (("run", "--fn", "main", "--fn", "main", "{good}"), "E902"),
    (("version", "extra"), "E904"),
    (("builtins", "{good}"), "E904"),
    (("lsp", "--json"), "E901"),
    (("serve", "--port", "70000", "{good}"), "E903"),
    (("run", "--fn", "0", "{good}"), "E903"),
    (("test", "--fn", "", "{good}"), "E903"),
], ids=lambda v: " ".join(v) if isinstance(v, tuple) else v)
def test_repro_each_refusal_kind_through_the_entry_point(
        tmp_path: Path, argv: tuple[str, ...], code: str) -> None:
    """Each line exited 0 at base, the flag or the operand ignored (or, for
    `check --bogus f`, failed as a missing file `--bogus`).  Now each is
    refused with its code, and under `--json` as the envelope on stdout."""
    f = _files(tmp_path)
    args = [a.format(**f) for a in argv]
    run = pipeline.cli(*args)
    assert run.returncode == 1, run
    own = args[:args.index("--")] if "--" in args else args
    assert _code(run, "--json" in own) == code, run


def test_repro_a_refusal_under_json_is_the_envelope(tmp_path: Path) -> None:
    """A command-line refusal on a command line that asks for `--json` is
    the documented envelope, on stdout, with the E9xx diagnostic, exactly as
    `vera.command_errors` builds it; the text form goes to stderr."""
    from vera import command_errors as ce

    f = _files(tmp_path)
    run = pipeline.cli("check", "--json", f["good"], f["bad"])
    assert run.returncode == 1 and run.stderr == ""
    envelope = json.loads(run.stdout)
    assert set(envelope) == {"ok", "file", "diagnostics"}
    assert envelope["ok"] is False and envelope["file"] == ""
    (diag,) = envelope["diagnostics"]
    assert diag["error_code"] == "E904"
    assert diag["fix"] == ce.second_file_refused("check", 2).fix
    run = pipeline.cli("check", f["good"], f["bad"])
    assert run.stdout == ""
    assert run.stderr.startswith(ce.second_file_refused("check", 2).format())


# =====================================================================
# The benchmark harness's lines: each behaves exactly as it did
# =====================================================================


def test_repro_benchmark_harness_version() -> None:
    import vera

    run = pipeline.cli("version")
    assert (run.returncode, run.stdout, run.stderr) == (
        0, f"vera {vera.__version__}\n", "")


def test_repro_benchmark_harness_check_json(tmp_path: Path) -> None:
    f = _files(tmp_path)
    run = pipeline.cli("check", "--json", f["good"])
    assert run.returncode == 0, run
    assert json.loads(run.stdout)["ok"] is True
    run = pipeline.cli("check", "--json", f["bad"])
    assert run.returncode == 1
    envelope = json.loads(run.stdout)
    assert envelope["ok"] is False and envelope["file"] == f["bad"]
    assert envelope["diagnostics"][0]["error_code"] == "E121"


def test_repro_benchmark_harness_verify_json(tmp_path: Path) -> None:
    f = _files(tmp_path)
    run = pipeline.cli("verify", "--json", f["min"])
    assert run.returncode == 0, run
    envelope = json.loads(run.stdout)
    assert envelope["ok"] is True and envelope["file"] == f["min"]
    assert envelope["verification"]["total"] >= 2


@pytest.mark.parametrize(("args", "stdout"), [
    (["-1", "-5"], "-5\n"),
    (["-5", "-1"], "-5\n"),
    (["3", "-1"], "-1\n"),
    (["7", "2"], "2\n"),
])
def test_repro_benchmark_harness_run_negative_arguments(
        tmp_path: Path, args: list[str], stdout: str) -> None:
    """`vera run FILE --fn NAME -- ARG...` with negative integers: a
    dash-led token after `--` is the program's argument, never an option."""
    f = _files(tmp_path)
    run = pipeline.cli("run", f["min"], "--fn", "min_of_two", "--", *args)
    assert (run.returncode, run.stdout, run.stderr) == (0, stdout, ""), run


def test_repro_benchmark_harness_run_dash_led_arguments(tmp_path: Path) -> None:
    """After `--`, `-1`, `-5`, `--5` and a bare `-` are the program's
    arguments: `width` takes a `@String` and returns its length.  None is
    read as an option of `vera run`.  Green at base, and pinned so."""
    f = _files(tmp_path)
    for arg in ("-1", "-5", "--5", "-", "--"):
        run = pipeline.cli("run", f["min"], "--fn", "width", "--", arg)
        assert (run.returncode, run.stdout, run.stderr) == (
            0, f"{len(arg)}\n", ""), (arg, run)


def test_repro_an_option_after_the_separator_is_the_program_s(
        tmp_path: Path) -> None:
    """`--json` and `--help` after `--` are the program's arguments too.
    At base `--json` there was read as `vera run`'s own as well, and the
    run printed the envelope."""
    f = _files(tmp_path)
    for arg in ("--json", "--help", "--fn"):
        run = pipeline.cli("run", f["min"], "--fn", "width", "--", arg)
        assert (run.returncode, run.stdout, run.stderr) == (
            0, f"{len(arg)}\n", ""), (arg, run)


def test_repro_benchmark_harness_run_fn_without_arguments(tmp_path: Path) -> None:
    """`vera run FILE --fn NAME` with no `--` at all."""
    p = tmp_path / "unit.vera"
    p.write_text("public fn seven(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
                 "  effects(pure)\n{\n  7\n}\n", encoding="utf-8")
    run = pipeline.cli("run", p.as_posix(), "--fn", "seven")
    assert (run.returncode, run.stdout, run.stderr) == (0, "7\n", ""), run


# =====================================================================
# Values, operands and pairs, through the real entry point
# =====================================================================


@pytest.mark.parametrize("value", ["0", "-5"])
def test_repro_a_test_gate_with_no_trials_is_refused(tmp_path: Path, value: str) -> None:
    """`vera test FILE --trials 0` (or `-5`) printed "Testing:", ran no
    trial and exited 0: a gate that passes having tested nothing.  A count
    of trials is a positive integer, and anything else is E903."""
    f = _files(tmp_path)
    run = pipeline.cli("test", f["min"], "--trials", value)
    assert run.returncode == 1 and run.stdout == "", run
    assert run.stderr.startswith("[E903] "), run.stderr
    assert (f"Invalid --trials value: {value} (expected a positive integer)"
            in run.stderr), run.stderr


@pytest.mark.parametrize(("env", "argv"), [
    ({}, ("--timeout-ms", str(2**32))),
    ({"VERA_Z3_TIMEOUT_MS": str(2**32)}, ()),
])
def test_repro_a_budget_past_the_solver_s_limit_is_refused(
        tmp_path: Path, env: dict[str, str], argv: tuple[str, ...]) -> None:
    """Z3 takes its budget as a C unsigned int, so 2**32 ms wrapped to 0
    and a budget of 2**32 + 1 ms to 1 ms, silently.  The flag and the
    variable share one validator, which refuses past 2**32 - 1 (E903)."""
    f = _files(tmp_path)
    run = pipeline.cli("verify", *argv, f["good"], env=env)
    assert run.returncode == 1, run
    assert "[E903]" in run.stderr and "the solver's limit" in run.stderr, run.stderr


@pytest.mark.parametrize("env_value", [str(2**32), "abc", "0"])
def test_repro_the_explicit_budget_wins_over_the_environment_s(
        tmp_path: Path, env_value: str) -> None:
    """`--timeout-ms` comes first in the budget's precedence, so the
    environment's value is validated only where it is the one used: with
    the flag, a malformed or out-of-range `VERA_Z3_TIMEOUT_MS` is not read
    (it was E903, the flag never reached); without it, it is E903."""
    f = _files(tmp_path)
    env = {"VERA_Z3_TIMEOUT_MS": env_value}
    run = pipeline.cli("verify", "--json", "--timeout-ms", "1000", f["good"], env=env)
    assert run.returncode == 0, run
    assert json.loads(run.stdout)["verification"]["timeout_ms"] == 1000
    run = pipeline.cli("verify", "--json", f["good"], env=env)
    assert run.returncode == 1, run
    (diag,) = json.loads(run.stdout)["diagnostics"]
    assert diag["error_code"] == "E903"
    assert diag["description"].startswith("VERA_Z3_TIMEOUT_MS: "), diag
    # `vera test` takes no flag: the environment's value is always the one used.
    run = pipeline.cli("test", f["good"], env=env)
    assert run.returncode == 1 and run.stderr.startswith("[E903] "), run


@pytest.mark.parametrize("values", [("5", "0"), ("0", "5"), ("0", "0"), ("abc", "5")])
def test_repro_a_repeated_option_is_e902_whatever_its_values(
        tmp_path: Path, values: tuple[str, str]) -> None:
    """An option given twice is E902 whatever the two values are, a bad
    one included; a single bad value stays E903."""
    f = _files(tmp_path)
    first, second = values
    run = pipeline.cli("test", "--trials", first, "--trials", second, f["good"])
    assert run.returncode == 1 and run.stderr.startswith("[E902] "), run
    assert "--trials is given twice" in run.stderr
    run = pipeline.cli("test", "--trials", "0", f["good"])
    assert run.stderr.startswith("[E903] "), run


@pytest.mark.parametrize(("args", "stdout"), [
    (["7", "2"], "5\n"), (["2", "7"], "-5\n"),
    (["-1", "-5"], "4\n"), (["-5", "-1"], "-4\n"),
])
def test_repro_run_passes_the_program_s_arguments_in_order(
        tmp_path: Path, args: list[str], stdout: str) -> None:
    """`minus` returns its first parameter less its second (`@Int.1 -
    @Int.0`: `@Int.0` is the last), so a reordering of the arguments after
    `--` changes the result, which `min_of_two` could not show."""
    f = _files(tmp_path)
    run = pipeline.cli("run", f["min"], "--fn", "minus", "--", *args)
    assert (run.returncode, run.stdout, run.stderr) == (0, stdout, ""), run
    run = pipeline.cli("run", "--fn", "minus", f["min"], "--", *args)
    assert (run.returncode, run.stdout) == (0, stdout), run


@pytest.mark.parametrize("operand", ["sub", ""], ids=["directory", "empty"])
@pytest.mark.parametrize("command", ["check", "verify", "fmt", "run"])
def test_repro_an_operand_that_is_no_file_is_e900_not_e699(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch, operand: str,
        command: str) -> None:
    """`vera check sub` (a directory) and `vera check ''` were E699, the
    internal-error code, for a user's mistake.  Each is E900, with its fix."""
    (tmp_path / "sub").mkdir()
    monkeypatch.chdir(tmp_path)
    run = pipeline.cli(command, operand)
    assert run.returncode == 1, run
    assert run.stderr.startswith("[E900] "), run.stderr
    assert "E699" not in run.stderr
    assert ("is a directory" if operand else "an empty argument") in run.stderr
    run = pipeline.cli(command, "--json", operand) if command != "fmt" else None
    if run is not None:
        envelope = json.loads(run.stdout)
        assert envelope["diagnostics"][0]["error_code"] == "E900", envelope


def test_repro_a_file_whose_name_begins_with_a_dash(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """`vera check -dash.vera` read the file at base; now a dash-led token
    is an option, so the refusal says how to name the file: `./-dash.vera`,
    which checks.  After `--` the same holds."""
    (tmp_path / "-dash.vera").write_text(GOOD, encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    for argv in (("check", "-dash.vera"), ("check", "--", "-dash.vera")):
        run = pipeline.cli(*argv)
        assert run.returncode == 1 and run.stderr.startswith("[E901] "), run
        assert "vera check ./-dash.vera" in run.stderr, run.stderr
    run = pipeline.cli("check", "./-dash.vera")
    assert (run.returncode, run.stdout) == (0, "OK: ./-dash.vera\n"), run


@pytest.mark.parametrize(("argv", "fix"), [
    (("run", "{min}", "--fn=min_of_two", "--", "1", "2"),
     "vera run --fn min_of_two program.vera"),
    (("test", "{min}", "--trials=5"), "vera test --trials 5 program.vera"),
    (("verify", "--timeout-ms=5000", "{good}"), "vera verify --timeout-ms 5000 program.vera"),
    (("compile", "{good}", "--target=browser"), "vera compile --target browser program.vera"),
])
def test_repro_the_equals_form_says_how_to_write_it(
        tmp_path: Path, argv: tuple[str, ...], fix: str) -> None:
    """`--fn=add` and its kind are refused (E901), at base two were ignored;
    the fix writes the option and its value as two arguments."""
    f = _files(tmp_path)
    run = pipeline.cli(*[a.format(**f) for a in argv])
    assert run.returncode == 1 and run.stderr.startswith("[E901] "), run
    assert fix in run.stderr, run.stderr


def test_repro_an_option_where_a_value_is_due_is_a_missing_value(
        tmp_path: Path) -> None:
    """`vera run FILE --fn --json` was E906, "function not found" for a
    function called `--json`.  The value is missing: E903, and the `--json`
    the command line holds makes the refusal the envelope."""
    f = _files(tmp_path)
    run = pipeline.cli("run", f["min"], "--fn", "--json")
    assert run.returncode == 1 and run.stderr == "", run
    (diag,) = json.loads(run.stdout)["diagnostics"]
    assert (diag["error_code"], diag["description"]) == ("E903", "--fn: missing value")
    run = pipeline.cli("run", f["min"], "--fn", "--quiet")
    assert run.returncode == 1 and run.stderr.startswith("[E903] "), run
    assert "--fn: missing value" in run.stderr


@pytest.mark.parametrize("argv", [
    ("fmt", "--check", "--write", "{ugly}"),
    ("compile", "--wat", "-o", "{out}", "{good}"),
    ("compile", "--wat", "--target", "browser", "{good}"),
])
def test_repro_options_that_contradict_each_other(
        tmp_path: Path, argv: tuple[str, ...]) -> None:
    """`vera fmt --check --write FILE` exited 0 and only checked;
    `--wat -o` printed the WAT and wrote nothing; `--wat --target browser`
    printed the core module's WAT and emitted no bundle.  Each is E902, as
    `--reconcile --no-reconcile` was already, and nothing is written."""
    f = _files(tmp_path)
    before = Path(f["ugly"]).read_text(encoding="utf-8")
    out = tmp_path / "x.wasm"
    run = pipeline.cli(*[a.format(out=out.as_posix(), **f) for a in argv])
    assert run.returncode == 1 and run.stderr.startswith("[E902] "), run
    assert ", not both." in run.stderr
    assert Path(f["ugly"]).read_text(encoding="utf-8") == before
    assert not out.exists()


def test_repro_lsp_lists_stdio() -> None:
    """`vera lsp --stdio`, the flag editors pass by habit, is an option the
    server lists: stdio is its one transport.  Its help names it."""
    run = pipeline.cli("lsp", "--help")
    assert run.returncode == 0 and "--stdio" in run.stdout, run


# =====================================================================
# The documents: every command line they show, read by the table
# =====================================================================

ROOT = Path(__file__).resolve().parent.parent

#: The documents that show `vera` command lines to a reader.
DOCS = ("CLAUDE.md", "TOOLCHAIN.md", "README.md", "SKILL.md",
        "PYPI_README.md", "FAQ.md", "EXAMPLES.md", "DE_BRUIJN.md",
        "LSP_SERVER.md", "TESTING.md", "CONTRIBUTING.md", "examples/README.md",
        "vera/README.md", "docs/index.md", "docs/index.html")

#: A fence whose lines are pictures or prose, not commands.
_PROSE_FENCES = ("text", "json", "vera", "diff", "python", "wat", "toml",
                 "yaml", "javascript", "js", "html")


def _doc_command_lines(path: Path) -> list[tuple[int, list[str]]]:
    """Each `vera <command> ...` the document shows in code: an inline code
    span, or a line of a shell fence with its comment cut and its
    continuation joined.  Placeholders (`<file>`, `[--json]`, `...`, a
    capitalised name) end the reading of that line: they are notation."""
    from vera.command_line import COMMANDS

    names = "|".join(sorted(COMMANDS, key=len, reverse=True))
    pattern = re.compile(
        rf"(?<![\w/.-])vera ({names})(?![\w-])((?: +[^\s`|;&<>()\[\]{{}}\"']+)*)")
    found: list[tuple[int, list[str]]] = []
    fence: str | None = None
    lines = path.read_text(encoding="utf-8").splitlines()
    n = 0
    while n < len(lines):
        line = lines[n]
        n += 1
        stripped = line.lstrip()
        if stripped.startswith("```"):
            fence = None if fence is not None else (stripped[3:].strip() or "sh")
            continue
        if fence is not None:
            if fence in _PROSE_FENCES:
                continue
            while line.endswith("\\") and n < len(lines):
                line = line[:-1] + " " + lines[n]
                n += 1
            snippets = [re.split(r"\s#", line)[0]]
        else:
            snippets = [m.group(1) or m.group(2) for m in
                        re.finditer(r"`([^`]+)`|<code>(.*?)</code>", line)]
        for snippet in snippets:
            # A table cell escapes its pipe: what follows is another command.
            snippet = snippet.split("\\|")[0]
            for m in pattern.finditer(snippet):
                tokens = [m.group(1)] + [t.rstrip(".,:;") for t in m.group(2).split()]
                if any(re.search(r"[*…$%]|\.\.\.|^[A-Z_]+$", t) for t in tokens[1:]):
                    continue
                found.append((n, tokens))
    return found


def test_every_documented_command_line_is_one_the_table_takes() -> None:
    """A command line a document shows is one the table takes: no option
    the command does not list, no second file, no value it does not take.
    A line that names no file is read as if it named one (a document says
    `vera verify --json` of no file in particular), and a valued option
    standing last with no value is a document naming the option."""
    from vera.command_line import Refusal, parse

    paths = [ROOT / d for d in DOCS] + sorted((ROOT / "spec").glob("*.md"))
    refused: list[str] = []
    seen = 0
    for path in paths:
        for line, tokens in _doc_command_lines(path):
            seen += 1
            read = parse(tokens)
            if isinstance(read, Refusal) and "names no file" in read.diagnostic.description:
                read = parse([*tokens, "file.vera"])
            if not isinstance(read, Refusal):
                continue
            if read.diagnostic.description.endswith(": missing value"):
                continue
            # Whether the file exists is the tree's, not the table's.
            if read.diagnostic.error_code == "E900":
                continue
            refused.append(f"{path.relative_to(ROOT).as_posix()}:{line}: vera "
                           f"{' '.join(tokens)}: {read.diagnostic.description}")
    assert seen > 500, seen
    assert not refused, "\n".join(refused)


def _json_list(text: str) -> list[str]:
    return re.findall(r"`(?:vera )?(\w+)`", text)


@pytest.mark.parametrize(("path", "anchor", "end"), [
    ("spec/00-introduction.md", "via the `--json` flag, supported on ", ". The JSON"),
    ("TOOLCHAIN.md", "2. **Two audiences.** ", " have a `--json` mode"),
    ("TOOLCHAIN.md", "The diagnostic-producing commands ", " speak `--json`"),
])
def test_each_sentence_listing_the_json_commands_is_the_table(
        path: str, anchor: str, end: str) -> None:
    """The prose that lists the commands taking `--json` lists what the
    table says (the introspection commands apart where the sentence names
    them separately), the `typecheck` alias included: the table lists it as
    a command of its own, and `owners()`, which names the commands in a
    refusal, leaves it out, so the oracle is the table itself."""
    from vera.command_line import COMMANDS

    text = (ROOT / path).read_text(encoding="utf-8")
    start = text.index(anchor) + len(anchor)
    listed = sorted(_json_list(text[start:text.index(end, start)]))
    takers = [n for n, c in COMMANDS.items() if c.option("--json")]
    assert "typecheck" in takers
    registries = ["builtins", "effects", "errors"]
    assert listed in (sorted(takers),
                      sorted(t for t in takers if t not in registries)), listed


def test_the_commands_whose_success_carries_no_ok_are_the_spec_s(
        tmp_path: Path) -> None:
    """Spec §0.5.8 makes `ok` the exit signal and names the commands whose
    `--json` output on success is a listing with no `ok` (the registries'
    `schema` and `items`, the AST).  Each command taking `--json` is run to
    success on a program, and the ones whose output has no `ok` are the ones
    the sentence names; each of them, refused, is the envelope with `ok`
    false and exit 1."""
    from vera.command_line import COMMANDS

    f = _files(tmp_path)
    no_ok: list[str] = []
    for name, command in COMMANDS.items():
        if command.option("--json") is None:
            continue
        argv = [name, "--json"] + ([f["good"]] if command.reads_file else [])
        run = pipeline.cli(*argv)
        assert run.returncode == 0, (name, run)
        out = json.loads(run.stdout)
        if "ok" in out:
            assert out["ok"] is True, (name, out)
            continue
        no_ok.append(name)
        if not command.reads_file:
            assert sorted(out) == ["items", "schema"], (name, sorted(out))
        refused = pipeline.cli(name, "--json", "--bogus")
        envelope = json.loads(refused.stdout)
        assert refused.returncode == 1 and envelope["ok"] is False, (name, envelope)
    text = (ROOT / "spec/00-introduction.md").read_text(encoding="utf-8")
    anchor = "The exception is a command whose output on success is a listing"
    end = "carries `ok` when it succeeds"
    assert anchor in text and end in text, (
        f"spec §0.5.8 names no exception to `ok`, but {sorted(no_ok)} print no "
        "`ok` on success")
    start = text.index(anchor)
    # The commands the exception names, up to the clause that says they
    # carry no `ok`: a later mention (`vera ast` a source that does not
    # parse) is not a name in the list.
    named = sorted(set(re.findall(r"`vera (\w+)`", text[start:text.index(end, start)])))
    assert named == sorted(no_ok), (
        f"spec §0.5.8 names {named} as printing no `ok`; what runs: {sorted(no_ok)}")


def test_the_sentence_naming_the_commands_that_refuse_json_is_the_table() -> None:
    """TOOLCHAIN.md names the commands that refuse `--json`: every command
    the table gives no `--json`, and no other."""
    from vera.command_line import COMMANDS

    text = (ROOT / "TOOLCHAIN.md").read_text(encoding="utf-8")
    anchor = "The rest ("
    start = text.index(anchor) + len(anchor)
    listed = sorted(_json_list(text[start:text.index(") refuse the flag", start)]))
    assert listed == sorted(n for n, c in COMMANDS.items() if not c.option("--json"))


def test_toolchain_s_table_is_the_one_the_command_line_reads() -> None:
    """TOOLCHAIN.md's command-options block is what `render_lists.py`
    writes from `vera.command_line.COMMANDS`, on every pull request rather
    than only at the release check."""
    from vera.command_line import markdown_table

    text = (ROOT / "TOOLCHAIN.md").read_text(encoding="utf-8")
    begin = "<!-- render_lists:begin command-options -->\n"
    start = text.index(begin) + len(begin)
    assert text[start:text.index("<!-- render_lists:end command-options -->")] == (
        markdown_table())


def test_usage_and_every_help_name_each_option_the_table_lists() -> None:
    """USAGE and each `--help` are rendered from the table: every option of
    every command appears in USAGE with its owners, and in that command's
    help; nothing else in the table is left out."""
    from vera.cli import USAGE
    from vera.command_line import COMMANDS, command_help, owners

    for name, command in COMMANDS.items():
        assert re.search(rf"^    {name}\b", USAGE, re.M), name
        help_text = command_help(name)
        for option in command.options:
            assert option.name in help_text, (name, option.name)
            assert re.search(
                rf"^    {re.escape(option.name)}\b.*\({re.escape(', '.join(owners(option.name)))}\)$",
                USAGE, re.M), option.name
