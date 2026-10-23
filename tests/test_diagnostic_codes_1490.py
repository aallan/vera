"""Every diagnostic carries a registered code, and none is built by hand
(#1490, #1793).

Spec §0.5.1 requires every diagnostic to carry a stable code.  Five sites
under ``vera/`` built one without: the missing-visibility error (now E188),
the removed `Float` alias (E136, the unknown type name it is), code
generation's guard rail for a call with no target, in its two shapes (E624),
and the WAT assembler's failure (E699, as its sibling branch).  The command
line built its 25 JSON diagnostics as dict literals with no code, no
rationale, no fix and no spec section, and printed their text as a bare
`Error:` line.  Each is now a `Diagnostic` built in `vera.command_errors`,
in two new ranges: E8xx for a program's own failure while it runs (E800, the
runtime trap) and E9xx for a refusal of the command line itself (E900 to
E911).  The JSON envelope keeps every field it had, and the text form is the
diagnostic block every diagnostic prints.  `scripts/check_diagnostic_fields.py`
now fails a diagnostic site with no code, which no opt-out waives, and a
diagnostic built by hand, bar the two its `HAND_BUILT_EXCEPTIONS` names.

E604 and E605 named state effects in the registry and were emitted for an
unsupported parameter type and an unsupported return type, the concepts
E600 and E601 already name: the compilability check now emits those, E604
and E605 leave the registry, and E607 is titled for what it reports.  #1793:
`vera compile` and `vera run` had no backstop for an exception the check
raised, and printed a traceback with an empty stdout under `--json`.

The matrix crosses each E8xx/E9xx concept with every command line that
reports it, in text and, where the command has it, under `--json`, through
the suite's in-process CLI driver.  Products that are not cells: `vera
parse`, `vera fmt` and `vera serve` have no `--json`; E910 (a port another
process holds) and E911 (an extra that is not installed) need a socket and
an import the matrix does not hold, and are unparametrised cells; E624 is
reached by no command, since the check refuses a call with no target first,
and is read from the emitter.
"""

from __future__ import annotations

import importlib.util
import json
import socket
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline
from tests.codegen_helpers import skip_map_inserts  # noqa: F401  (the fixture)
from vera import command_errors as ce

pytestmark = pytest.mark.matrix(decides=[
    "vera/cli.py", "vera/command_errors.py", "vera/errors.py",
    "vera/introspect.py", "vera/checker/registration.py",
    "vera/checker/resolution.py", "vera/codegen/api.py",
    "vera/codegen/compilability.py", "vera/codegen/core.py",
    "vera/codegen/modules.py",
])

ROOT = Path(__file__).resolve().parent.parent

#: The section every E8xx and E9xx diagnostic cites: the one that names
#: the two ranges.
SECTION = 'Chapter 0, Section 0.5.1 "Diagnostic Structure"'

# =====================================================================
# The programs
# =====================================================================

_HEAD = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

PROGRAMS = {
    # Issue #1490's program: a function with no visibility.
    "novis": f"fn f(@Int -> @Int)\n{_HEAD}{{\n  @Int.0\n}}\n",
    "novis_data": (f"data Colour {{ Red, Green }}\n\npublic fn main(@Unit -> @Int)"
                   f"\n{_HEAD}{{\n  0\n}}\n"),
    "float": f"public fn half(@Float -> @Float)\n{_HEAD}{{\n  @Float.0\n}}\n",
    "ok": (f"public fn main(@Unit -> @Int)\n{_HEAD}{{\n  42\n}}\n\n"
           f"public fn add(@Int, @Int -> @Int)\n{_HEAD}{{\n  @Int.0 + @Int.1\n}}\n\n"
           f"private fn hidden(@Int -> @Int)\n{_HEAD}{{\n  @Int.0\n}}\n"),
    "noexport": f"private fn main(@Unit -> @Int)\n{_HEAD}{{\n  42\n}}\n",
    "lib": f"public fn add(@Int, @Int -> @Int)\n{_HEAD}{{\n  @Int.0 + @Int.1\n}}\n",
    "divzero": (f"public fn divide(@Int, @Int -> @Int)\n{_HEAD}{{\n  @Int.1 / @Int.0\n}}"
                f"\n\npublic fn main(@Unit -> @Int)\n{_HEAD}{{\n  divide(10, 0)\n}}\n"),
    # A host family `--target wasi-p2` does not implement.
    "http": ("public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
             "  effects(<IO, Http>)\n{\n"
             '  let @Result<String, String> = Http.get("http://127.0.0.1:1/");\n'
             '  IO.print("x")\n}\n'),
    # `tally` holds a construct code generation drops (#1183's fixture: its
    # `map_insert` skips under `skip_map_inserts`, since the check refuses the
    # Array-valued map that skipped, E135), so `main` is dropped behind it;
    # `survivor` keeps its export.
    "dropped": (
        "private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        '  let @Map<String, Int> = map_insert(map_new(), "a", 1);\n'
        "  map_size(@Map<String, Int>.0)\n}\n\n"
        "public fn main(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        "  tally()\n}\n\n"
        "public fn survivor(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        "  4243\n}\n"),
    "all_dropped": (
        "private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        '  let @Map<String, Int> = map_insert(map_new(), "a", 1);\n'
        "  map_size(@Map<String, Int>.0)\n}\n\n"
        "public fn main(-> @Int) requires(true) ensures(true) effects(pure) {\n"
        "  tally()\n}\n"),
    # A generic nothing instantiates: its `@T` parameter, and its `@T`
    # return, have no WASM representation (E600, E601).
    "generic_param": f"public forall<T> fn ident(@T -> @T)\n{_HEAD}{{\n  @T.0\n}}\n",
    "generic_return": ("public forall<T> fn first(@Array<T> -> @T)\n"
                       "  requires(array_length(@Array<T>.0) > 0)\n  ensures(true)\n"
                       "  effects(pure)\n{\n  @Array<T>.0[0]\n}\n"),
}


def _write(root: Path, name: str) -> Path:
    path = root / f"{name}.vera"
    path.write_text(PROGRAMS[name], encoding="utf-8")
    return path


def _envelope(run: pipeline.CliResult) -> dict[str, Any]:
    out = json.loads(run.stdout)
    assert isinstance(out, dict), out
    return out


def _coded(envelope: dict[str, Any], code: str) -> dict[str, Any]:
    (found,) = [d for d in envelope["diagnostics"] if d.get("error_code") == code]
    return found


# =====================================================================
# The reported programs
# =====================================================================


def test_repro_1490_missing_visibility_is_e188_in_text_and_json(
    tmp_path: Path,
) -> None:
    """Issue #1490's program, and a `data` declaration with no visibility:
    each carried no code at fa9bcbe6, so `--json` had no `error_code` and the
    text no `[Exxx]` prefix; each is E188."""
    for name, kind, decl in (("novis", "fn", "f"), ("novis_data", "data", "Colour")):
        path = _write(tmp_path, name)
        envelope = _envelope(pipeline.cli("check", "--json", path))
        found = _coded(envelope, "E188")
        assert found["description"] == (
            f"Missing visibility on '{decl}'. Add 'public' or 'private' "
            f"before '{kind}'.")
        assert found["spec_ref"] == 'Chapter 8, Section 8.4 "Visibility"'
        assert found["rationale"] == (
            "Every top-level function and data type must have an explicit "
            "visibility annotation.")
        shape = "(...)" if kind == "fn" else " { ... }"
        assert found["fix"] == (
            f"private {kind} {decl}{shape} or public {kind} {decl}{shape}")
        run = pipeline.cli("check", path)
        assert run.returncode == 1
        assert run.stderr.startswith(f"[E188] Error at {path}, line 1, column 1:")


def test_repro_the_removed_float_alias_is_e136(tmp_path: Path) -> None:
    """`Float`, the removed alias, names no type: the unknown type name,
    E136, with its own message; it carried no code at fa9bcbe6."""
    path = _write(tmp_path, "float")
    envelope = _envelope(pipeline.cli("check", "--json", path))
    found = _coded(envelope, "E136")
    assert found["description"] == "'Float' is not a type. Did you mean 'Float64'?"
    assert found["rationale"] == "'Float' was removed; use 'Float64' instead."
    assert found["spec_ref"] == 'Chapter 2, Section 2.2 "Primitive Types"'
    assert pipeline.cli("check", path).stderr.startswith("[E136] Error at ")


def test_repro_the_guard_rail_is_e624_in_both_shapes() -> None:
    """Code generation's rail for a call with no target, a module-qualified
    call and a bare one: one code, E624.  No command reaches it (the check
    refuses the call first, E200, E230, E233 or E340), so it is read from
    the emitter, as `tests/test_warning_severity_1513.py` reads its text."""
    from vera.codegen import CodeGenerator

    source = PROGRAMS["ok"]
    call = pipeline.parse(source).program.declarations[0].decl
    gen = CodeGenerator(pipeline.typed(), source=source, file="main.vera")
    gen._emit_cross_module_error(call, "f", "m::f")
    gen._emit_cross_module_error(call, "f")
    rails = [d for d in gen.diagnostics
             if "is not defined in this module" in d.description]
    assert [d.error_code for d in rails] == ["E624", "E624"], rails
    assert [(d.severity, d.spec_ref) for d in rails] == [
        ("error", 'Chapter 8, Section 8.5.3 "Module-Qualified Calls"'),
        ("error", 'Chapter 8, Section 8.5.1 "Bare Calls"')], rails


def test_repro_the_wat_assembler_s_failure_is_e699(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An assembler failure that is no codegen invariant was the one
    exempt, codeless site; it is E699, with its sibling's fields."""
    import wasmtime

    def refuse(_wat: str) -> bytes:
        raise wasmtime.WasmtimeError("unexpected token")

    monkeypatch.setattr(wasmtime, "wat2wasm", refuse)
    compiled = pipeline.compile(PROGRAMS["ok"])
    (found,) = [d for d in compiled.diagnostics
                if d.description.startswith("WAT compilation failed")]
    assert (found.error_code, found.severity) == ("E699", "error")
    assert found.description == "WAT compilation failed: unexpected token"
    assert found.rationale == (
        "Code generation produced WebAssembly text the assembler refuses. "
        "That is a bug in the compiler, not something to change in the "
        "program.")
    assert found.fix == ("Please file a bug report with the offending program "
                         "at https://github.com/aallan/vera/issues")
    assert found.spec_ref == SECTION


def test_repro_the_compilability_check_emits_e600_and_e601(
    tmp_path: Path,
) -> None:
    """A parameter, and a return, with no WASM representation were E604 and
    E605 at the compilability check, codes the registry gave state effects;
    each is the code of its concept, E600 and E601, which the signature
    compile emits for the same two."""
    for name, code, fn, what, rationale in (
        ("generic_param", "E600", "ident", "parameter",
         "WASM code generation supports a fixed set of parameter types; this "
         "parameter's type is not among them, so the function is skipped "
         "rather than miscompiled."),
        ("generic_return", "E601", "first", "return",
         "WASM code generation supports a fixed set of return types; this "
         "function's return type is not among them, so the function is "
         "skipped rather than miscompiled.")):
        envelope = _envelope(pipeline.cli(
            "compile", "--json", _write(tmp_path, name)))
        (warning,) = envelope["warnings"]
        assert (warning["error_code"], warning["severity"]) == (code, "warning")
        assert warning["description"] == (
            f"Function '{fn}' has unsupported {what} type — skipped.")
        assert warning["rationale"] == rationale


def test_repro_the_runtime_trap_is_e800(tmp_path: Path) -> None:
    """The runtime-trap envelope was a dict with no code; it is E800, located
    at the function that trapped, with `trap_kind`, `frames` and an
    always-present `fix` beside the diagnostic's fields, and its text the
    diagnostic block, then the source backtrace."""
    path = _write(tmp_path, "divzero")
    envelope = _envelope(pipeline.cli("run", "--json", path))
    assert set(envelope) == {"ok", "file", "diagnostics"}, envelope
    found = _coded(envelope, "E800")
    assert found["description"] == "Integer division by zero"
    assert found["location"] == {"line": 1, "column": 1, "file": str(path)}
    assert found["trap_kind"] == "divide_by_zero"
    assert [f["func"] for f in found["frames"]] == ["divide"]
    assert "requires(divisor != 0)" in found["fix"]
    assert found["spec_ref"] == SECTION and found["rationale"]
    run = pipeline.cli("run", path)
    assert run.returncode == 1
    assert run.stderr.startswith(f"[E800] Error at {path}, line 1, column 1:")
    assert run.stderr.index("  Fix:") < run.stderr.index("Source backtrace:")


def test_repro_a_trap_whose_kind_has_no_fix_keeps_fix_in_the_envelope(
    tmp_path: Path,
) -> None:
    """A contract violation's kind has no generic fix: the envelope still
    carries `fix`, empty, as it always did, and the text prints no Fix
    block."""
    path = tmp_path / "violation.vera"
    path.write_text(
        f"public fn positive(@Int -> @Int)\n  requires(@Int.0 > 0)\n"
        f"  ensures(true)\n  effects(pure)\n{{\n  @Int.0\n}}\n\n"
        f"public fn main(@Unit -> @Int)\n{_HEAD}{{\n  positive(0 - 5)\n}}\n",
        encoding="utf-8")
    found = _coded(_envelope(pipeline.cli("run", "--json", path)), "E800")
    assert found["fix"] == "" and found["trap_kind"] == "contract_violation"
    assert "Fix:" not in pipeline.cli("run", path).stderr


def test_repro_1793_run_and_compile_report_a_crash_in_the_check_as_e699(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Issue #1793: an exception the check raised escaped `vera run` and
    `vera compile` as a traceback, with an empty stdout under `--json`;
    each reports it as `vera check` does, the E699 envelope."""
    import vera.checker

    def crash(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("the check fell over")

    monkeypatch.setattr(vera.checker, "typecheck_with_artifacts", crash)
    path = _write(tmp_path, "ok")
    for command, doing in (("run", "running"), ("compile", "compiling")):
        run = pipeline.cli(command, "--json", path)
        assert run.returncode == 1, run
        found = _coded(_envelope(run), "E699")
        assert found["description"] == (
            f"Internal compiler error while {doing} '{path}': "
            f"RuntimeError: the check fell over")
        run = pipeline.cli(command, path)
        assert run.returncode == 1 and "Traceback" not in run.stderr, run
        assert run.stderr.startswith("[E699] Error at "), run.stderr


def test_repro_an_unclassified_trap_is_e800_and_any_other_exception_e699(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`vera run`'s backstop: an exception named as wasmtime's traps are
    that slipped past the classifier is still a trap, E800; any other is
    the internal error, E699, which it raised past `main` before."""
    import vera.codegen

    class Trap(Exception):
        pass

    class WasmtimeError(Exception):
        pass

    path = _write(tmp_path, "ok")
    for raised, code in ((Trap("wasm trap: unknown"), "E800"),
                         (WasmtimeError("wasm trap: unknown"), "E800"),
                         (KeyError("lost"), "E699")):
        def execute(*_args: object, exc: Exception = raised,
                    **_kwargs: object) -> object:
            raise exc

        monkeypatch.setattr(vera.codegen, "execute", execute)
        run = pipeline.cli("run", "--json", path)
        assert run.returncode == 1, run
        found = _coded(_envelope(run), code)
        if code == "E800":
            assert found == ce.runtime_trap(
                str(path), "Unhandled WASM trap: wasm trap: unknown").to_dict()
            text = pipeline.cli("run", path)
            assert ce.runtime_trap(
                str(path), "Unhandled WASM trap: wasm trap: unknown"
            ).format() + "\n" in text.stderr, text.stderr


def test_the_debug_knob_still_lets_a_host_error_out(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Under `VERA_DEBUG_HOST_ERRORS` the exception reaches the caller
    untouched (ENVIRONMENT.md): `vera run`'s backstop does not catch it."""
    import vera.codegen

    def execute(*_args: object, **_kwargs: object) -> object:
        raise ValueError("a binding's own error")

    monkeypatch.setattr(vera.codegen, "execute", execute)
    with pytest.raises(ValueError, match="a binding's own error"):
        pipeline.cli("run", _write(tmp_path, "ok"),
                     env={"VERA_DEBUG_HOST_ERRORS": "1"})


# =====================================================================
# The registry
# =====================================================================


def test_the_registry_lists_each_new_code_in_its_range() -> None:
    """`vera errors --json` lists E188 at check, E624 at code generation,
    E800 as run and E900 to E911 as command, each since 0.2.6; E604 and
    E605 are gone, and E607 is titled for what its sites report."""
    items = {i["code"]: i for i in pipeline.cli("errors", "--json").json()["items"]}
    expected = {"E188": "typecheck", "E624": "codegen", "E800": "run",
                **{f"E9{n:02d}": "command" for n in range(12)}}
    for code, phase in expected.items():
        assert (items[code]["phase"], items[code]["since"]) == (phase, "0.2.6"), code
    assert "E604" not in items and "E605" not in items
    assert items["E607"]["title"] == "State cell type code generation cannot lower"


# =====================================================================
# The matrix: every E8xx/E9xx concept, at every command line that
# reports it, in text and under --json
# =====================================================================


@dataclass(frozen=True)
class Refusal:
    """One command line that reports an E8xx/E9xx code."""

    #: The code.
    code: str
    #: The arguments: `{name}` is the program of that name, `{missing}` a
    #: path that names no file.
    argv: tuple[str, ...]
    #: The description, exactly as the command always wrote it.
    description: str
    #: The envelope's keys under `--json`; `None` for a command line with no
    #: `--json`.
    keys: frozenset[str] | None
    #: Whether the diagnostic's location, and the envelope's `file`, name
    #: the source file: a refusal the command line gets before it reads one
    #: names none.
    located: bool = True
    env: tuple[tuple[str, str], ...] = ()


_CHECK = frozenset({"ok", "file", "diagnostics", "warnings"})
_RUN = frozenset({"ok", "file", "diagnostics"})

_NO_EXPORTS_RUN = (
    "No exported functions to call.\n\nDeclared functions:\n  private fn main\n\n"
    "Only public functions are exported as WASM entry points.\n"
    "To make a function callable, declare it as public:\n\n"
    "  public fn main(-> @Int)\n    requires(true)\n    ensures(true)\n"
    "    effects(pure)\n  {{\n    0\n  }}\n\n"
    "Alternatively, use 'vera check' or 'vera verify' to validate without running.")
_FAMILY = ("--target wasi-p2: --target wasi-p2 does not support the following host "
           "family: http (http_get). Supported families: IO, Random.")

REFUSALS: dict[str, Refusal] = {
    # E900: the file is not there.
    **{f"E900-{c}": Refusal("E900", (c, "{missing}"), "file not found: {missing}",
                            keys) for c, keys in (
        ("check", _CHECK), ("verify", _CHECK), ("compile", _CHECK),
        ("run", _RUN), ("test", _RUN), ("ast", _CHECK), ("parse", None),
        ("fmt", None), ("serve", None))},
    "E900-check-explain-slots": Refusal(
        "E900", ("check", "--explain-slots", "{missing}"),
        "file not found: {missing}", _CHECK | {"slot_environments"}),
    # E901: an option the command does not read.
    "E901-timeout-ms": Refusal(
        "E901", ("check", "--timeout-ms", "5", "{ok}"),
        "--timeout-ms is only accepted by `vera verify`, not `vera check`. Set "
        "VERA_Z3_TIMEOUT_MS in the environment to reach `vera test` and the "
        "language server.", _RUN, located=False),
    "E901-distrust": Refusal(
        "E901", ("verify", "--distrust", "{ok}"),
        "--distrust is only accepted by `vera test`, not `vera verify`.",
        _RUN, located=False),
    "E901-reconcile": Refusal(
        "E901", ("check", "--reconcile", "{ok}"),
        "--reconcile is only accepted by `vera verify`, not `vera check`.",
        _RUN, located=False),
    "E901-no-reconcile": Refusal(
        "E901", ("run", "--no-reconcile", "{ok}"),
        "--no-reconcile is only accepted by `vera verify`, not `vera run`.",
        _RUN, located=False),
    # E902: options that contradict each other.
    "E902-compile-world": Refusal(
        "E902", ("compile", "--world", "server", "{ok}"),
        "--world server requires --target wasi-p2 (the core and browser "
        "targets have no world concept)", _CHECK),
    "E902-run-world": Refusal(
        "E902", ("run", "--world", "server", "{ok}"),
        "--world server requires --target wasi-p2 (the core and browser "
        "targets have no world concept)", _RUN),
    "E902-run-server-world": Refusal(
        "E902", ("run", "--target", "wasi-p2", "--world", "server", "{ok}"),
        "a server-world component exports wasi:http/incoming-handler, which "
        "`vera run` cannot host.  Compile it and serve with the wasmtime CLI:\n"
        "  vera compile --target wasi-p2 --world server {ok}\n"
        "  wasmtime serve <output>.wasm\n"
        "(or use `vera serve` for the native Python driver)", _RUN),
    "E902-run-fn-wasi": Refusal(
        "E902", ("run", "--target", "wasi-p2", "--fn", "add", "{ok}"),
        "--target wasi-p2 runs 'main' only (the component lifts a single "
        "entry); --fn add is not available.  Use the default target for --fn.",
        _RUN),
    "E902-reconcile-both": Refusal(
        "E902", ("verify", "--reconcile", "--no-reconcile", "{ok}"),
        "`vera verify` takes --reconcile or --no-reconcile, not both.",
        _RUN, located=False),
    # E903: an option's value it does not take.
    "E903-trials": Refusal(
        "E903", ("test", "--trials", "x", "{ok}"), "Invalid --trials value: x",
        _RUN, located=False),
    "E903-target": Refusal(
        "E903", ("compile", "--target", "nope", "{ok}"),
        "Invalid --target value: nope (expected 'wasm', 'browser', or "
        "'wasi-p2')", _RUN, located=False),
    "E903-world": Refusal(
        "E903", ("compile", "--world", "nope", "{ok}"),
        "Invalid --world value: nope (expected 'cli' or 'server')", _RUN,
        located=False),
    "E903-port": Refusal(
        "E903", ("serve", "--port", "x", "{ok}"),
        "--port requires an integer, not 'x'.", _RUN, located=False),
    "E903-timeout-ms": Refusal(
        "E903", ("verify", "--timeout-ms", "abc", "{ok}"),
        "--timeout-ms: expected a positive integer number of milliseconds, "
        "got 'abc'", _RUN, located=False),
    "E903-timeout-ms-missing": Refusal(
        "E903", ("verify", "{ok}", "--timeout-ms"), "--timeout-ms: missing value",
        _RUN, located=False),
    "E903-environment": Refusal(
        "E903", ("verify", "{ok}"),
        "VERA_Z3_TIMEOUT_MS: expected a positive integer number of "
        "milliseconds, got 'abc'",
        _RUN, located=False, env=(("VERA_Z3_TIMEOUT_MS", "abc"),)),
    # E904: a command line `vera` does not understand.
    "E904-unknown": Refusal(
        "E904", ("frobnicate", "{ok}"), "Unknown command: frobnicate", _RUN,
        located=False),
    "E904-no-file": Refusal(
        "E904", ("check",),
        "`vera check` names no file: it reads a .vera source file.", _RUN,
        located=False),
    # E905: nothing to call.
    "E905-run": Refusal("E905", ("run", "{noexport}"), _NO_EXPORTS_RUN, _RUN),
    "E905-compile": Refusal(
        "E905", ("compile", "{all_dropped}"),
        "No exported functions — the compiled module has no entry points.\n\n"
        "Declared public functions:\n  - main\n\n"
        "A public function whose body (or a callee's body) could not be "
        "compiled is dropped from the module with a diagnostic above; fix the "
        "reported construct to restore the export.",
        frozenset({"ok", "file", "exports", "diagnostics", "warnings"})),
    # E906: `--fn` names no export.
    "E906-missing": Refusal(
        "E906", ("run", "--fn", "nope", "{ok}"),
        "Function 'nope' not found in exports. Available: main, add", _RUN),
    "E906-private": Refusal(
        "E906", ("run", "--fn", "hidden", "{ok}"),
        "Function 'hidden' is declared private and cannot be called directly."
        "\n\nTo make it callable, change its declaration to:\n\n"
        "  public fn hidden", _RUN),
    # E907: the entry was dropped.
    "E907-main": Refusal(
        "E907", ("run", "{dropped}"),
        "Function 'main' was declared but dropped from the compiled output, so "
        "it cannot be run.\n\nReason: [E620] Function 'main' calls function "
        "'tally', which was skipped by codegen (see the [E602] diagnostic at "
        "line 2, column 27) — function dropped from the compiled output.\n\n"
        "Fix the construct at the reported location, or run a surviving "
        "function with --fn <name>.\nAvailable exports: survivor", _CHECK),
    # E908: what the target needs.
    "E908-browser": Refusal(
        "E908", ("compile", "--target", "browser", "{lib}"),
        "--target browser: no 'main' function is exported, so there is "
        "nothing for the page to call.  Exports: add.\n\nThe generated "
        "index.html calls main() on load, so the bundle would fail in the "
        "browser.", _CHECK),
    "E908-wasi-compile": Refusal(
        "E908", ("compile", "--target", "wasi-p2", "{http}"), _FAMILY, _CHECK),
    "E908-wasi-run": Refusal(
        "E908", ("run", "--target", "wasi-p2", "{http}"), _FAMILY, _RUN),
    "E908-serve": Refusal(
        "E908", ("serve", "--port", "0", "{lib}"),
        "vera serve: the program must export a public 'handle' function "
        "(public fn handle(@Request -> @Response) effects(<HttpServer>))", None),
    # E909: the arguments do not fit.
    "E909-count": Refusal(
        "E909", ("run", "--fn", "add", "{ok}", "--", "1"),
        "Function 'add' expects 2 arguments but 1 was provided.", _RUN),
    "E909-value": Refusal(
        "E909", ("run", "--fn", "add", "{ok}", "--", "a", "b"),
        "Argument 'a' is not valid for parameter type 'i64': invalid literal "
        "for int() with base 10: 'a'", _RUN),
    "E909-range": Refusal(
        "E909", ("run", "--fn", "add", "{ok}", "--", "99999999999999999999", "1"),
        "Argument '99999999999999999999' is out of range for parameter type "
        "@Int: an @Int holds -9223372036854775808 .. 9223372036854775807.",
        _RUN),
    "E909-none": Refusal(
        "E909", ("run", "--fn", "add", "{ok}"),
        "Function 'add' expects 2 parameters but 0 were provided.\n\n"
        "Available exports: main, add\n\nTo call a specific function with "
        "arguments:\n\n  vera run <file> --fn add -- <args>", _RUN),
    # E800: the program trapped.
    "E800-trap": Refusal(
        "E800", ("run", "{divzero}"), "Integer division by zero", _RUN),
}


def _expected(code: str, path: str | None, description: str) -> Any:
    """The diagnostic `vera.command_errors` builds for *code*: the oracle a
    command line's is held to.  Its texts are pinned on their own, by
    `test_each_command_error_s_text_is_exact`."""
    from vera import command_errors as ce

    if code == "E900":
        assert path is not None and description == f"file not found: {path}"
        return ce.file_not_found(path)
    factory = {
        "E901": lambda: ce.option_not_accepted(description),
        "E902": lambda: ce.contradictory_options(description, path),
        "E903": lambda: ce.invalid_option_value(description),
        "E904": lambda: ce.command_not_understood(description),
        "E905": lambda: ce.no_exports(path, description),
        "E906": lambda: ce.fn_not_exported(path, description),
        "E907": lambda: ce.entry_dropped(path, description),
        "E908": lambda: ce.target_requirement(path, description),
        "E909": lambda: ce.arguments_do_not_fit(path, description),
    }[code]
    return factory()


def _names(root: Path) -> dict[str, str]:
    names = {name: str(_write(root, name)) for name in PROGRAMS}
    names["missing"] = str(root / "missing.vera")
    return names


def _argv(refusal: Refusal, as_json: bool, names: dict[str, str]) -> list[str]:
    argv = [a.format(**names) for a in refusal.argv]
    if as_json:
        argv.insert(1, "--json")
    return argv


def _assert_refusal(name: str, as_json: bool, root: Path) -> None:
    """The command line exits 1 and prints its code's diagnostic, exactly as
    `vera.command_errors` builds it from the description the command always
    wrote: under `--json` in the envelope it always printed, its keys and
    `file` unchanged, printed as the CLI prints every envelope; in text as
    the diagnostic block, the usage text after an E904's alone."""
    from vera.cli import USAGE

    refusal = REFUSALS[name]
    names = _names(root)
    argv = _argv(refusal, as_json, names)
    run = pipeline.cli(*argv, env=dict(refusal.env))
    assert run.returncode == 1, (name, run)
    assert "Traceback" not in run.stderr, (name, run.stderr[-2000:])
    description = refusal.description.format(**names)
    path = next(a for a in argv if a.endswith(".vera")) if refusal.located else None
    if as_json:
        envelope = _envelope(run)
        assert run.stdout == json.dumps(envelope, indent=2) + "\n", name
        assert set(envelope) == refusal.keys, (name, envelope)
        if "slot_environments" in envelope:
            assert envelope["slot_environments"] == [], (name, envelope)
        assert envelope["ok"] is False and envelope["file"] == (path or ""), name
        found = _coded(envelope, refusal.code)
        if refusal.code == "E800":
            expected = dict(found, description=description)
            assert found["rationale"] == _rationale("E800"), name
        else:
            expected = _expected(refusal.code, path, description).to_dict()
        assert found == expected, (name, found, expected)
        return
    header = f"[{refusal.code}] Error at "
    assert header in run.stderr, (name, run.stderr[-2000:])
    if refusal.code == "E800":
        assert f"\n\n  {description}\n" in run.stderr, name
        return
    block = _expected(refusal.code, path, description).format() + "\n"
    assert block in run.stderr, (name, run.stderr[-3000:], block)
    assert run.stderr.endswith(block + USAGE + "\n") == (refusal.code == "E904"), name


def _rationale(code: str) -> str:
    from vera import command_errors as ce

    assert code == "E800"
    return ce.runtime_trap(None, "").rationale


def _cells() -> list[object]:
    return [pytest.param(name, as_json, id=f"{name}-{'json' if as_json else 'text'}")
            for name, refusal in REFUSALS.items()
            for as_json in ((False, True) if refusal.keys is not None else (False,))]


@pytest.mark.parametrize(("name", "as_json"), _cells())
@pytest.mark.usefixtures("skip_map_inserts")
def test_every_refusal_of_a_command_carries_its_code(
    name: str, as_json: bool, tmp_path: Path,
) -> None:
    """Each command line exits 1 with its code: under `--json` in the
    envelope it always printed, its keys unchanged and its description as
    the command always wrote it, now with a rationale, a fix and §0.5.1 as
    the spec section; in text as the diagnostic block, `[Exxx] Error at`
    first.  At fa9bcbe6 none carried a code, and the text was `Error:`."""
    _assert_refusal(name, as_json, tmp_path)


def _every(code: str, root: Path) -> None:
    """Every command line of the matrix that reports *code*, in each form:
    the unparametrised cell the matrix's sample cannot leave out."""
    for name, refusal in REFUSALS.items():
        if refusal.code != code:
            continue
        for as_json in ((False, True) if refusal.keys is not None else (False,)):
            cell = root / f"{name}-{as_json}"
            cell.mkdir()
            _assert_refusal(name, as_json, cell)


def test_named_e900_at_every_command(tmp_path: Path) -> None:
    _every("E900", tmp_path)


def test_named_e901_at_every_option(tmp_path: Path) -> None:
    _every("E901", tmp_path)


def test_named_e902_at_every_contradiction(tmp_path: Path) -> None:
    _every("E902", tmp_path)


def test_named_e903_at_every_value(tmp_path: Path) -> None:
    _every("E903", tmp_path)


def test_named_e904_at_every_command_line(tmp_path: Path) -> None:
    _every("E904", tmp_path)


@pytest.mark.usefixtures("skip_map_inserts")
def test_named_e905_at_compile_and_run(tmp_path: Path) -> None:
    _every("E905", tmp_path)


@pytest.mark.usefixtures("skip_map_inserts")
def test_named_e906_e907_at_run(tmp_path: Path) -> None:
    _every("E906", tmp_path)
    _every("E907", tmp_path)


def test_named_e908_at_every_target(tmp_path: Path) -> None:
    _every("E908", tmp_path)


def test_named_e909_at_every_argument_list(tmp_path: Path) -> None:
    _every("E909", tmp_path)


def test_named_e800_in_both_forms(tmp_path: Path) -> None:
    _every("E800", tmp_path)


def test_e910_a_port_another_process_holds(tmp_path: Path) -> None:
    """`vera serve` on a port another socket holds: E910, the bind refused,
    where it printed `Error: could not bind`."""
    server = ROOT / "examples" / "http_server.vera"
    held = socket.socket()
    held.bind(("127.0.0.1", 0))
    held.listen(1)
    try:
        port = held.getsockname()[1]
        second = socket.socket()
        try:
            second.bind(("127.0.0.1", port))
        except OSError as exc:
            refusal = str(exc)
        finally:
            second.close()
        run = pipeline.cli("serve", "--port", str(port), server)
    finally:
        held.close()
    assert run.returncode == 1, run
    expected = ce.cannot_bind(
        f"could not bind 127.0.0.1:{port} — {refusal}", str(server))
    assert run.stderr == expected.format() + "\n", run.stderr


def test_e911_the_language_server_without_its_extra(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """`vera lsp` with the `[lsp]` extra's transport not importable: E911,
    which names the module and the install command."""
    for name in [n for n in sys.modules
                 if n == "vera.lsp.server" or n == "pygls" or n.startswith("pygls.")]:
        monkeypatch.delitem(sys.modules, name)
    monkeypatch.setitem(sys.modules, "pygls", None)
    run = pipeline.cli("lsp")
    assert run.returncode == 1, run
    expected = ce.optional_dependency(
        "The LSP server needs the optional [lsp] extra, and `pygls` is not "
        "installed.")
    assert run.stderr == expected.format() + "\n", run.stderr


# =====================================================================
# The texts: each command_errors function's diagnostic, pinned
# =====================================================================

#: Each function of `vera.command_errors`, called on a fixed description and
#: path, and the diagnostic it builds, field by field: the oracle the matrix
#: holds every command line to is itself held to these.
_PINS: list[tuple[Any, dict[str, Any]]] = [
    (lambda: ce.runtime_trap("main.vera", "D800", fix="F800"),
        {'severity': 'error',
         'description': 'D800',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': 'The program stopped while it ran: a check the compiler emitted '
                      'failed, or WebAssembly refused an operation, and nothing after '
                      "that point ran. The trap's kind is `trap_kind` in the `--json` "
                      'envelope, and the source backtrace names the functions it '
                      'unwound through.',
         'fix': 'F800',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E800'}),
    (lambda: ce.file_not_found("dir/missing.vera"),
        {'severity': 'error',
         'description': 'file not found: dir/missing.vera',
         'location': {'line': 0, 'column': 0, 'file': 'dir/missing.vera'},
         'rationale': 'A command reads the Vera source file its command line names, '
                      'and no file exists at that path. A relative path is read from '
                      'the directory the command runs in.',
         'fix': 'Name a .vera file that exists: a path relative to the directory the '
                'command runs in, or an absolute one.\n'
                '\n'
                '  vera check path/to/program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E900'}),
    (lambda: ce.option_not_accepted("D901"),
        {'severity': 'error',
         'description': 'D901',
         'location': {'line': 0, 'column': 0},
         'rationale': 'An option belongs to the commands that read it. A command that '
                      'cannot honour an option refuses it rather than ignore it, so an '
                      'option never seems to take effect where it does not.',
         'fix': 'Drop the option, or give it to the command that takes it:\n'
                '\n'
                '  vera verify --timeout-ms 60000 program.vera\n'
                '  vera test --distrust program.vera\n'
                '  vera verify --no-reconcile program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E901'}),
    (lambda: ce.contradictory_options("D902", "main.vera"),
        {'severity': 'error',
         'description': 'D902',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': 'The options on this command line cannot all hold: one needs '
                      'another that is absent, or two ask for opposite things, so the '
                      'command cannot tell which was meant.',
         'fix': 'Keep one consistent set of options, as the description says. `--world '
                'server` needs `--target wasi-p2` and is served, not run; `--fn` runs '
                'under the default target; `vera verify` takes `--reconcile` or '
                '`--no-reconcile`:\n'
                '\n'
                '  vera compile --target wasi-p2 --world server program.vera\n'
                '  vera run --fn f program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E902'}),
    (lambda: ce.invalid_option_value("D903"),
        {'severity': 'error',
         'description': 'D903',
         'location': {'line': 0, 'column': 0},
         'rationale': "An option's value must be one the option takes. The description "
                      'names the option and, where it takes a fixed set, the values.',
         'fix': 'Give the option a value it takes: `--target` wasm, browser or '
                'wasi-p2; `--world` cli or server; `--trials` and `--port` an integer; '
                '`--timeout-ms` and VERA_Z3_TIMEOUT_MS a positive integer number of '
                'milliseconds.\n'
                '\n'
                '  vera verify --timeout-ms 60000 program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E903'}),
    (lambda: ce.command_not_understood("D904"),
        {'severity': 'error',
         'description': 'D904',
         'location': {'line': 0, 'column': 0},
         'rationale': '`vera` takes a command, its options and, for a command that '
                      "reads a program, the path of the program's source file. The "
                      'usage text lists the commands.',
         'fix': 'Name one of the commands the usage lists, and the file it reads:\n'
                '\n'
                '  vera check program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E904'}),
    (lambda: ce.no_exports("main.vera", "D905"),
        {'severity': 'error',
         'description': 'D905',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': "A module's entry points are the public functions code "
                      'generation compiled. With none, the compiled module has nothing '
                      'a host can call.',
         'fix': 'Declare the function to call public, and where code generation '
                'dropped a public function, fix the construct its [E602] warning '
                'names:\n'
                '\n'
                '  public fn main(-> @Int)\n'
                '    requires(true)\n'
                '    ensures(true)\n'
                '    effects(pure)\n'
                '  {\n'
                '    0\n'
                '  }',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E905'}),
    (lambda: ce.fn_not_exported("main.vera", "D906"),
        {'severity': 'error',
         'description': 'D906',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': '`--fn` names the function to call, and only an exported one, a '
                      'public function code generation compiled, can be called from '
                      'outside the module.',
         'fix': 'Name a function the description lists as exported, or declare the one '
                'you meant public:\n'
                '\n'
                '  vera run program.vera --fn main',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E906'}),
    (lambda: ce.entry_dropped("main.vera", "D907"),
        {'severity': 'error',
         'description': 'D907',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': 'Code generation dropped the function to run, because its body, '
                      'or the body of a function it calls, holds a construct code '
                      'generation cannot compile. Running another function in its '
                      'place would answer a question nobody asked.',
         'fix': 'Fix the construct the [E602] warning names (the [E620] chain says '
                'which call reaches it), or run another exported function with --fn.',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E907'}),
    (lambda: ce.target_requirement("main.vera", "D908"),
        {'severity': 'error',
         'description': 'D908',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': 'A target needs something of the program: `--target browser` '
                      'calls `main` when the page loads, `--target wasi-p2` hosts only '
                      'the host families it implements, and `vera serve` calls '
                      '`handle(@Request -> @Response)` for each request.',
         'fix': 'Give the program what the target needs, as the description says, or '
                'build it for the default target:\n'
                '\n'
                '  vera run program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E908'}),
    (lambda: ce.arguments_do_not_fit("main.vera", "D909"),
        {'severity': 'error',
         'description': 'D909',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': '`vera run` passes the arguments after `--` to the function it '
                      "calls, one per parameter, each read as its parameter's type and "
                      "held to that type's range.",
         'fix': 'Pass one argument per parameter, each a value of its type:\n'
                '\n'
                '  vera run program.vera --fn f -- 1 2',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E909'}),
    (lambda: ce.cannot_bind("D910", "main.vera"),
        {'severity': 'error',
         'description': 'D910',
         'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
         'rationale': '`vera serve` listens on a host and port, and the operating '
                      'system refused to bind them: another process holds the port, or '
                      'the host names no interface of this machine.',
         'fix': 'Serve on a free port, or stop the process that holds this one:\n'
                '\n'
                '  vera serve --port 8080 program.vera',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E910'}),
    (lambda: ce.optional_dependency("D911"),
        {'severity': 'error',
         'description': 'D911',
         'location': {'line': 0, 'column': 0},
         'rationale': "The language server's transport is an optional extra, so the "
                      'base install stays minimal, and `vera lsp` needs it.',
         'fix': 'Install the extra in the source checkout:\n'
                '\n'
                '  pip install -e ".[lsp]"',
         'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
         'error_code': 'E911'}),
]


def test_each_command_error_s_text_is_exact() -> None:
    """Every E8xx/E9xx diagnostic as `vera.command_errors` builds it: the
    location (the file, or none before a file is read), the rationale, the
    fix, the section every one cites, and the code."""
    for build, expected in _PINS:
        assert build().to_dict() == expected


#: A trap two of the program's own functions unwind through: `main` calls
#: `divide` outside a tail position, so its frame stays on the stack.
_NESTED_TRAP = (f"public fn divide(@Int, @Int -> @Int)\n{_HEAD}{{\n  @Int.1 / @Int.0\n}}\n\n"
                f"public fn main(@Unit -> @Int)\n{_HEAD}{{\n"
                f"  let @Int = divide(42, 0);\n  @Int.0\n}}\n")


def test_e800_is_located_at_the_innermost_function_of_the_program_s_own(
    tmp_path: Path,
) -> None:
    """A trap is located at the first frame of the program's own its
    backtrace names, the innermost, where the trap fired: `divide`, line 1,
    not `main`, which called it; and its text wraps the kind's fix for a
    terminal, every line within 76 columns."""
    path = tmp_path / "nested.vera"
    path.write_text(_NESTED_TRAP, encoding="utf-8")
    found = _coded(_envelope(pipeline.cli("run", "--json", path)), "E800")
    assert [f["func"] for f in found["frames"]] == ["divide", "main"], found
    assert found["location"] == {"line": 1, "column": 1, "file": str(path)}
    stderr = pipeline.cli("run", path).stderr
    fix = stderr[stderr.index("  Fix:\n\n"):stderr.index("\n\n  See: ")]
    lines = fix.splitlines()[2:]
    assert len(lines) > 1 and all(len(line) <= 76 for line in lines), lines
    assert " ".join(" ".join(lines).split()) == " ".join(found["fix"].split())


def test_e800_s_location_passes_runtime_helpers_and_unknown_names() -> None:
    """The location is the first frame of the program's own with a source
    line: a runtime helper's frame, and a frame whose name the source map
    does not hold, are passed over, and the first frame that qualifies is
    the one taken, not a later one."""
    from vera.runtime.traps import TrapFrame

    frames = [TrapFrame("alloc", "<builtin>", None, None, True),
              TrapFrame("anon_0", "<unknown>", None, None, False),
              TrapFrame("pick", "x.vera", 3, 9, False),
              TrapFrame("main", "x.vera", 11, 16, False)]
    found = ce.runtime_trap("x.vera", "D", frames=frames)
    assert (found.location.file, found.location.line,
            found.location.column) == ("x.vera", 3, 1)
    alone = ce.runtime_trap("y.vera", "D", frames=frames[:2])
    assert (alone.location.file, alone.location.line,
            alone.location.column) == ("y.vera", 0, 0)


#: An index out of bounds two of the program's own functions unwind
#: through; its kind's fix wraps differently at 71, 72 and 73 columns.
_OUT_OF_BOUNDS = (
    "public fn pick(@Array<Int>, @Int -> @Int)\n" + _HEAD
    + "{\n  @Array<Int>.0[@Int.0]\n}\n\n"
    + "public fn main(@Unit -> @Int)\n" + _HEAD
    + "{\n  let @Int = pick([1, 2, 3], 5);\n  @Int.0\n}\n")


def test_e800_s_text_wraps_its_kind_s_fix_at_72_columns(tmp_path: Path) -> None:
    """The text form wraps the trap kind's fix at 72 columns, each line
    indented four, so a terminal shows it within 76 (#547): the lines are
    exactly the paragraph's at that width."""
    import textwrap

    path = tmp_path / "oob.vera"
    path.write_text(_OUT_OF_BOUNDS, encoding="utf-8")
    found = _coded(_envelope(pipeline.cli("run", "--json", path)), "E800")
    assert found["trap_kind"] == "index_out_of_bounds", found
    assert found["location"] == {"line": 1, "column": 1, "file": str(path)}
    stderr = pipeline.cli("run", path).stderr
    fix = stderr[stderr.index("  Fix:\n\n") + len("  Fix:\n\n"):
                 stderr.index("\n\n  See: ")]
    assert fix.splitlines() == [
        "    " + line for line in textwrap.fill(found["fix"], width=72).splitlines()]


#: A host binding's refusal: its exception unwinds through no frame of the
#: program's own.
_HOST_ERROR = ("public fn main(@Unit -> @Unit)\n  requires(true) ensures(true) "
               "effects(<IO>)\n{\n  IO.print(\"before\");\n"
               "  IO.print(json_stringify(JNumber(nan())))\n}\n")


def test_e800_with_no_frame_of_the_program_s_is_located_at_the_file(
    tmp_path: Path,
) -> None:
    """A trap whose backtrace names no function of the program's own is
    located at the file the command ran, in the envelope and in the text."""
    path = tmp_path / "hosterr.vera"
    path.write_text(_HOST_ERROR, encoding="utf-8")
    found = _coded(_envelope(pipeline.cli("run", "--json", path)), "E800")
    assert (found["trap_kind"], found["frames"]) == ("host_error", []), found
    assert found["location"] == {"line": 0, "column": 0, "file": str(path)}
    run = pipeline.cli("run", path)
    assert f"[E800] Error at {path}, line 0, column 0:" in run.stderr, run.stderr


def test_e904_names_each_command_that_reads_a_file(tmp_path: Path) -> None:
    """Each command that reads a source file, given none, is E904 naming it,
    with the usage text after the diagnostic, and under `--json` the
    envelope; a word that is no command is E904 too, as unknown."""
    from vera.cli import USAGE

    commands = ("parse", "check", "typecheck", "verify", "test", "compile",
                "serve", "run", "ast", "fmt")
    for command in commands:
        expected = ce.command_not_understood(
            f"`vera {command}` names no file: it reads a .vera source file.")
        run = pipeline.cli(command)
        assert run.returncode == 1, (command, run)
        assert run.stderr == expected.format() + "\n" + USAGE + "\n", command
        run = pipeline.cli(command, "--json")
        assert run.returncode == 1, (command, run)
        assert _coded(_envelope(run), "E904") == expected.to_dict(), command
    run = pipeline.cli("nonsense")
    assert run.stderr.startswith(ce.command_not_understood(
        "Unknown command: nonsense").format()), run.stderr


# =====================================================================
# The fixes, applied
# =====================================================================

#: For each code whose fix edits a command line or a program mechanically:
#: the refused command line, and the one its fix writes.  Not here: E907's
#: fix is the construct its [E602] names, or another function, the second
#: of which is this table's E906 row; E910 serves forever once it binds;
#: E911 installs a package; E800's fix is a program change that moves the
#: failure to the call, not away; E624 no command reaches.
FIXES: dict[str, tuple[tuple[str, ...], tuple[str, ...]]] = {
    "E900": (("check", "{missing}"), ("check", "{ok}")),
    "E901": (("check", "--timeout-ms", "5", "{ok}"), ("check", "{ok}")),
    "E902": (("compile", "--wat", "--world", "server", "{http_server}"),
             ("compile", "--wat", "--target", "wasi-p2", "--world", "server",
              "{http_server}")),
    "E903": (("test", "--trials", "x", "{ok}"), ("test", "--trials", "3", "{ok}")),
    "E904": (("frobnicate", "{ok}"), ("check", "{ok}")),
    "E906": (("run", "--fn", "nope", "{ok}"), ("run", "{ok}", "--fn", "main")),
    "E908": (("compile", "--wat", "--target", "browser", "{lib}"),
             ("compile", "--wat", "{lib}")),
    "E909": (("run", "--fn", "add", "{ok}", "--", "1"),
             ("run", "--fn", "add", "{ok}", "--", "1", "2")),
}


@pytest.mark.parametrize("code", sorted(FIXES))
def test_a_command_line_s_fix_applied_passes(code: str, tmp_path: Path) -> None:
    """The refused command line exits 1 with the code; the one its fix
    writes exits 0 with no diagnostic of it."""
    refused, fixed = FIXES[code]
    names = {name: str(_write(tmp_path, name)) for name in PROGRAMS}
    names["missing"] = str(tmp_path / "missing.vera")
    server = tmp_path / "http_server.vera"
    server.write_bytes((ROOT / "examples" / "http_server.vera").read_bytes())
    names["http_server"] = str(server)
    before = pipeline.cli(*(a.format(**names) for a in refused))
    assert before.returncode == 1 and f"[{code}]" in before.stderr, before
    after = pipeline.cli(*(a.format(**names) for a in fixed))
    assert after.returncode == 0 and f"[{code}]" not in after.stderr, after


def test_e905_s_fix_applied_runs_the_function(tmp_path: Path) -> None:
    """E905's fix declares the function to call public: the program then
    runs, printing what `main` returns."""
    path = _write(tmp_path, "noexport")
    assert "[E905]" in pipeline.cli("run", path).stderr
    path.write_text(PROGRAMS["noexport"].replace("private fn", "public fn"),
                    encoding="utf-8")
    run = pipeline.cli("run", path)
    assert (run.returncode, run.stdout) == (0, "42\n"), run


def test_e188_s_fix_applied_passes_check(tmp_path: Path) -> None:
    """E188's fix writes the visibility before the declaration's keyword;
    the program then checks with no E188."""
    for name in ("novis", "novis_data"):
        path = _write(tmp_path, name)
        found = _coded(_envelope(pipeline.cli("check", "--json", path)), "E188")
        keyword = "fn" if name == "novis" else "data"
        assert found["fix"].startswith(f"private {keyword} "), found
        path.write_text("private " + PROGRAMS[name], encoding="utf-8")
        run = pipeline.cli("check", "--json", path)
        assert run.returncode == 0 and not _envelope(run)["diagnostics"], run


def test_e136_s_fix_applied_passes_check(tmp_path: Path) -> None:
    """E136's fix for the removed alias replaces it with the type it
    became; the program then checks clean."""
    path = _write(tmp_path, "float")
    found = _coded(_envelope(pipeline.cli("check", "--json", path)), "E136")
    assert found["fix"] == "Replace 'Float' with 'Float64'."
    path.write_text(PROGRAMS["float"].replace("Float", "Float64"), encoding="utf-8")
    assert pipeline.cli("check", path).returncode == 0


# =====================================================================
# The gate: a code at every site, and no diagnostic built by hand
# =====================================================================


@pytest.fixture(scope="module")
def gate() -> Any:
    spec = importlib.util.spec_from_file_location(
        "check_diagnostic_fields_1490",
        ROOT / "scripts" / "check_diagnostic_fields.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # Its dataclasses resolve their module through `sys.modules`.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_SHAPES = '''\
class Checker:
    def check(self, node):
        self._error(node, "a", rationale="r", fix="f", spec_ref="s")
        self._warning(node, "b", rationale="r", spec_ref="s")
        self._error_once(node, "c", rationale="r")
        report(Diagnostic(description="d", location=loc, rationale="r",
                          fix="f", spec_ref="s"))
        self._error(node, "e", error_code="")  # diag-fields-exempt: a reason
'''


def test_the_gate_requires_a_code_at_every_site_shape(gate: Any) -> None:
    """Each shape of diagnostic site with no code is a violation: a
    `Diagnostic(...)`, an `_error`, a `_warning`, code generation's
    `_error_once`, and an empty code under the opt-out marker, which waives
    no code; a code threaded from the caller is one."""
    found = sorted(
        gate.error_code_presence_violations_in_source(_SHAPES, "vera/x.py"),
        key=lambda v: v.line)
    assert [(v.line, v.target) for v in found] == [
        (3, "_error"), (4, "_warning"), (5, "_error_once"), (6, "Diagnostic"),
        (8, "_error")], found
    threaded = _SHAPES.replace('rationale="r"', 'rationale="r", error_code=code')
    assert [v.line for v in gate.error_code_presence_violations_in_source(
        threaded, "vera/x.py")] == [8]


def test_the_gate_refuses_a_diagnostic_built_by_hand(gate: Any) -> None:
    """A dict with a "severity" key, a `dict(severity=...)` call and a
    string holding a "severity" JSON key are violations, as the command
    line's 25 dict-built diagnostics were; at the sites the exception list
    names they are not, and an exception naming no such site is one."""
    source = '''\
def refuse():
    one = {"severity": "error", "description": "x"}
    two = dict(severity="error", description="y")
    three = '{"severity": "error"}'
    return one, two, three


def _internal_error_envelope():
    return '{"severity": "error", "error_code": "E699"}'
'''
    found = gate.hand_built_diagnostic_violations_in_source(source, "vera/cli.py")
    assert sorted(v.line for v in found) == [2, 3, 4], found
    assert sorted(v.line for v in gate.hand_built_diagnostic_violations_in_source(
        source, "vera/other.py")) == [2, 3, 4, 9]


def test_an_exception_naming_no_hand_built_site_fails_the_gate(
    gate: Any, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The exception list only shrinks: an entry naming a function that
    builds no diagnostic by hand, in a file the gate reads, is a violation."""
    stale = ("vera/cli.py", "cmd_version")
    monkeypatch.setitem(gate.HAND_BUILT_EXCEPTIONS, stale, "a reason")
    found = gate.hand_built_diagnostic_violations([ROOT / "vera" / "cli.py"])
    assert [v.missing for v in found] == [[
        "HAND_BUILT_EXCEPTIONS names vera/cli.py::cmd_version, which builds "
        "no diagnostic by hand: delete the entry"]], found


def test_the_live_tree_carries_a_code_everywhere_and_builds_none_by_hand(
    gate: Any,
) -> None:
    """Over every file under `vera/`: no codeless site, no hand-built
    diagnostic, and each named exception a live site.  At fa9bcbe6 the
    two passes reported the five codeless sites and the 25 envelopes."""
    files = gate.iter_vera_files(ROOT / "vera")
    assert gate.error_code_presence_violations(files) == []
    assert gate.hand_built_diagnostic_violations(files) == []


def test_mutant_a_code_removed_from_one_site_fails_the_gate(gate: Any) -> None:
    """The mutant the gate exists for: E188 taken off the missing-visibility
    site, the instance #1490 reported, is a violation at that site."""
    path = ROOT / "vera" / "checker" / "registration.py"
    source = path.read_text(encoding="utf-8")
    assert source.count('error_code="E188",') == 1
    mutant = source.replace('error_code="E188",', "")
    found = gate.error_code_presence_violations_in_source(
        mutant, "vera/checker/registration.py")
    assert len(found) == 1 and found[0].target == "_error", found
    assert gate.error_code_presence_violations_in_source(
        source, "vera/checker/registration.py") == []
