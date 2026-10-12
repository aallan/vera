"""tests/pipeline.py, the suite's one driver for the compiler pipeline.

Each stage is held to the command it stands in for: over every corpus
program, ``check``, ``verify`` and ``compile`` give exactly the envelope
``vera <stage> --json`` prints and ``compile`` exactly the WAT ``vera compile
--wat`` prints, and over every conformance program whose run is pinned,
``run`` gives the envelope ``vera run --json`` prints.  The CLI side runs in
process through ``pipeline.cli``, which is itself held to the CLI run as a
process.  The rest pins the driver's own rules: what a stage takes, what
reading an artefact a stage did not make raises, the unchecked compile, and
what ``cli`` borrows and gives back.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

from tests import pipeline
from vera.codegen import compile as codegen_compile
from vera.errors import ParseError
from vera.runtime.traps import WasmTrapError

ROOT = Path(__file__).resolve().parent.parent
CONFORMANCE = ROOT / "tests" / "conformance"
EXAMPLES = ROOT / "examples"
MANIFEST: list[dict[str, object]] = json.loads(
    (CONFORMANCE / "manifest.json").read_text(encoding="utf-8"))

CORPUS = sorted(
    [CONFORMANCE / str(e["file"]) for e in MANIFEST]
    + list(EXAMPLES.glob("*.vera")))
PINNED_RUNS = [
    CONFORMANCE / str(e["file"]) for e in MANIFEST
    if e["level"] == "run" and "expected_stdout" in e
]


def _id(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


# =====================================================================
# Each stage reports what its command reports
# =====================================================================


@pytest.mark.parametrize("path", CORPUS, ids=_id)
def test_each_stage_reports_what_its_command_reports(path: Path) -> None:
    assert pipeline.check(path).envelope() == (
        pipeline.cli("check", "--json", path).json())
    assert pipeline.verify(path).envelope() == (
        pipeline.cli("verify", "--json", path).json())
    compiled = pipeline.compile(path)
    envelope = compiled.envelope()
    assert envelope == pipeline.cli("compile", "--json", path).json()
    if envelope["ok"]:
        assert pipeline.cli("compile", "--wat", path).stdout == (
            compiled.wat + "\n")


@pytest.mark.parametrize("path", PINNED_RUNS, ids=_id)
def test_a_run_reports_what_vera_run_reports(path: Path) -> None:
    ran = pipeline.run(path, stdin="")
    assert ran.envelope() == pipeline.cli("run", "--json", path).json()
    assert ran.returncode == pipeline.cli("run", path).returncode


@pytest.mark.parametrize("name,distrust", [
    ("factorial.vera", False),
    ("safe_divide.vera", False),
    ("refinement_types.vera", False),
    ("factorial.vera", True),
])
def test_contract_testing_reports_what_vera_test_reports(
    name: str, distrust: bool,
) -> None:
    path = EXAMPLES / name
    tested = pipeline.contract_test(path, trials=5, distrust=distrust)
    flags = ["--distrust"] if distrust else []
    envelope = pipeline.cli("test", "--json", "--trials", "5", *flags, path).json()
    assert tested.ok == envelope["ok"]
    summary = tested.result.summary
    assert {k: getattr(summary, k) for k in envelope["summary"]} == (
        envelope["summary"])
    assert [(f.fn_name, f.category) for f in tested.result.functions] == [
        (f["name"], f["category"]) for f in envelope["functions"]]


def test_the_corpus_is_all_there() -> None:
    """The differential above is over the whole corpus, not whatever a glob
    happened to find: every manifest entry and every example is a cell."""
    assert len(CORPUS) == len(MANIFEST) + len(list(EXAMPLES.glob("*.vera")))
    assert len(PINNED_RUNS) > 100


# =====================================================================
# The CLI in process is the CLI
# =====================================================================


_HELLO = EXAMPLES / "hello_world.vera"
_FACTORIAL = EXAMPLES / "factorial.vera"


@pytest.mark.parametrize("args", [
    ("check", _HELLO),
    ("check", "--json", _FACTORIAL),
    ("verify", _FACTORIAL),
    ("verify", "--json", _FACTORIAL),
    ("compile", "--wat", _HELLO),
    ("run", _HELLO),
    ("run", "--json", _FACTORIAL, "--fn", "factorial", "--", "5"),
    ("check", ROOT / "no-such-file.vera"),
], ids=lambda a: " ".join(Path(x).name if isinstance(x, Path) else x for x in a))
def test_cli_in_process_prints_what_the_cli_process_prints(
    args: tuple[str | Path, ...],
) -> None:
    argv = [os.fspath(a) for a in args]
    process = subprocess.run(
        [sys.executable, "-m", "vera.cli", *argv],
        capture_output=True, text=True, encoding="utf-8", check=False,
        cwd=ROOT, stdin=subprocess.DEVNULL, timeout=300,
    )
    mine = pipeline.cli(*argv)
    assert (mine.returncode, mine.stdout, mine.stderr) == (
        process.returncode, process.stdout, process.stderr)


def test_cli_gives_back_what_it_borrows(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("VERA_W24_PROBE", "kept")
    monkeypatch.delenv("VERA_W24_ABSENT", raising=False)
    argv, stdin, stdout, stderr = sys.argv, sys.stdin, sys.stdout, sys.stderr
    result = pipeline.cli(
        "check", "--json", _HELLO,
        env={"VERA_W24_PROBE": None, "VERA_W24_ABSENT": "set"},
    )
    assert result.returncode == 0 and result.json()["ok"] is True
    assert (sys.argv, sys.stdin, sys.stdout, sys.stderr) == (
        argv, stdin, stdout, stderr)
    assert os.environ["VERA_W24_PROBE"] == "kept"
    assert "VERA_W24_ABSENT" not in os.environ


def test_cli_hands_the_command_its_stdin_and_environment(tmp_path: Path) -> None:
    program = tmp_path / "echo.vera"
    program.write_text(
        "public fn main(@Unit -> @Unit)\n"
        "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"
        "{\n"
        "  let @String = IO.read_line(());\n"
        "  IO.print(@String.0);\n"
        "  match IO.get_env(\"VERA_W24_PROBE\") {\n"
        "    Some(@String) -> IO.print(@String.0),\n"
        "    None -> IO.print(\"-\")\n"
        "  }\n"
        "}\n",
        encoding="utf-8",
    )
    ran = pipeline.cli("run", program, stdin="hello\n",
                       env={"VERA_W24_PROBE": "!"})
    assert (ran.returncode, ran.stdout) == (0, "hello!\n"), ran.stderr


# =====================================================================
# What a stage takes
# =====================================================================


def test_source_text_is_checked_as_the_file_it_came_from() -> None:
    text = _FACTORIAL.read_text(encoding="utf-8")
    assert pipeline.verify(text, file=str(_FACTORIAL)).envelope() == (
        pipeline.verify(_FACTORIAL).envelope())
    assert pipeline.check(text).file is None


def test_a_path_resolves_its_imports_and_source_text_does_not() -> None:
    path = EXAMPLES / "modules.vera"
    assert pipeline.check(path).ok
    assert pipeline.check(path).modules
    text = pipeline.check(path.read_text(encoding="utf-8"), file=str(path))
    assert text.modules is None and not text.ok


def test_modules_given_replace_resolution(tmp_path: Path) -> None:
    entry = pipeline.write_tree(tmp_path, {
        "main.vera": (
            "import lib(twice);\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  twice(21)\n}\n"),
        "lib.vera": (
            "module lib;\n\n"
            "public fn twice(@Int -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  @Int.0 * 2\n}\n"),
    })
    resolved = pipeline.check(entry)
    assert resolved.ok and resolved.modules
    assert pipeline.run(entry).value == 42
    given = pipeline.run(entry.read_text(encoding="utf-8"),
                         modules=resolved.modules)
    assert given.value == 42


def test_compile_builds_the_module_vera_codegen_compile_builds() -> None:
    """The stage builds its own generator, to hand it back; the module it
    builds is the one the public function builds from the same tables."""
    path = EXAMPLES / "modules.vera"
    checked = pipeline.check(path, collect_module_artifacts=True)
    artifacts = checked.artifacts
    expected = codegen_compile(
        checked.program, source=checked.source, file=checked.file,
        resolved_modules=checked.resolved,
        expr_semantic_types=artifacts.expr_semantic_types,
        expr_target_types=artifacts.expr_target_types,
        module_artifacts=artifacts.module_artifacts,
    )
    built = pipeline.compile(path)
    assert built.generator is not None
    assert built.wat == expected.wat


_UNCHECKED = """fn helper(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(@Int.0)
}
"""


def test_an_unchecked_compile_builds_what_the_check_refuses() -> None:
    assert not pipeline.check(_UNCHECKED).ok
    refused = pipeline.compile(_UNCHECKED)
    assert not refused.ok and refused.generator is None
    with pytest.raises(pipeline.StageFailed, match="Missing visibility"):
        refused.result
    built = pipeline.compile(_UNCHECKED, checked=False)
    assert built.ok and built.checked is None
    assert pipeline.run(built, fn="f", args=[41]).value == 42
    assert pipeline.run(_UNCHECKED, fn="f", args=[41], checked=False).value == 42


# =====================================================================
# Reading what a stage did not make
# =====================================================================


_UNPARSED = "public fn f(@Int -> @Int) {"
_ILL_TYPED = """public fn f(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""
_TRAPS = """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = 0;
  10 / @Int.0
}
"""


def test_a_parse_error_is_a_result_and_reading_past_it_raises_it() -> None:
    checked = pipeline.check(_UNPARSED)
    assert not checked.ok
    assert [d.error_code for d in checked.errors] == ["E001"]
    with pytest.raises(ParseError):
        checked.program
    with pytest.raises(ParseError):
        pipeline.verify(_UNPARSED).result
    with pytest.raises(ParseError):
        pipeline.compile(_UNPARSED).result
    with pytest.raises(ParseError):
        pipeline.run(_UNPARSED).value


def test_a_refusing_check_stops_the_stages_after_it() -> None:
    verified = pipeline.verify(_ILL_TYPED)
    assert not verified.ok and not verified.ran
    with pytest.raises(pipeline.StageFailed, match="the check reported"):
        verified.result
    ran = pipeline.run(_ILL_TYPED, fn="f", args=[1])
    assert not ran.ok and ran.module is None and ran.returncode == 1
    with pytest.raises(pipeline.StageFailed):
        ran.value


def test_a_verify_past_the_check_verifies_what_the_check_refused() -> None:
    past = pipeline.verify(_ILL_TYPED, past_check=True)
    assert past.ran and not past.ok
    assert past.checked.errors
    assert past.result.obligations is not None
    assert pipeline.verify(_UNPARSED, past_check=True).ran is False


def test_a_compile_past_the_check_builds_what_the_check_refused() -> None:
    refused = pipeline.compile(_ILL_TYPED)
    assert refused.generator is None
    past = pipeline.compile(_ILL_TYPED, past_check=True)
    assert past.generator is not None
    assert past.checked is not None and past.checked.errors
    assert not past.ok
    assert "f" in past.result.exports


def test_a_trap_is_a_result_and_reading_the_value_raises_it() -> None:
    ran = pipeline.run(_TRAPS)
    assert not ran.ok and ran.returncode == 1
    assert ran.trap is not None and ran.trap.kind == "divide_by_zero"
    with pytest.raises(WasmTrapError):
        ran.value


def test_every_compile_holds_the_call_indirect_table_invariant() -> None:
    """#1185, asserted on every module the stage builds."""
    with pytest.raises(AssertionError, match="#1185"):
        pipeline.assert_no_orphan_call_indirect(
            "(module\n  (func $f\n    call_indirect (type 0)\n  )\n)")
    pipeline.assert_no_orphan_call_indirect(
        "(module\n  (table 1 funcref)\n  (func $f\n    call_indirect (type 0)\n  )\n)")
    pipeline.assert_no_orphan_call_indirect("(module\n  (table 1 funcref)\n)")


def test_stderr_is_captured_as_vera_run_captures_it(
    capsys: pytest.CaptureFixture[str],
) -> None:
    source = (
        "public fn main(@Unit -> @Unit)\n"
        "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"
        "{\n  IO.stderr(\"note\")\n}\n")
    assert pipeline.run(source).stderr == "note"
    assert capsys.readouterr().err == ""
    assert pipeline.run(source, capture_stderr=False).stderr == ""
    assert capsys.readouterr().err == "note"
