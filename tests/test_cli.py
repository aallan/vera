"""Tests for vera.cli — command-line interface."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from vera.cli import cmd_ast, cmd_check, cmd_compile, cmd_parse, cmd_run, cmd_verify

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
INCREMENT = str(EXAMPLES_DIR / "increment.vera")
FACTORIAL = str(EXAMPLES_DIR / "factorial.vera")
CLOSURES = str(EXAMPLES_DIR / "closures.vera")
HELLO_WORLD = str(EXAMPLES_DIR / "hello_world.vera")


# =====================================================================
# Helpers
# =====================================================================


def _bad_vera(tmp_path: Path, content: str) -> str:
    """Write a bad .vera file and return its path."""
    p = tmp_path / "bad.vera"
    p.write_text(content)
    return str(p)


def _type_error_source() -> str:
    """A .vera program that parses but fails type-checking."""
    return """\
fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""


def _syntax_error_source() -> str:
    """A .vera program that fails to parse."""
    return "fn broken(@@@ -> ???) {{"


# =====================================================================
# cmd_parse
# =====================================================================


class TestCmdParse:
    def test_valid_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_parse(INCREMENT)
        assert rc == 0
        out = capsys.readouterr().out
        assert len(out) > 0

    def test_missing_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_parse("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_parse(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0


# =====================================================================
# cmd_check
# =====================================================================


class TestCmdCheck:
    def test_clean_example(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_check(INCREMENT)
        assert rc == 0
        out = capsys.readouterr().out
        assert "OK:" in out

    def test_warning_only_example(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """closures.vera produces warnings but no errors."""
        rc = cmd_check(CLOSURES)
        assert rc == 0
        captured = capsys.readouterr()
        assert "OK:" in captured.out
        assert "warning" in captured.err.lower()

    def test_type_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_check(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    def test_missing_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_check("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_check(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    # -- JSON mode --

    def test_json_ok(self, capsys: pytest.CaptureFixture[str]) -> None:
        """Clean file produces JSON with ok: true."""
        rc = cmd_check(INCREMENT, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["diagnostics"] == []

    def test_json_with_warnings(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Warnings-only file has ok: true with warnings in JSON."""
        rc = cmd_check(CLOSURES, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["diagnostics"] == []
        assert len(data["warnings"]) > 0
        assert data["warnings"][0]["severity"] == "warning"

    def test_json_type_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Type error produces JSON with ok: false and diagnostics."""
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_check(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0
        diag = data["diagnostics"][0]
        assert diag["severity"] == "error"
        assert "location" in diag
        assert "description" in diag

    def test_json_missing_file(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Missing file in JSON mode still produces valid JSON."""
        rc = cmd_check("/nonexistent/file.vera", as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_json_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Syntax error in JSON mode produces valid JSON diagnostic."""
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_check(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0


# =====================================================================
# cmd_verify
# =====================================================================


class TestCmdVerify:
    def test_tier1_example(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """increment.vera has Tier 1 verifiable contracts."""
        rc = cmd_verify(INCREMENT)
        assert rc == 0
        captured = capsys.readouterr()
        assert "OK:" in captured.out
        assert "Verification:" in captured.out
        assert "verified (Tier 1)" in captured.out

    def test_tier3_example(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """factorial.vera has recursive contracts that fall to Tier 3."""
        rc = cmd_verify(FACTORIAL)
        assert rc == 0
        captured = capsys.readouterr()
        assert "OK:" in captured.out
        assert "runtime checks (Tier 3)" in captured.out

    def test_type_error_blocks_verify(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_verify(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    def test_missing_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_verify("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_verify(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    # -- JSON mode --

    def test_json_tier1(self, capsys: pytest.CaptureFixture[str]) -> None:
        """Tier 1 verified file produces JSON with verification summary."""
        rc = cmd_verify(INCREMENT, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["diagnostics"] == []
        assert "verification" in data
        v = data["verification"]
        assert v["tier1_verified"] > 0
        assert v["total"] > 0

    def test_json_tier3(self, capsys: pytest.CaptureFixture[str]) -> None:
        """Tier 3 file produces JSON with runtime check counts."""
        rc = cmd_verify(FACTORIAL, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        v = data["verification"]
        assert v["tier3_runtime"] > 0
        assert len(data["warnings"]) > 0

    def test_json_type_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Type error blocks verification and produces JSON diagnostic."""
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_verify(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_json_missing_file(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Missing file in JSON verify mode produces valid JSON."""
        rc = cmd_verify("/nonexistent/file.vera", as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False


# =====================================================================
# cmd_compile
# =====================================================================


class TestCmdCompile:
    def test_compile_wat(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """--wat prints WAT text to stdout."""
        rc = cmd_compile(HELLO_WORLD, wat=True)
        assert rc == 0
        out = capsys.readouterr().out
        assert "(module" in out
        assert "vera.print" in out

    def test_compile_binary(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Writes a .wasm binary to the specified output path."""
        out_path = str(tmp_path / "test.wasm")
        rc = cmd_compile(HELLO_WORLD, output=out_path)
        assert rc == 0
        captured = capsys.readouterr()
        assert "Compiled:" in captured.out
        assert Path(out_path).exists()
        assert len(Path(out_path).read_bytes()) > 0

    def test_compile_default_output(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Without -o, writes .wasm next to the .vera file."""
        # Copy hello_world.vera to tmp_path
        src = Path(HELLO_WORLD)
        dest = tmp_path / "hello_world.vera"
        dest.write_text(src.read_text())
        rc = cmd_compile(str(dest))
        assert rc == 0
        wasm = tmp_path / "hello_world.wasm"
        assert wasm.exists()

    def test_compile_json(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """JSON mode returns exports list."""
        rc = cmd_compile(HELLO_WORLD, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert "main" in data["exports"]

    def test_compile_missing_file(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        rc = cmd_compile("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_compile_type_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_compile(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0


# =====================================================================
# cmd_run
# =====================================================================


class TestCmdRun:
    def test_run_hello_world(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """vera run hello_world.vera prints Hello, World!"""
        rc = cmd_run(HELLO_WORLD)
        assert rc == 0
        out = capsys.readouterr().out
        assert "Hello, World!" in out

    def test_run_factorial(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """vera run factorial.vera --fn factorial -- 5 returns 120."""
        rc = cmd_run(FACTORIAL, fn_name="factorial", fn_args=[5])
        assert rc == 0
        out = capsys.readouterr().out
        assert "120" in out

    def test_run_json(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """JSON mode returns structured result."""
        rc = cmd_run(HELLO_WORLD, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["stdout"] == "Hello, World!"

    def test_run_json_with_value(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """JSON mode returns function return value."""
        rc = cmd_run(FACTORIAL, as_json=True, fn_name="factorial", fn_args=[5])
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["value"] == 120

    def test_run_missing_file(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        rc = cmd_run("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_run_type_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_run(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0


# =====================================================================
# cmd_ast
# =====================================================================


class TestCmdAst:
    def test_text_output(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_ast(INCREMENT)
        assert rc == 0
        out = capsys.readouterr().out
        assert len(out) > 0

    def test_json_output(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_ast(INCREMENT, as_json=True)
        assert rc == 0
        out = capsys.readouterr().out
        parsed = json.loads(out)
        assert isinstance(parsed, dict)

    def test_missing_file(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_ast("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_ast(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0


# =====================================================================
# main() — subprocess integration tests
# =====================================================================


class TestMain:
    def test_no_args(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Usage:" in result.stderr

    def test_one_arg_only(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Usage:" in result.stderr

    def test_unknown_command(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "bogus", "file.vera"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Unknown command" in result.stderr

    def test_dispatch_parse(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "parse", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert len(result.stdout) > 0

    def test_dispatch_check(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "OK:" in result.stdout

    def test_dispatch_typecheck_alias(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "typecheck", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "OK:" in result.stdout

    def test_dispatch_verify(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "OK:" in result.stdout
        assert "Verification:" in result.stdout

    def test_dispatch_ast(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "ast", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0

    def test_dispatch_ast_json(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "ast", "--json", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        parsed = json.loads(result.stdout)
        assert isinstance(parsed, dict)

    def test_dispatch_check_json(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", "--json", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is True

    def test_dispatch_verify_json(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", "--json", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is True
        assert "verification" in parsed

    def test_dispatch_compile_wat(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat", HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "(module" in result.stdout
        assert "vera.print" in result.stdout

    def test_dispatch_compile_json(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--json", HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is True
        assert "main" in parsed["exports"]

    def test_dispatch_run(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "Hello, World!" in result.stdout

    def test_dispatch_run_with_fn_and_args(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", FACTORIAL,
             "--fn", "factorial", "--", "5"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "120" in result.stdout

    def test_dispatch_run_json(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", "--json", HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is True
        assert parsed["stdout"] == "Hello, World!"
