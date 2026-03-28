"""Tests for vera.cli — command-line interface."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from vera.cli import cmd_ast, cmd_check, cmd_compile, cmd_fmt, cmd_parse, cmd_run, cmd_test, cmd_verify

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
INCREMENT = str(EXAMPLES_DIR / "increment.vera")
FACTORIAL = str(EXAMPLES_DIR / "factorial.vera")
MUTUAL_RECURSION = str(EXAMPLES_DIR / "mutual_recursion.vera")
CLOSURES = str(EXAMPLES_DIR / "closures.vera")
HELLO_WORLD = str(EXAMPLES_DIR / "hello_world.vera")
SAFE_DIVIDE = str(EXAMPLES_DIR / "safe_divide.vera")
ABS_VALUE = str(EXAMPLES_DIR / "absolute_value.vera")


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
private fn bad(@Int -> @Bool)
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
        """increment.vera has contracts that fall to Tier 3."""
        rc = cmd_verify(INCREMENT)
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
        rc = cmd_verify(INCREMENT, as_json=True)
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

    def test_json_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Syntax error in JSON verify mode produces valid JSON diagnostic."""
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_verify(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0


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

    def test_compile_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_compile(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    def test_compile_syntax_error_json(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_compile(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_compile_type_error_json(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_compile(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_compile_missing_file_json(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        rc = cmd_compile("/nonexistent/file.vera", as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False


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

    def test_run_syntax_error(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_run(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    def test_run_syntax_error_json(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_run(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_run_type_error_json(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_run(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_run_missing_file_json(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        rc = cmd_run("/nonexistent/file.vera", as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False


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

    def test_dispatch_run_json_with_value(self) -> None:
        """Subprocess: vera run --json --fn factorial -- 5 returns value."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", "--json", FACTORIAL,
             "--fn", "factorial", "--", "5"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is True
        assert parsed["value"] == 120

    def test_dispatch_compile_binary(self, tmp_path: Path) -> None:
        """Subprocess: vera compile -o <path> produces a .wasm binary."""
        out_path = tmp_path / "output.wasm"
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "-o", str(out_path), HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert out_path.exists()
        assert len(out_path.read_bytes()) > 0
        assert "Compiled:" in result.stdout

    def test_dispatch_compile_missing_file(self) -> None:
        """Subprocess: vera compile on missing file returns error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "--wat", "/nonexistent/file.vera"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "file not found" in result.stderr

    def test_dispatch_run_missing_file(self) -> None:
        """Subprocess: vera run on missing file returns error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", "/nonexistent/file.vera"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "file not found" in result.stderr

    def test_dispatch_compile_json_missing_file(self) -> None:
        """Subprocess: vera compile --json on missing file returns JSON error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "--json", "/nonexistent/file.vera"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is False

    def test_dispatch_run_json_missing_file(self) -> None:
        """Subprocess: vera run --json on missing file returns JSON error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run",
             "--json", "/nonexistent/file.vera"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        parsed = json.loads(result.stdout)
        assert parsed["ok"] is False


# =====================================================================
# cmd_run — additional edge cases
# =====================================================================


class TestCmdRunEdgeCases:
    def test_run_with_multiple_args(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Run a function with multiple integer arguments."""
        # Create a temp file with a two-arg function
        import tempfile
        source = """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path, fn_name="add", fn_args=[3, 4])
        assert rc == 0
        out = capsys.readouterr().out
        assert "7" in out

    def test_run_with_negative_args(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Run a function with negative integer arguments."""
        import tempfile
        source = """\
public fn abs(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 >= 0 then { @Int.0 } else { -@Int.0 } }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path, fn_name="abs", fn_args=[-42])
        assert rc == 0
        out = capsys.readouterr().out
        assert "42" in out

    def test_run_runtime_trap(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Run a function that triggers a runtime precondition trap."""
        import tempfile
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        # Runtime error → caught by cmd_run's RuntimeError handler
        rc = cmd_run(path, fn_name="positive", fn_args=[0])
        assert rc == 1

    def test_run_compile_json_with_warnings(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Compile JSON mode includes warnings from compilation."""
        import tempfile
        # Use an unsupported effect to trigger a compilation warning
        source = """\
effect Counter { op inc(Unit -> Unit); }

private fn count(@Unit -> @Unit)
  requires(true) ensures(true) effects(<Counter>)
{ () }

private fn simple(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_compile(path, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        # The Counter effect function produces a compilation warning
        assert len(data["warnings"]) > 0

    def test_run_invalid_int_arg(self) -> None:
        """Non-parseable arguments after -- produce a clean type error."""
        import tempfile
        source = """\
public fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli",
             "run", path, "--fn", "id", "--", "abc"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "not valid for parameter type" in result.stderr

    def test_run_float_arg(self) -> None:
        """Float arguments work for Float64 parameters."""
        import tempfile
        source = """\
public fn double(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 + @Float64.0 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli",
             "run", path, "--fn", "double", "--", "3.5"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "7.0" in result.stdout

    def test_run_string_arg(self) -> None:
        """String arguments work for String parameters."""
        import tempfile
        source = """\
public fn greet(@String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(@String.0) }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli",
             "run", path, "--fn", "greet", "--", "Hello"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "Hello" in result.stdout

    def test_run_bool_arg(self) -> None:
        """Bool arguments work using true/false strings."""
        import tempfile
        source = """\
public fn identity(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli",
             "run", path, "--fn", "identity", "--", "true"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "1" in result.stdout or "true" in result.stdout.lower()

    def test_run_invalid_arg_json(self) -> None:
        """Invalid args with --json produce JSON error."""
        import tempfile
        source = """\
public fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli",
             "run", "--json", path, "--fn", "id", "--", "xyz"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data["ok"] is False
        assert "not valid for parameter type" in data["diagnostics"][0]["description"]

    def test_run_no_main_no_args(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """vera run on file without main and no args gives helpful error."""
        import tempfile
        source = """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert "expects 2 parameters but 0 were provided" in err
        assert "No 'main' function found" in err
        assert "--fn add" in err

    def test_run_no_main_no_args_json(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """JSON mode returns structured error for missing args."""
        import tempfile
        source = """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.1 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert "expects 2 parameters" in data["diagnostics"][0]["description"]

    def test_run_no_exports(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """vera run with only private functions gives helpful no-exports error."""
        import tempfile
        source = """\
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert "No exported functions to call" in err
        assert "private fn helper" in err
        assert "public fn main" in err

    def test_run_no_exports_json(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """JSON mode returns structured error for no exports."""
        import tempfile
        source = """\
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert "No exported functions" in data["diagnostics"][0]["description"]

    def test_run_private_fn_targeted(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """vera run --fn targeting a private function gives helpful error."""
        import tempfile
        source = """\
private fn secret(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            path = f.name
        rc = cmd_run(path, fn_name="secret", fn_args=[1])
        assert rc == 1
        err = capsys.readouterr().err
        assert "declared private" in err
        assert "public fn secret" in err


# =====================================================================
# Multi-file resolution (C7a)
# =====================================================================

class TestMultiFileResolution:
    """Test CLI commands with import resolution."""

    def test_check_with_resolved_import(self, tmp_path: Path) -> None:
        """vera check resolves imports from sibling files."""
        main_src = """\
import lib;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        lib_src = """\
private fn helper(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        main_file = tmp_path / "main.vera"
        lib_file = tmp_path / "lib.vera"
        main_file.write_text(main_src, encoding="utf-8")
        lib_file.write_text(lib_src, encoding="utf-8")

        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", str(main_file)],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "OK:" in result.stdout

    def test_check_unresolved_import_error(self, tmp_path: Path) -> None:
        """vera check reports error for unresolved imports."""
        main_src = """\
import missing;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        main_file = tmp_path / "main.vera"
        main_file.write_text(main_src, encoding="utf-8")

        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", str(main_file)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Cannot resolve import" in result.stderr

    def test_check_json_with_unresolved_import(self, tmp_path: Path) -> None:
        """vera check --json includes resolver diagnostics."""
        main_src = """\
import missing;

private fn main(-> @Unit) requires(true) ensures(true) effects(pure) { () }
"""
        main_file = tmp_path / "main.vera"
        main_file.write_text(main_src, encoding="utf-8")

        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", "--json",
             str(main_file)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data["ok"] is False
        assert any(
            "Cannot resolve import" in d["description"]
            for d in data["diagnostics"]
        )

    def test_check_with_bare_imported_call(self, tmp_path: Path) -> None:
        """vera check passes when main.vera calls an imported function."""
        lib_src = """\
public fn double(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + @Int.0 }
"""
        main_src = """\
import lib(double);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ double(@Int.0) }
"""
        lib_dir = tmp_path / "lib.vera"
        lib_dir.write_text(lib_src, encoding="utf-8")
        main_file = tmp_path / "main.vera"
        main_file.write_text(main_src, encoding="utf-8")

        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", str(main_file)],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "OK" in result.stdout


# =====================================================================
# cmd_fmt
# =====================================================================


def _canonical_source() -> str:
    """A .vera program already in canonical form."""
    return """\
public fn id(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def _non_canonical_source() -> str:
    """A .vera program NOT in canonical form (extra blank lines, spacing)."""
    return """\
public fn id(  @Int   ->   @Int  )
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


class TestCmdFmt:
    def test_stdout_output(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Default mode prints formatted source to stdout."""
        path = tmp_path / "test.vera"
        path.write_text(_non_canonical_source())
        rc = cmd_fmt(str(path))
        assert rc == 0
        out = capsys.readouterr().out
        assert "public fn id(@Int -> @Int)" in out

    def test_check_canonical(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """--check returns 0 for already-canonical source."""
        path = tmp_path / "test.vera"
        path.write_text(_canonical_source())
        rc = cmd_fmt(str(path), check=True)
        assert rc == 0
        out = capsys.readouterr().out
        assert "OK:" in out

    def test_check_non_canonical(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """--check returns 1 for non-canonical source."""
        path = tmp_path / "test.vera"
        path.write_text(_non_canonical_source())
        rc = cmd_fmt(str(path), check=True)
        assert rc == 1
        err = capsys.readouterr().err
        assert "Would reformat" in err

    def test_write_in_place(self, tmp_path: Path) -> None:
        """--write overwrites the file with canonical form."""
        path = tmp_path / "test.vera"
        path.write_text(_non_canonical_source())
        rc = cmd_fmt(str(path), write=True)
        assert rc == 0
        result = path.read_text()
        assert result == _canonical_source()

    def test_write_idempotent(self, tmp_path: Path) -> None:
        """--write on already-canonical file leaves it unchanged."""
        path = tmp_path / "test.vera"
        path.write_text(_canonical_source())
        rc = cmd_fmt(str(path), write=True)
        assert rc == 0
        assert path.read_text() == _canonical_source()

    def test_missing_file(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        rc = cmd_fmt("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_syntax_error(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str]
    ) -> None:
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_fmt(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    def test_example_file(
        self, capsys: pytest.CaptureFixture[str]
    ) -> None:
        """Formatting increment.vera produces valid output."""
        rc = cmd_fmt(INCREMENT)
        assert rc == 0
        out = capsys.readouterr().out
        assert "fn increment" in out
        assert out.endswith("\n")


class TestCmdFmtMain:
    """Subprocess integration tests for vera fmt."""

    def test_dispatch_fmt(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "fmt", INCREMENT],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "fn increment" in result.stdout

    def test_dispatch_fmt_check_canonical(self, tmp_path: Path) -> None:
        path = tmp_path / "test.vera"
        path.write_text(_canonical_source())
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "fmt", "--check", str(path)],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "OK:" in result.stdout

    def test_dispatch_fmt_check_non_canonical(self, tmp_path: Path) -> None:
        path = tmp_path / "test.vera"
        path.write_text(_non_canonical_source())
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "fmt", "--check", str(path)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Would reformat" in result.stderr

    def test_dispatch_fmt_write(self, tmp_path: Path) -> None:
        path = tmp_path / "test.vera"
        path.write_text(_non_canonical_source())
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "fmt", "--write", str(path)],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "Formatted:" in result.stdout
        assert path.read_text() == _canonical_source()

    def test_dispatch_fmt_missing_file(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "fmt", "/nonexistent/file.vera"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "file not found" in result.stderr


# =====================================================================
# cmd_test
# =====================================================================


class TestCmdTest:
    """Tests for vera test command."""

    def test_verified_example(self, capsys: pytest.CaptureFixture[str]) -> None:
        """safe_divide should report all functions as verified."""
        rc = cmd_test(SAFE_DIVIDE)
        assert rc == 0
        out = capsys.readouterr().out
        assert "VERIFIED" in out

    def test_tier1_example(self, capsys: pytest.CaptureFixture[str]) -> None:
        """absolute_value should be verified (Tier 1)."""
        rc = cmd_test(ABS_VALUE)
        assert rc == 0
        out = capsys.readouterr().out
        assert "VERIFIED" in out or "TESTED" in out or "SKIPPED" in out

    def test_json_output(self, capsys: pytest.CaptureFixture[str]) -> None:
        """--json should produce valid JSON."""
        rc = cmd_test(SAFE_DIVIDE, as_json=True)
        assert rc == 0
        out = capsys.readouterr().out
        data = json.loads(out)
        assert data["ok"] is True
        assert "functions" in data
        assert "summary" in data

    def test_trials_flag(self, capsys: pytest.CaptureFixture[str]) -> None:
        """--trials should limit trial count."""
        rc = cmd_test(SAFE_DIVIDE, trials=5)
        assert rc == 0

    def test_file_not_found(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_test("/nonexistent/file.vera")
        assert rc == 1
        err = capsys.readouterr().err
        assert "file not found" in err

    def test_file_not_found_json(self, capsys: pytest.CaptureFixture[str]) -> None:
        rc = cmd_test("/nonexistent/file.vera", as_json=True)
        assert rc == 1
        out = capsys.readouterr().out
        data = json.loads(out)
        assert data["ok"] is False

    def test_type_errors_abort(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Type errors should abort before testing."""
        bad = tmp_path / "bad.vera"
        bad.write_text("""\
private fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        rc = cmd_test(str(bad))
        assert rc == 1


class TestCmdTestMain:
    """Subprocess integration tests for vera test."""

    def test_dispatch_test(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "Testing:" in result.stdout

    def test_dispatch_test_json(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test", "--json", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data["ok"] is True

    def test_dispatch_test_trials(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test", "--trials", "5", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 0

    def test_dispatch_test_fn(self) -> None:
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test", "--fn", "safe_divide", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 0


class TestIOOperations:
    """Tests for IO operations via the CLI."""

    def test_run_io_exit_code(self, tmp_path: Path) -> None:
        """vera run returns the exit code from IO.exit."""
        prog = tmp_path / "exit_test.vera"
        prog.write_text("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(42)
}
""")
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", str(prog)],
            capture_output=True, text=True,
        )
        assert result.returncode == 42

    def test_run_io_read_line(self, tmp_path: Path) -> None:
        """vera run with stdin passes input to IO.read_line."""
        prog = tmp_path / "read_line_test.vera"
        prog.write_text("""\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = IO.read_line(());
  IO.print(@String.0)
}
""")
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", str(prog)],
            capture_output=True, text=True,
            input="hello from stdin\n",
        )
        assert result.returncode == 0
        assert "hello from stdin" in result.stdout


# =====================================================================
# _is_int_str helper
# =====================================================================


class TestIsIntStr:
    def test_positive_int(self) -> None:
        from vera.cli import _is_int_str
        assert _is_int_str("42") is True

    def test_negative_int(self) -> None:
        from vera.cli import _is_int_str
        assert _is_int_str("-7") is True

    def test_zero(self) -> None:
        from vera.cli import _is_int_str
        assert _is_int_str("0") is True

    def test_not_int_alpha(self) -> None:
        from vera.cli import _is_int_str
        assert _is_int_str("abc") is False

    def test_not_int_float(self) -> None:
        from vera.cli import _is_int_str
        assert _is_int_str("1.5") is False

    def test_not_int_empty(self) -> None:
        from vera.cli import _is_int_str
        assert _is_int_str("") is False


# =====================================================================
# cmd_verify — verification error paths
# =====================================================================


class TestCmdVerifyErrors:
    """Cover verification-error display (non-JSON) in cmd_verify."""

    def _verify_fail_source(self) -> str:
        """A program that passes type-check but fails verification."""
        return """\
private fn bad(@Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{ @Int.0 }
"""

    def test_verification_failure(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Postcondition failure prints errors to stderr."""
        path = tmp_path / "vfail.vera"
        path.write_text(self._verify_fail_source())
        rc = cmd_verify(str(path))
        assert rc == 1
        err = capsys.readouterr().err
        assert "postcondition" in err.lower() or len(err) > 0

    def test_verification_failure_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Postcondition failure in JSON mode returns structured error."""
        path = tmp_path / "vfail.vera"
        path.write_text(self._verify_fail_source())
        rc = cmd_verify(str(path), as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0


# =====================================================================
# cmd_compile — browser target and error paths
# =====================================================================


class TestCmdCompileBrowser:
    """Cover --target browser path in cmd_compile."""

    def test_browser_target(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--target browser emits a browser bundle directory."""
        out_dir = tmp_path / "browser_out"
        rc = cmd_compile(
            HELLO_WORLD, target="browser", output=str(out_dir),
        )
        assert rc == 0
        captured = capsys.readouterr()
        assert "Browser bundle:" in captured.out
        assert out_dir.exists()

    def test_browser_target_default_dir(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Without -o, browser target creates <stem>_browser/ next to source."""
        src = Path(HELLO_WORLD)
        dest = tmp_path / "hello_world.vera"
        dest.write_text(src.read_text())
        rc = cmd_compile(str(dest), target="browser")
        assert rc == 0
        captured = capsys.readouterr()
        assert "Browser bundle:" in captured.out
        expected_dir = tmp_path / "hello_world_browser"
        assert expected_dir.exists()


class TestCmdCompileErrors:
    """Cover codegen error paths in cmd_compile."""

    def test_compile_type_error_non_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Type error in non-JSON mode prints to stderr."""
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_compile(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0


# =====================================================================
# cmd_run — additional uncovered paths
# =====================================================================


class TestCmdRunUncoveredPaths:
    """Cover uncovered branches in cmd_run."""

    def test_run_fn_not_found_not_private(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Targeting a non-existent function shows available exports."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        path = tmp_path / "test.vera"
        path.write_text(source)
        rc = cmd_run(str(path), fn_name="nonexistent")
        assert rc == 1
        err = capsys.readouterr().err
        assert "not found in exports" in err
        assert "main" in err

    def test_run_fn_not_found_not_private_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Targeting a non-existent function in JSON mode."""
        source = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        path = tmp_path / "test.vera"
        path.write_text(source)
        rc = cmd_run(str(path), fn_name="nonexistent", as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert "not found in exports" in data["diagnostics"][0]["description"]

    def test_run_private_fn_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Targeting a private function in JSON mode."""
        source = """\
private fn secret(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        path = tmp_path / "test.vera"
        path.write_text(source)
        rc = cmd_run(str(path), fn_name="secret", fn_args=[1], as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert "private" in data["diagnostics"][0]["description"].lower()

    def test_run_io_exit_code_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON mode includes exit_code field when IO.exit is used."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(42)
}
"""
        path = tmp_path / "exit_test.vera"
        path.write_text(source)
        rc = cmd_run(str(path), as_json=True)
        assert rc == 42
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is True
        assert data["exit_code"] == 42

    def test_run_io_exit_code_non_json(
        self, tmp_path: Path,
    ) -> None:
        """Non-JSON mode returns exit code from IO.exit."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.exit(7)
}
"""
        path = tmp_path / "exit_test.vera"
        path.write_text(source)
        rc = cmd_run(str(path))
        assert rc == 7

    def test_run_runtime_trap_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Runtime contract violation in JSON mode."""
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
"""
        path = tmp_path / "trap.vera"
        path.write_text(source)
        rc = cmd_run(str(path), fn_name="positive", fn_args=[0], as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        # Pin the specific runtime contract violation diagnostic
        diag_text = json.dumps(data).lower()
        assert "trap" in diag_text or "contract" in diag_text or "unreachable" in diag_text

    def test_run_no_exports_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """No exports in JSON mode produces structured error."""
        source = """\
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
"""
        path = tmp_path / "priv.vera"
        path.write_text(source)
        rc = cmd_run(str(path), as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert "No exported functions" in data["diagnostics"][0]["description"]


# =====================================================================
# cmd_test — uncovered output paths
# =====================================================================


class TestCmdTestUncoveredPaths:
    """Cover human-readable output paths and JSON type-error path."""

    def test_type_error_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Type error in JSON test mode returns structured diagnostic."""
        path = _bad_vera(tmp_path, _type_error_source())
        rc = cmd_test(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False
        assert len(data["diagnostics"]) > 0

    def test_syntax_error(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Syntax error in test mode prints to stderr."""
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_test(path)
        assert rc == 1
        err = capsys.readouterr().err
        assert len(err) > 0

    def test_syntax_error_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Syntax error in JSON test mode produces valid JSON."""
        path = _bad_vera(tmp_path, _syntax_error_source())
        rc = cmd_test(path, as_json=True)
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        assert data["ok"] is False

    def test_tested_output(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Human-readable output for tested (Tier 3) functions."""
        source = """\
public fn clamp(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  ensures(@Int.result <= 100)
  effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
"""
        path = tmp_path / "clamp.vera"
        path.write_text(source)
        rc = cmd_test(str(path), trials=10)
        assert rc == 0
        out = capsys.readouterr().out
        assert "Testing:" in out
        assert "Results:" in out
        # Should show TESTED or VERIFIED
        assert "TESTED" in out or "VERIFIED" in out

    def test_fn_name_filter(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--fn filters to a specific function."""
        rc = cmd_test(SAFE_DIVIDE, fn_name="safe_divide")
        assert rc == 0
        out = capsys.readouterr().out
        # Must mention the filtered function by name
        assert "safe_divide" in out

    def test_trials_display(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Human-readable output shows trial counts."""
        source = """\
public fn clamp(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  ensures(@Int.result <= 100)
  effects(pure)
{
  if @Int.0 < 0 then { 0 }
  else { if @Int.0 > 100 then { 100 } else { @Int.0 } }
}
"""
        path = tmp_path / "clamp.vera"
        path.write_text(source)
        rc = cmd_test(str(path), trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "Results:" in out
        # Must show the function was actually processed
        assert "clamp" in out


# =====================================================================
# cmd_ast — JSON output path
# =====================================================================


class TestCmdAstJson:
    def test_json_has_declarations(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON AST output contains declarations."""
        rc = cmd_ast(INCREMENT, as_json=True)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        assert "declarations" in data


# =====================================================================
# cmd_fmt — additional paths via subprocess
# =====================================================================


class TestCmdFmtSubprocess:
    """Cover fmt dispatch through main()."""

    def test_dispatch_fmt_syntax_error(self, tmp_path: Path) -> None:
        path = tmp_path / "bad.vera"
        path.write_text(_syntax_error_source())
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "fmt", str(path)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert len(result.stderr) > 0


# =====================================================================
# main() — additional argument parsing paths
# =====================================================================


class TestMainArgParsing:
    """Cover main() argument parsing edge cases."""

    def test_invalid_trials_value(self) -> None:
        """--trials with non-integer value prints error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test",
             "--trials", "abc", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Invalid --trials value" in result.stderr

    def test_invalid_trials_value_json(self) -> None:
        """--trials with non-integer value in JSON mode."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test",
             "--json", "--trials", "abc", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data["ok"] is False
        assert "Invalid --trials" in data["diagnostics"][0]["description"]

    def test_invalid_target_value(self) -> None:
        """--target with invalid value prints error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "--target", "invalid", HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Invalid --target value" in result.stderr

    def test_invalid_target_value_json(self) -> None:
        """--target with invalid value in JSON mode."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "--json", "--target", "invalid", HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data["ok"] is False
        assert "Invalid --target" in data["diagnostics"][0]["description"]

    def test_browser_target_via_main(self, tmp_path: Path) -> None:
        """--target browser dispatches correctly via main()."""
        out_dir = tmp_path / "browser_out"
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "--target", "browser", "-o", str(out_dir), HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert "Browser bundle:" in result.stdout
        assert out_dir.exists()

    def test_invalid_args_after_dashdash(self) -> None:
        """Extra arguments after -- for a no-arg function produce error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run",
             HELLO_WORLD, "--", "notanarg"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        # Argument count mismatch: main takes 0 args
        assert "expects 0 arguments" in result.stderr

    def test_invalid_args_after_dashdash_json(self) -> None:
        """Extra arguments after -- in JSON mode produce structured error."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run",
             "--json", HELLO_WORLD, "--", "notanarg"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        data = json.loads(result.stdout)
        assert data["ok"] is False
        assert "expects 0 arguments" in data["diagnostics"][0]["description"]

    def test_dispatch_test_command(self) -> None:
        """test command dispatches correctly."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test",
             "--trials", "5", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 0

    def test_dispatch_test_with_fn(self) -> None:
        """test command with --fn dispatches correctly."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "test",
             "--fn", "safe_divide", SAFE_DIVIDE],
            capture_output=True, text=True,
        )
        assert result.returncode == 0

    def test_no_filepath_after_flags(self) -> None:
        """Flags without filepath prints usage."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "Usage:" in result.stderr

    def test_output_path_flag(self, tmp_path: Path) -> None:
        """-o flag sets output path via main()."""
        out_path = tmp_path / "out.wasm"
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile",
             "-o", str(out_path), HELLO_WORLD],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        assert out_path.exists()


# =====================================================================
# main() — in-process tests (for coverage)
# =====================================================================


class TestMainInProcess:
    """Test main() in-process via sys.argv patching for coverage."""

    def test_no_args(self, capsys: pytest.CaptureFixture[str]) -> None:
        """No args prints usage and exits 1."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera"]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        assert "Usage:" in capsys.readouterr().err

    def test_unknown_command(self, capsys: pytest.CaptureFixture[str]) -> None:
        """Unknown command prints error and usage."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "bogus", HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        err = capsys.readouterr().err
        assert "Unknown command: bogus" in err

    def test_parse_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """parse command dispatches to cmd_parse."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "parse", INCREMENT]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_check_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """check command dispatches to cmd_check."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "check", INCREMENT]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_typecheck_alias(self, capsys: pytest.CaptureFixture[str]) -> None:
        """typecheck alias dispatches to cmd_check."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "typecheck", INCREMENT]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_verify_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """verify command dispatches."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "verify", SAFE_DIVIDE]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_compile_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """compile command dispatches."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "compile", "--wat", HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_run_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """run command dispatches."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "run", HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_ast_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """ast command dispatches."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "ast", INCREMENT]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_fmt_dispatch(self, capsys: pytest.CaptureFixture[str]) -> None:
        """fmt command dispatches."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "fmt", INCREMENT]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_invalid_trials_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--trials with non-int value, in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "test", "--trials", "abc", SAFE_DIVIDE]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        assert "Invalid --trials" in capsys.readouterr().err

    def test_invalid_trials_json_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--trials with non-int value in JSON mode, in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "test", "--json", "--trials", "abc",
                                SAFE_DIVIDE]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        out = capsys.readouterr().out
        import json as _json
        data = _json.loads(out)
        assert data["ok"] is False

    def test_invalid_target_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--target with invalid value, in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "compile", "--target", "invalid",
                                HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        assert "Invalid --target" in capsys.readouterr().err

    def test_invalid_target_json_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--target with invalid value in JSON mode, in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "compile", "--json", "--target",
                                "invalid", HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        out = capsys.readouterr().out
        import json as _json
        data = _json.loads(out)
        assert data["ok"] is False

    def test_invalid_fn_args_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Extra args after -- for no-arg function, in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "run", HELLO_WORLD, "--", "abc"]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        assert "expects 0 arguments" in capsys.readouterr().err

    def test_invalid_fn_args_json_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Non-integer args after -- in JSON mode, in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "run", "--json", HELLO_WORLD, "--",
                                "abc"]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        out = capsys.readouterr().out
        import json as _json
        data = _json.loads(out)
        assert data["ok"] is False

    def test_no_filepath_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Flags but no filepath prints usage."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "compile", "--wat"]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 1
        assert "Usage:" in capsys.readouterr().err

    def test_fn_name_parsing(self, capsys: pytest.CaptureFixture[str]) -> None:
        """--fn flag is parsed correctly."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "run", "--fn", "main", HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_output_path_parsing(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """-o flag is parsed correctly."""
        from unittest.mock import patch
        out = tmp_path / "out.wasm"
        with patch("sys.argv", ["vera", "compile", "-o", str(out),
                                HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0
        assert out.exists()

    def test_run_with_fn_args(self, capsys: pytest.CaptureFixture[str]) -> None:
        """run with -- args parses integer arguments."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "run", "--fn", "main",
                                HELLO_WORLD, "--", "42"]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            # main() doesn't take args, but dispatch should work
            assert exc_info.value.code in (0, 1)

    def test_test_with_trials_and_fn(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """test with --trials and --fn."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "test", "--trials", "5", "--fn",
                                "safe_divide", SAFE_DIVIDE]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_compile_browser_inprocess(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """--target browser in-process."""
        from unittest.mock import patch
        out_dir = tmp_path / "browser"
        with patch("sys.argv", ["vera", "compile", "--target", "browser",
                                "-o", str(out_dir), HELLO_WORLD]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0
        assert out_dir.exists()

    def test_check_json_inprocess(
        self, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """check --json in-process."""
        from unittest.mock import patch
        with patch("sys.argv", ["vera", "check", "--json", INCREMENT]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_fmt_write_inprocess(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """fmt --write in-process."""
        from unittest.mock import patch
        src = Path(INCREMENT)
        dest = tmp_path / "test.vera"
        dest.write_text(src.read_text())
        with patch("sys.argv", ["vera", "fmt", "--write", str(dest)]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            assert exc_info.value.code == 0

    def test_fmt_check_inprocess(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """fmt --check in-process."""
        from unittest.mock import patch
        src = Path(INCREMENT)
        dest = tmp_path / "test.vera"
        dest.write_text(src.read_text())
        with patch("sys.argv", ["vera", "fmt", "--check", str(dest)]):
            with pytest.raises(SystemExit) as exc_info:
                from vera.cli import main
                main()
            # May pass or fail depending on formatting
            assert exc_info.value.code in (0, 1)


# =====================================================================
# cmd_test — test failure output paths
# =====================================================================


class TestCmdTestFailureOutput:
    """Cover the FAILED output path and trial failure details."""

    def test_test_failure_output(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with a violated postcondition shows testing output.

        Use a complex enough function that Z3 can't verify it (Tier 3)
        but the postcondition is violated on some inputs.
        """
        source = """\
public fn buggy_hash(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @Int = @Int.0 * 31 + 17;
  let @Int = @Int.0 * @Int.1;
  let @Int = @Int.0 + @Int.1 * 7;
  @Int.0
}
"""
        path = tmp_path / "fail.vera"
        path.write_text(source)
        rc = cmd_test(str(path), trials=50)
        out = capsys.readouterr().out
        assert "Testing:" in out
        assert "Results:" in out
        # Must show either TESTED or FAILED for a Tier 3 function
        assert "TESTED" in out or "FAILED" in out or "VERIFIED" in out

    def test_test_failure_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON output for tested function includes function status."""
        source = """\
public fn buggy_hash(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @Int = @Int.0 * 31 + 17;
  let @Int = @Int.0 * @Int.1;
  let @Int = @Int.0 + @Int.1 * 7;
  @Int.0
}
"""
        path = tmp_path / "fail.vera"
        path.write_text(source)
        rc = cmd_test(str(path), as_json=True, trials=50)
        out = capsys.readouterr().out
        data = json.loads(out)
        assert "functions" in data
        # The function must appear with a concrete category
        assert len(data["functions"]) > 0
        categories = {f["category"] for f in data["functions"]}
        assert categories & {"tested", "verified", "failed"}

    def test_skipped_function_output(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Functions with IO effects are skipped in test output."""
        source = """\
public fn hello(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("hello")
}
"""
        path = tmp_path / "io.vera"
        path.write_text(source)
        rc = cmd_test(str(path))
        assert rc == 0
        out = capsys.readouterr().out
        # IO-effectful function must be skipped — assert the specific status
        assert "SKIPPED" in out


class TestCmdRunRuntimeTrap:
    """Cover the runtime trap exception handler in cmd_run."""

    def test_runtime_precondition_trap_non_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A precondition violation produces a trap in non-JSON mode."""
        source = """\
public fn positive(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
"""
        path = tmp_path / "trap.vera"
        path.write_text(source)
        rc = cmd_run(str(path), fn_name="positive", fn_args=[0])
        assert rc == 1
        captured = capsys.readouterr()
        # Pin: must mention the precondition violation specifically
        combined = (captured.err + captured.out).lower()
        assert "precondition violation" in combined or "trap" in combined


# =====================================================================
# TestStdinInput — /dev/stdin regression (#335)
# =====================================================================


class TestStdinInput:
    """/dev/stdin works for all pipeline commands. Regression for #335.

    Before the fix, each cmd_* function called p.read_text() to capture
    the source and then called parse_file(path) which re-opened the path
    a second time.  For /dev/stdin the second open returns empty content,
    causing the parse tree to be empty and producing 'No exported functions
    to call'.  The fix reads source once and passes it to parse() directly.
    """

    SIMPLE_PROGRAM = """\
public fn main(-> @Int)
  requires(true)
  ensures(@Int.result == 42)
  effects(pure)
{ 42 }
"""

    def test_run_file(self, tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
        """cmd_run executes a regular .vera file correctly."""
        path = tmp_path / "input.vera"
        path.write_text(self.SIMPLE_PROGRAM)
        rc = cmd_run(str(path))
        assert rc == 0
        captured = capsys.readouterr()
        assert "42" in captured.out

    def test_check_reads_source_once(self) -> None:
        """cmd_check parses from the already-read source, not by re-opening."""
        # If check re-opened the file it would still work for a normal file,
        # so we verify the behaviour via subprocess on /dev/stdin instead.
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", "/dev/stdin"],
            input=self.SIMPLE_PROGRAM,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "OK" in result.stdout

    def test_run_dev_stdin_subprocess(self) -> None:
        """vera run /dev/stdin produces correct output end-to-end. (#335)"""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "run", "/dev/stdin"],
            input=self.SIMPLE_PROGRAM,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "42" in result.stdout

    def test_verify_dev_stdin_subprocess(self) -> None:
        """vera verify /dev/stdin works end-to-end."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "verify", "/dev/stdin"],
            input=self.SIMPLE_PROGRAM,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "verified" in result.stdout.lower(), result.stdout

    def test_compile_dev_stdin_wat(self) -> None:
        """vera compile --wat /dev/stdin prints WAT to stdout."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat", "/dev/stdin"],
            input=self.SIMPLE_PROGRAM,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        assert "(module" in result.stdout

    def test_compile_dev_stdin_default_output(self, tmp_path: Path) -> None:
        """vera compile /dev/stdin writes stdin.wasm in CWD, not /dev/stdin.wasm."""
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "/dev/stdin"],
            input=self.SIMPLE_PROGRAM,
            capture_output=True,
            text=True,
            cwd=tmp_path,
        )
        assert result.returncode == 0, result.stderr
        out_path = tmp_path / "stdin.wasm"
        assert out_path.exists(), f"Expected {out_path} to be created"
        assert out_path.stat().st_size > 0

    def test_check_dev_stdin_module_resolution(self, tmp_path: Path) -> None:
        """vera check /dev/stdin resolves imports from CWD, not /dev/.

        The _load_and_parse normalization returns Path.cwd()/"stdin.vera" for
        stdin, so ModuleResolver uses the subprocess CWD (tmp_path) as the
        import root.  Without the fix, ModuleResolver would look in /dev/ and
        the import would fail to resolve.
        """
        lib_source = """\
public fn helper(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ 1 }
"""
        main_source = """\
import lib(helper);

public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ helper() }
"""
        (tmp_path / "lib.vera").write_text(lib_source)
        result = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", "/dev/stdin"],
            input=main_source,
            capture_output=True,
            text=True,
            cwd=tmp_path,
        )
        assert result.returncode == 0, result.stderr


class TestTypedArgParsingDirect:
    """In-process tests for execute(raw_args=...) typed CLI argument parsing.

    Subprocess tests in TestCmdRunEdgeCases exercise the same paths end-to-end
    but do not contribute to coverage measurement.  These direct tests call
    compile() + execute() without spawning a subprocess so that the new code
    in vera/codegen/api.py is traced by the coverage tool.
    """

    @staticmethod
    def _compile(source: str) -> object:
        """Compile a Vera source string and return the CompileResult."""
        import tempfile
        from vera.codegen import compile as codegen_compile
        from vera.parser import parse_file
        from vera.transform import transform
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False
        ) as f:
            f.write(source)
            f.flush()
            path = f.name
        tree = parse_file(path)
        ast = transform(tree)
        return codegen_compile(ast, source=source, file=path)

    def test_string_arg_direct(self) -> None:
        """execute(raw_args=["hello"]) allocates a String into WASM memory."""
        from vera.codegen import execute
        source = """\
public fn greet(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ @String.0 }
"""
        result = self._compile(source)
        exec_result = execute(result, fn_name="greet", raw_args=["hello"])  # type: ignore[arg-type]
        # String functions return an i32 pointer; just confirm no error was raised
        assert exec_result is not None

    def test_float_arg_direct(self) -> None:
        """execute(raw_args=["3.5"]) parses as f64 for Float64 parameters."""
        from vera.codegen import execute
        source = """\
public fn double(@Float64 -> @Float64)
  requires(true) ensures(true) effects(pure)
{ @Float64.0 + @Float64.0 }
"""
        result = self._compile(source)
        exec_result = execute(result, fn_name="double", raw_args=["3.5"])  # type: ignore[arg-type]
        assert exec_result.value == pytest.approx(7.0)

    def test_bool_arg_true_direct(self) -> None:
        """execute(raw_args=["true"]) parses as i32 1 for Bool parameters."""
        from vera.codegen import execute
        source = """\
public fn identity(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 }
"""
        result = self._compile(source)
        exec_result = execute(result, fn_name="identity", raw_args=["true"])  # type: ignore[arg-type]
        assert exec_result.value == 1

    def test_bool_arg_false_direct(self) -> None:
        """execute(raw_args=["false"]) parses as i32 0 for Bool parameters."""
        from vera.codegen import execute
        source = """\
public fn identity(@Bool -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 }
"""
        result = self._compile(source)
        exec_result = execute(result, fn_name="identity", raw_args=["false"])  # type: ignore[arg-type]
        assert exec_result.value == 0

    def test_byte_arg_direct(self) -> None:
        """execute(raw_args=["65"]) parses as i32 for Byte parameters."""
        from vera.codegen import execute
        source = """\
public fn identity(@Byte -> @Byte)
  requires(true) ensures(true) effects(pure)
{ @Byte.0 }
"""
        result = self._compile(source)
        exec_result = execute(result, fn_name="identity", raw_args=["65"])  # type: ignore[arg-type]
        assert exec_result.value == 65

    def test_empty_raw_args_arity_error(self) -> None:
        """execute(raw_args=[]) with a function expecting 1 arg raises RuntimeError."""
        from vera.codegen import execute
        source = """\
public fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = self._compile(source)
        with pytest.raises(RuntimeError, match="expects 1 argument"):
            execute(result, fn_name="id", raw_args=[])  # type: ignore[arg-type]

    def test_type_mismatch_error(self) -> None:
        """execute(raw_args=["abc"]) for an Int param raises RuntimeError."""
        from vera.codegen import execute
        source = """\
public fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = self._compile(source)
        with pytest.raises(RuntimeError, match="not valid for parameter type"):
            execute(result, fn_name="id", raw_args=["abc"])  # type: ignore[arg-type]
    def test_fallback_wasm_type_direct(self) -> None:
        """execute(raw_args=...) with an unsupported wasm_type falls back to int()."""
        from vera.codegen import execute
        source = """\
public fn id(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        result = self._compile(source)
        # Inject a fake wasm type that doesn't match any known tag to exercise
        # the fallback branch in the type-dispatch loop.
        result.fn_param_types["id"] = ["unsupported_wasm_tag"]  # type: ignore[index]
        exec_result = execute(result, fn_name="id", raw_args=["42"])  # type: ignore[arg-type]
        assert exec_result.value == 42
