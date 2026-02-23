"""Tests for vera.cli — command-line interface."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from vera.cli import cmd_ast, cmd_check, cmd_parse, cmd_verify

EXAMPLES_DIR = Path(__file__).parent.parent / "examples"
INCREMENT = str(EXAMPLES_DIR / "increment.vera")
FACTORIAL = str(EXAMPLES_DIR / "factorial.vera")
CLOSURES = str(EXAMPLES_DIR / "closures.vera")


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
