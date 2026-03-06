"""Conformance test suite — spec-anchored feature validation.

Each test corresponds to a small .vera program in tests/conformance/ that
exercises one language feature.  The manifest (manifest.json) declares the
deepest pipeline stage each program must pass: parse, check, verify, or run.

This module is part of the full test suite and runs in CI alongside the
unit tests and example round-trip tests.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from vera.formatter import format_source
from vera.parser import parse_file

# ---------------------------------------------------------------------------
# Load manifest
# ---------------------------------------------------------------------------

CONFORMANCE_DIR = Path(__file__).parent / "conformance"
MANIFEST: list[dict] = json.loads(
    (CONFORMANCE_DIR / "manifest.json").read_text()
)

_LEVEL_ORDER = {"parse": 0, "check": 1, "verify": 2, "run": 3}


def _at_least(entry: dict, level: str) -> bool:
    """Return True if the entry's declared level is >= *level*."""
    return _LEVEL_ORDER.get(entry["level"], 0) >= _LEVEL_ORDER[level]


def _vera(*args: str) -> subprocess.CompletedProcess[str]:
    """Run a vera CLI command and return the completed process."""
    return subprocess.run(
        [sys.executable, "-m", "vera.cli", *args],
        capture_output=True,
        text=True,
    )


# ---------------------------------------------------------------------------
# Parametrised conformance tests
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("entry", MANIFEST, ids=lambda e: e["id"])
class TestConformance:
    """Conformance suite — one class, one test per pipeline stage."""

    def test_parse(self, entry: dict) -> None:
        """Every conformance program must parse without errors."""
        path = str(CONFORMANCE_DIR / entry["file"])
        tree = parse_file(path)
        assert tree is not None

    def test_check(self, entry: dict) -> None:
        """Programs at level check/verify/run must type-check cleanly."""
        if not _at_least(entry, "check"):
            pytest.skip("parse-only")
        path = str(CONFORMANCE_DIR / entry["file"])
        result = _vera("check", path)
        assert "OK:" in result.stdout, (
            f"Type-check failed for {entry['id']}:\n{result.stdout}\n{result.stderr}"
        )

    def test_verify(self, entry: dict) -> None:
        """Programs at level verify/run must verify contracts cleanly."""
        if not _at_least(entry, "verify"):
            pytest.skip(f"{entry['level']}-only")
        path = str(CONFORMANCE_DIR / entry["file"])
        result = _vera("verify", path)
        assert "OK:" in result.stdout, (
            f"Verification failed for {entry['id']}:\n{result.stdout}\n{result.stderr}"
        )

    def test_run(self, entry: dict) -> None:
        """Programs at level run must compile and execute successfully."""
        if not _at_least(entry, "run"):
            pytest.skip(f"{entry['level']}-only")
        path = str(CONFORMANCE_DIR / entry["file"])
        result = _vera("run", path)
        assert result.returncode == 0, (
            f"Execution failed for {entry['id']}:\n{result.stdout}\n{result.stderr}"
        )

    def test_format_idempotent(self, entry: dict) -> None:
        """Every conformance program must be in canonical format."""
        path = CONFORMANCE_DIR / entry["file"]
        source = path.read_text()
        formatted = format_source(source)
        assert formatted == source, (
            f"Not in canonical format: {entry['id']}\n"
            f"Run: vera fmt --write {path}"
        )
