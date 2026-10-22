"""The wheel-availability gate tells a Python without pip from a lost platform (#1743).

``scripts/check_wheel_availability.py`` asks ``python -m pip download`` for
a wheel of each runtime dependency on each supported platform, and reads a
failed download as a platform the dependency no longer has wheels for.  A
virtual environment ``uv sync`` creates holds no ``pip``, so every one of
the 36 downloads failed there with ``No module named pip``, and the gate
said a platform was lost.  The gate now checks for ``pip`` once, before the
matrix: without it, it names that cause, once, and stops with exit 2, which
no lost platform returns.
"""

from __future__ import annotations

import importlib.util
import os
import subprocess
import venv
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "check_wheel_availability.py"


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_wheel_availability", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


cwa = _load()

#: What the gate says when a download fails for a platform, which a Python
#: without pip must not be reported as.
_LOST_PLATFORM = "you have dropped a platform"


def _python_without_pip(where: Path) -> Path:
    """A virtual environment's interpreter, made without pip as ``uv`` makes one.

    It links to the interpreter, as ``python -m venv`` does off Windows: a
    copy of a relocatable build such as ``uv``'s looks for its library
    relative to itself, in a ``lib/`` the new environment does not hold."""
    venv.create(where, with_pip=False, clear=True, symlinks=os.name != "nt")
    return where / ("Scripts/python.exe" if os.name == "nt" else "bin/python")


def test_a_python_without_pip_names_the_cause_once(tmp_path: Path) -> None:
    """The gate under an interpreter with no pip module downloads nothing:
    one message names the missing pip, no cell is reported, the lost
    platform hint is not given, and the exit is 2."""
    python = _python_without_pip(tmp_path / "no-pip")
    env = {name: value for name, value in os.environ.items() if not name.startswith("PYTHON")}
    proc = subprocess.run(
        [str(python), str(SCRIPT)], capture_output=True, text=True, encoding="utf-8",
        errors="replace", cwd=ROOT, env=env, timeout=120, check=False,
    )
    output = proc.stdout + proc.stderr
    assert proc.returncode == 2, output
    lines = output.strip().splitlines()
    assert len(lines) == 1 and "has no pip module" in lines[0], output
    assert "✗" not in output and _LOST_PLATFORM not in output, output


def test_without_pip_no_download_is_attempted(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    """In process: the check comes before the matrix, so no cell runs."""
    calls: list[tuple[str, str, str]] = []
    monkeypatch.setattr(cwa, "pip_available", lambda: False)
    monkeypatch.setattr(cwa, "check_one", lambda *cell: calls.append(cell) or (True, ""))
    assert cwa.main() == 2
    assert calls == []
    assert _LOST_PLATFORM not in capsys.readouterr().out


def test_with_pip_every_cell_is_checked(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    """The nearest accepted neighbour: with pip there, the gate checks every
    dependency on every platform, and passes when each has a wheel."""
    calls: list[tuple[str, str, str]] = []
    monkeypatch.setattr(cwa, "pip_available", lambda: True)
    monkeypatch.setattr(cwa, "check_one", lambda *cell: calls.append(cell) or (True, ""))
    assert cwa.main() == 0
    assert len(calls) == len(cwa.runtime_deps()) * len(cwa.SUPPORTED)
    assert "OK — all" in capsys.readouterr().out


def test_with_pip_a_lost_wheel_is_still_a_lost_platform(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    """The gate's own finding is unchanged: a download that fails under a
    Python with pip is a platform the dependency has no wheel for, exit 1."""
    monkeypatch.setattr(cwa, "pip_available", lambda: True)
    monkeypatch.setattr(
        cwa, "check_one",
        lambda dep, platform_tag, python_version: (platform_tag != "win_amd64", "no matching distribution"),
    )
    assert cwa.main() == 1
    assert _LOST_PLATFORM in capsys.readouterr().out


def test_pip_available_reads_this_interpreter() -> None:
    """It answers for the interpreter the downloads run under, this one."""
    assert cwa.pip_available() is (importlib.util.find_spec("pip") is not None)
