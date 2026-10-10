"""`vera.__version__` is the version `pyproject.toml` states, read once.

The version is written in one place, `[project].version`.  An installed
`veralang` carries it in its metadata, so `vera/__init__.py` reads it from
there; a source tree imported without an install (`PYTHONPATH` at a
checkout) has no metadata, so it reads the `pyproject.toml` beside the
package, and a tree with neither says so rather than guessing.  Each case
runs `vera/__init__.py` itself, with a version no other source could
supply.
"""

from __future__ import annotations

import importlib.metadata
import runpy
import shutil
from pathlib import Path

import pytest

import vera

INIT = Path(vera.__file__).resolve()


def _run_init(package_dir: Path) -> dict[str, object]:
    """Execute a copy of `vera/__init__.py` as `<package_dir>/__init__.py`."""
    package_dir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(INIT, package_dir / "__init__.py")
    return runpy.run_path(str(package_dir / "__init__.py"))


def _not_installed(name: str) -> str:
    raise importlib.metadata.PackageNotFoundError(name)


def test_an_installed_distribution_supplies_the_version(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    asked: list[str] = []

    def version(name: str) -> str:
        asked.append(name)
        return "9.8.7"

    monkeypatch.setattr(importlib.metadata, "version", version)
    names = _run_init(tmp_path / "vera")
    assert asked == ["veralang"]
    assert names["__version__"] == "9.8.7"
    assert names["version"] == "9.8.7"


def test_a_source_tree_without_an_install_reads_its_pyproject(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(importlib.metadata, "version", _not_installed)
    (tmp_path / "pyproject.toml").write_text(
        '[project]\nname = "veralang"\nversion = "7.6.5"\n', encoding="utf-8"
    )
    assert _run_init(tmp_path / "vera")["__version__"] == "7.6.5"


def test_neither_is_an_unknown_version_not_a_guess(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(importlib.metadata, "version", _not_installed)
    assert _run_init(tmp_path / "vera")["__version__"] == "0+unknown"


def test_the_package_states_no_version_of_its_own() -> None:
    """No literal version in `vera/__init__.py`: a second copy is what
    `scripts/check_version_sync.py` existed to hold in step."""
    source = INIT.read_text(encoding="utf-8")
    assert "__version__ = \"" not in source and "__version__ = '" not in source


def test_this_checkout_reports_its_own_version() -> None:
    """The dev install: the metadata `uv sync` or `pip install -e .` wrote
    is the one `vera` reports."""
    assert vera.__version__ == importlib.metadata.version("veralang")
