#!/usr/bin/env python
"""Validate Vera's built wheel and source distribution contents."""

from __future__ import annotations

import configparser
from email.parser import Parser
from pathlib import Path
import sys
import tarfile
import tomllib
import zipfile


ROOT = Path(__file__).resolve().parent.parent


def _project_identity() -> tuple[str, str]:
    data = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))
    project = data["project"]
    return str(project["name"]), str(project["version"])


def _check_metadata(raw: bytes, name: str, version: str, source: str) -> None:
    metadata = Parser().parsestr(raw.decode("utf-8"))
    if metadata["Name"] != name:
        raise ValueError(f"{source}: Name is {metadata['Name']!r}, expected {name!r}")
    if metadata["Version"] != version:
        raise ValueError(
            f"{source}: Version is {metadata['Version']!r}, expected {version!r}"
        )


def _check_no_generated_files(names: set[str], source: str) -> None:
    bad = sorted(
        path
        for path in names
        if "/__pycache__/" in f"/{path}" or path.endswith((".pyc", ".pyo"))
    )
    if bad:
        raise ValueError(f"{source}: generated Python files included: {bad}")


def _check_wheel(path: Path, name: str, version: str) -> None:
    dist_info = f"{name}-{version}.dist-info"
    with zipfile.ZipFile(path) as archive:
        names = set(archive.namelist())
        required = {
            "vera/__init__.py",
            "vera/cli.py",
            "vera/grammar.lark",
            "vera/browser/harness.mjs",
            "vera/browser/runtime.mjs",
            f"{dist_info}/METADATA",
            f"{dist_info}/entry_points.txt",
            f"{dist_info}/RECORD",
        }
        missing = sorted(required - names)
        if missing:
            raise ValueError(f"{path.name}: required files missing: {missing}")
        if any(item.startswith("tests/") for item in names):
            raise ValueError(f"{path.name}: wheel must not include tests/")
        if not any(item == f"{dist_info}/licenses/LICENSE" for item in names):
            raise ValueError(f"{path.name}: packaged LICENSE is missing")
        _check_no_generated_files(names, path.name)
        _check_metadata(
            archive.read(f"{dist_info}/METADATA"), name, version, path.name
        )

        entry_points = configparser.ConfigParser()
        entry_points.read_string(
            archive.read(f"{dist_info}/entry_points.txt").decode("utf-8")
        )
        command = entry_points.get("console_scripts", "vera", fallback="")
        if command != "vera.cli:main":
            raise ValueError(
                f"{path.name}: vera console script is {command!r}, "
                "expected 'vera.cli:main'"
            )


def _check_sdist(path: Path, name: str, version: str) -> None:
    top = f"{name}-{version}"
    with tarfile.open(path, "r:gz") as archive:
        names = {member.name for member in archive.getmembers()}
        required = {
            f"{top}/LICENSE",
            f"{top}/PKG-INFO",
            f"{top}/PYPI_README.md",
            f"{top}/pyproject.toml",
            f"{top}/vera/grammar.lark",
            f"{top}/vera/browser/harness.mjs",
            f"{top}/vera/browser/runtime.mjs",
        }
        missing = sorted(required - names)
        if missing:
            raise ValueError(f"{path.name}: required files missing: {missing}")
        _check_no_generated_files(names, path.name)
        metadata_file = archive.extractfile(f"{top}/PKG-INFO")
        if metadata_file is None:
            raise ValueError(f"{path.name}: could not read PKG-INFO")
        _check_metadata(metadata_file.read(), name, version, path.name)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    dist_dir = Path(args[0]) if args else ROOT / "dist"
    name, version = _project_identity()
    wheel = dist_dir / f"{name}-{version}-py3-none-any.whl"
    sdist = dist_dir / f"{name}-{version}.tar.gz"

    missing = [str(path) for path in (wheel, sdist) if not path.is_file()]
    if missing:
        print(f"ERROR: expected distribution files are missing: {missing}", file=sys.stderr)
        return 1

    try:
        _check_wheel(wheel, name, version)
        _check_sdist(sdist, name, version)
    except (ValueError, OSError, tarfile.TarError, zipfile.BadZipFile) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print(f"Distribution archives for {name} {version} are complete.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
