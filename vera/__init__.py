"""Vera: a programming language designed for LLMs."""

import importlib.metadata as _metadata


def _read_version() -> str:
    """`[project].version`, the one place the version is written.

    An installed `veralang` carries it in its metadata.  A source tree
    imported without an install has none, so the `pyproject.toml` beside
    the package is read instead; with neither, the version is unknown.
    """
    try:
        return _metadata.version("veralang")
    except _metadata.PackageNotFoundError:
        pass
    import tomllib
    from pathlib import Path

    pyproject = Path(__file__).resolve().parent.parent / "pyproject.toml"
    try:
        project = tomllib.loads(pyproject.read_text(encoding="utf-8"))["project"]
        if project.get("name") == "veralang":
            return str(project["version"])
    except (OSError, KeyError, tomllib.TOMLDecodeError):
        pass
    return "0+unknown"


__version__ = _read_version()
version = __version__
