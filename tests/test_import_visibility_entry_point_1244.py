"""#1244: one program, one verdict — whatever file `vera check` was given.

`mid.vera` imports only `cap` from `deep`; its body also calls `other`.
Checked directly, `mid` reported E200 (unresolved) — correct, §8.5.1: a
module's bodies resolve in the namespace ITS file declares and imports.
Checked as a dependency of `main`, the same program was accepted in
silence, because the importer only REGISTERED each module (harvesting what
it declares) and never checked its bodies at all.  The lenient verdict is
the dangerous one: it lets a module use names it never imported, and the
run then resolves them out of the importer's flat namespace.

The verifier has honoured the module-local rule regardless of entry point
since #1225, so a name that misses there missed loudly while the checker
stayed quiet.

The tests are written as EQUALITY between the two entry points rather
than as "the importer warns", because the property is agreement: a future
change that made the standalone verdict lenient would satisfy "no
disagreement" and must fail here on the standalone leg's own assertion.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from tests import pipeline

_DEEP = """
public fn cap(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  5
}

public fn other(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}
"""

# `mid` imports `cap` ONLY, and calls `other` as well.
_MID_LEAKY = """
import deep(cap);

public fn use_both(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  cap(@Int.0) + other(@Int.0)
}
"""

# The control: `mid` imports both, so nothing is out of scope anywhere.
_MID_HONEST = """
import deep(cap, other);

public fn use_both(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  cap(@Int.0) + other(@Int.0)
}
"""

_MAIN = """
import mid(use_both);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  use_both(1)
}
"""

# The residual from the issue: a module body whose TYPE error only a body
# check can see.  `deep::cap` returns `@Int`; `mid` binds it to `@Bool`.
_MID_TYPE_ERROR = """
import deep(cap);

public fn bad(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Bool = cap(@Int.0);
  @Int.0
}
"""


def _codes(path: Path) -> list[tuple[str, str, int]]:
    """(error code, basename of the file blamed, line) for every diagnostic
    the check stage's envelope reports."""
    payload = pipeline.check(path).envelope()
    return sorted(
        (d["error_code"], Path(d["location"]["file"]).name, d["location"]["line"])
        for d in payload["diagnostics"] + payload["warnings"]
    )


def _write(tmp_path: Path, files: dict[str, str]) -> None:
    for name, text in files.items():
        (tmp_path / name).write_text(text, encoding="utf-8")


def test_unimported_name_is_reported_from_either_entry_point(
    tmp_path: Path,
) -> None:
    """`mid`'s leaked `other` is reported whether `mid` or `main` is given."""
    _write(tmp_path, {
        "deep.vera": _DEEP, "mid.vera": _MID_LEAKY, "main.vera": _MAIN,
    })
    standalone = _codes(tmp_path / "mid.vera")
    assert ("E200", "mid.vera", 9) in standalone, standalone
    assert standalone == _codes(tmp_path / "main.vera"), (
        "same program, different verdict by entry point"
    )


def test_honest_module_stays_clean_from_either_entry_point(
    tmp_path: Path,
) -> None:
    """The control: importing the name it uses, `mid` is clean both ways.

    Green before the fix as well as after — it is what stops the new body
    check from being a blanket rejection of cross-module programs rather
    than the visibility rule it implements.
    """
    _write(tmp_path, {
        "deep.vera": _DEEP, "mid.vera": _MID_HONEST, "main.vera": _MAIN,
    })
    assert _codes(tmp_path / "mid.vera") == []
    assert _codes(tmp_path / "main.vera") == []


def test_module_type_error_reaches_the_importer(tmp_path: Path) -> None:
    """A type error in a module BODY is an importer's error too.

    The issue's second shape: a module binding an `@Int`-returning call to
    an `@Bool` slot checked clean through an importer, verified Tier-1, and
    failed at compile.  Registration cannot see it — only a body check can —
    so it is the same gap as the visibility one and closes with it.
    """
    _write(tmp_path, {
        "deep.vera": _DEEP,
        "mid.vera": _MID_TYPE_ERROR,
        "main.vera": _MAIN.replace("use_both(1)", "bad(1)").replace(
            "import mid(use_both);", "import mid(bad);"),
    })
    standalone = _codes(tmp_path / "mid.vera")
    assert standalone, "the module must be rejected standalone"
    assert all(f == "mid.vera" for _, f, _ in standalone), standalone
    assert _codes(tmp_path / "main.vera") == standalone


def test_each_module_is_reported_once(tmp_path: Path) -> None:
    """A module imported by two files is diagnosed once, not twice.

    The body check is memoised by module path across the nested checkers;
    without that, a diamond (`main` -> `left`/`right` -> `deep`) would
    report `deep`'s diagnostics once per path to it.
    """
    leaky_deep = _DEEP + """
public fn leaky(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nowhere(@Int.0)
}
"""
    side = """
import deep(cap);

public fn %s(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  cap(@Int.0)
}
"""
    _write(tmp_path, {
        "deep.vera": leaky_deep,
        "left.vera": side % "via_left",
        "right.vera": side % "via_right",
        "main.vera": """
import left(via_left);
import right(via_right);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  via_left(1) + via_right(2)
}
""",
    })
    codes = _codes(tmp_path / "main.vera")
    deep_hits = [c for c in codes if c[1] == "deep.vera"]
    assert len(deep_hits) == 1, codes


@pytest.mark.parametrize("entry", ["mid.vera", "main.vera"])
def test_import_cycle_still_terminates(tmp_path: Path, entry: str) -> None:
    """A cycle between two modules does not recurse in the body check."""
    _write(tmp_path, {
        "mid.vera": """
import cyc(ping);

public fn use_both(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  ping(@Int.0)
}
""",
        "cyc.vera": """
import mid(use_both);

public fn ping(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
""",
        "main.vera": _MAIN,
    })
    proc = pipeline.cli("check", "--json", str(tmp_path / entry))
    assert proc.returncode in (0, 1), proc.stderr
    json.loads(proc.stdout)
