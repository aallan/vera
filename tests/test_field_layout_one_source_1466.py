"""One layout table, proved behaviourally: widen it and every walk follows.

A constructed object's field layout is construction's contract with every
walk that reads one back — the `let`-destructure, the match sub-pattern
extraction, the nested tag check, the structural-eq field walk, the closure
env block, the registered `ConstructorLayout`, and the boundary guard's
tuple decomposition.  Each of those carried its own copy of the two width
tables, and the copies agreed, so nothing could tell them apart.

A STATIC scan (`tests/guard_emitter_scan.py`, driven by a cell in
`test_boundary_guard_correctness_1466.py`) says no copy remains.  That is a
tripwire, not a proof: it reads source, so a copy in a shape it does not
match is invisible to it, and it says nothing about whether the walks agree.

This file is the proof.  It WIDENS one scalar in the single table — `"i32"`
from 4 bytes to 8, with its alignment — and asserts that programs which
round-trip a value through each walk still print what they printed before.
The table is mutated in a SCRATCH COPY of the tree, so nothing in the real
checkout changes, and the programs are run through the CLI of that copy.

Measured, rather than assumed, at three revisions:

* at `c4fd37d5`, before the walks in `vera/wasm/data.py` and
  `vera/wasm/operators.py` were folded, TWO of the five walks are red —
  `match-sub-pattern` and `nested-constructor`.  That is the shape the
  PR #1478 reviewer measured:
  `match MkBox("hello", 77) { MkBox(@String, @Int) -> … }` printing 77000
  instead of 5077, the `@Int` read out of the `@String`'s length word;
* at `71c2e314` and after, all five are green;
* at the merge-base `7f9a9d85` the fixture ERRORS rather than passing,
  because the single table it widens does not exist there yet.  A cell that
  cannot find what it mutates says so.

Three of the five walks were green at `c4fd37d5` too, and the reason is
worth writing down rather than leaving as apparent coverage: the
`let`-destructure had already been folded, while the closure env block and
the structural-eq walk are SELF-consistent — each writes and reads by the
same code — and the registered `ConstructorLayout.field_offsets` is read by
every consumer for its widths and by none for its offsets.  So no round trip
can witness those folds, and what holds them is the static scan.  They are
kept as cells because a future reader of those offsets would make them
witnesses, and a cell that is vacuous for a stated reason is not a cell that
is vacuous for no reason.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

import vera

_TREE = Path(vera.__file__).resolve().parents[1]

#: One widening, applied to the ONE table.  `"i32"` is the interesting
#: scalar: it is the ADT pointer, the `Bool` / `Byte` width and the half of a
#: pair, so every walk meets it, and widening it moves every field behind an
#: i32 one.  A walk that agrees with the table follows; a walk with its own
#: copy reads where the field used to be.
_WIDENED = (
    ('"i32": 4, "i64": 8, "f64": 8, "i32_pair": 8, "unit": 0',
     '"i32": 8, "i64": 8, "f64": 8, "i32_pair": 8, "unit": 0'),
    ('"i32": 4, "i64": 8, "f64": 8, "i32_pair": 4, "unit": 1',
     '"i32": 8, "i64": 8, "f64": 8, "i32_pair": 8, "unit": 1'),
)

#: Each program round-trips values through one walk and prints a number that
#: depends on every field it reads, so a field read at the wrong offset
#: changes the output rather than merely trapping.
_ROUND_TRIPS: dict[str, str] = {
    # The match sub-pattern extraction, over a pair field followed by a
    # scalar one — the reviewer's shape.
    "match-sub-pattern": """private data Box {
  MkBox(String, Int)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkBox("hello", 77) {
    MkBox(@String, @Int) -> string_length(@String.0) * 1000 + @Int.0
  }
}
""",
    # The `let`-destructure, same layout, different walk.
    "let-destructure": """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@String, @Int> = Tuple("hello", 77);
  string_length(@String.0) * 1000 + @Int.0
}
""",
    # The nested tag check AND the nested extraction, one behind a pair.
    "nested-constructor": """private data Inner {
  MkInner(Int)
}

private data Outer {
  MkOuter(String, Inner)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match MkOuter("hello", MkInner(77)) {
    MkOuter(@String, MkInner(@Int)) ->
      string_length(@String.0) * 1000 + @Int.0
  }
}
""",
    # The closure env block: a pair capture followed by a scalar one, read
    # back inside the lifted body.
    "closure-env": """public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @String = "hello";
  let @Int = 77;
  apply_fn(
    fn(@Bool -> @Int) effects(pure) {
      string_length(@String.0) * 1000 + @Int.0
    },
    true)
}
""",
    # The structural-eq field walk, over the same shape.
    "structural-eq": """private data Box {
  MkBox(String, Int)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if MkBox("hello", 77) == MkBox("hello", 77) { 5077 } else { 0 }
}
""",
}

_EXPECTED = 5077


def _run(tree: Path, source: str, tmp: Path, name: str) -> str:
    path = tmp / f"{name}.vera"
    path.write_text(source, encoding="utf-8")
    env = dict(os.environ)
    env["PYTHONPATH"] = str(tree)
    proc = subprocess.run(
        [sys.executable, "-m", "vera.cli", "run", str(path)],
        capture_output=True, text=True, encoding="utf-8", check=False,
        env=env, cwd=str(tree), timeout=300,
    )
    return proc.stdout + proc.stderr


@pytest.fixture(scope="module")
def widened_tree(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """A copy of the compiler with ONE widened layout table."""
    dest = tmp_path_factory.mktemp("widened") / "vera"
    shutil.copytree(_TREE / "vera", dest / "vera")
    helpers = dest / "vera" / "wasm" / "helpers.py"
    text = helpers.read_text(encoding="utf-8")
    for old, new in _WIDENED:
        assert old in text, f"the layout table no longer reads {old!r}"
        text = text.replace(old, new, 1)
    helpers.write_text(text, encoding="utf-8")
    return dest


def test_the_unwidened_tree_prints_the_expected_value(tmp_path: Path) -> None:
    """The premise: every program prints 5077 as the compiler stands.

    Without this the widened readings below could agree for the trivial
    reason that the programs never worked.
    """
    for name, source in _ROUND_TRIPS.items():
        out = _run(_TREE, source, tmp_path, name)
        assert str(_EXPECTED) in out, f"{name} does not round-trip: {out[-400:]}"


@pytest.mark.parametrize("name", sorted(_ROUND_TRIPS))
def test_every_walk_follows_the_one_table(
    name: str, widened_tree: Path, tmp_path: Path,
) -> None:
    """Widen the table and every walk still agrees with construction.

    A walk with a copy of the widths reads the field where it used to be:
    the reviewer measured 77000 for the match sub-pattern, where the `@Int`
    was read out of the `@String`'s length word.  What this asserts is
    therefore not "it still works" but "construction and this reader moved
    TOGETHER" — the property one table buys and the scan cannot see.
    """
    out = _run(widened_tree, _ROUND_TRIPS[name], tmp_path, name)
    assert str(_EXPECTED) in out, (
        f"{name} disagrees with construction once the single layout table is "
        f"widened, so it is reading widths of its own:\n{out[-600:]}"
    )


def test_the_widening_actually_reaches_the_compiler(
    widened_tree: Path, tmp_path: Path,
) -> None:
    """And the mutant is live: the emitted WAT moves.

    A widening the copy did not receive would make every cell above pass for
    nothing, so this reads the artifact: the same program compiled by the
    widened tree lays its fields out differently.
    """
    source = _ROUND_TRIPS["match-sub-pattern"]
    path = tmp_path / "wat.vera"
    path.write_text(source, encoding="utf-8")

    def wat(tree: Path) -> str:
        env = dict(os.environ)
        env["PYTHONPATH"] = str(tree)
        return subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat", str(path)],
            capture_output=True, text=True, encoding="utf-8", check=False,
            env=env, cwd=str(tree), timeout=300,
        ).stdout

    plain, widened = wat(_TREE), wat(widened_tree)
    assert plain and widened, "one of the trees emitted no WAT at all"
    assert plain != widened, (
        "the widened copy emits the same module as the real tree, so the "
        "mutation never reached the compiler and every cell above is vacuous"
    )
    offsets = lambda t: sorted(set(re.findall(r"offset=(\d+)", t)))  # noqa: E731
    assert offsets(plain) != offsets(widened), (
        "the widened copy uses the same field offsets, so the table it was "
        "given is not the one the layout is computed from"
    )
