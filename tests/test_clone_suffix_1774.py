"""A clone's suffix spells its type arguments as its signature does (#1774).

The clone-name display qualified a data type in a clone's suffix only where
two module owners of its name met, and did not count the entry file as an
owner, so a clone instantiated at an entry `Shape` and a module's `Shape`
was spelled `pair$Shape_JShape` beside a signature reading
`(@Shape, @la.Shape, @Int -> @Int)`.  A clone is named from its typed
instantiation, and its suffix qualifies a type exactly where the signature
does.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/binding.py", "vera/monomorphize.py"])

_LA = """\
module la;

public data Shape {
  Sq(Int)
}

public fn mk(@Int -> @Shape)
  requires(true)
  ensures(true)
  effects(pure)
{
  Sq(@Int.0)
}
"""

_MAIN = """\
import la(mk);

private data Shape {
  Circle(Int)
}

private forall<A, B> fn pair(@A, @B, @Int -> @Int)
  requires(true)
  ensures(@Int.result > @Int.0)
  effects(pure)
{
  @Int.0 - 1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pair(Circle(1), mk(2), 5)
}
"""


@pytest.mark.xfail(strict=True, reason="red at 94cef528: the typed program (#1679) flips it")
def test_repro_1774_suffix_qualifies_as_the_signature_does(tmp_path: Path) -> None:
    path = pipeline.write_tree(tmp_path, {"la.vera": _LA, "main.vera": _MAIN})
    result = pipeline.cli("run", str(path))
    assert result.returncode != 0
    assert ("Postcondition violation in pair$Shape_Jla.Shape"
            "(@Shape, @la.Shape, @Int -> @Int)") in result.stderr, result.stderr
    assert "in pair$Shape_Jla.Shape  (" in result.stderr, result.stderr
