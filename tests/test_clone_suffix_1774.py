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

pytestmark = pytest.mark.matrix(
    decides=["vera/binding.py", "vera/monomorphize.py", "vera/typed.py"])

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


def test_repro_1774_suffix_qualifies_as_the_signature_does(tmp_path: Path) -> None:
    path = pipeline.write_tree(tmp_path, {"la.vera": _LA, "main.vera": _MAIN})
    result = pipeline.cli("run", str(path))
    assert result.returncode != 0
    assert ("Postcondition violation in pair$Shape_Jla.Shape"
            "(@Shape, @la.Shape, @Int -> @Int)") in result.stderr, result.stderr
    assert "in pair$Shape_Jla.Shape  (" in result.stderr, result.stderr


#: A clone's name as code generation mangles it, and its spelling: a module
#: type is qualified where another type of its name meets it, the entry's
#: own (written bare, in the suffix or in the message) or a second module's,
#: and is bare where it is the only type of its name.
_SPELLINGS: dict[str, tuple[str, str]] = {
    "the entry's beside a module's": (
        "pair$Shape_Jmod_U24_la_U24_Shape", "pair$Shape_Jla.Shape"),
    "the entry's in the signature": (
        "f$mod_U24_la_U24_Shape(@Shape -> @Int)", "f$la.Shape(@Shape -> @Int)"),
    "a module's alone": ("epick$mod_U24_cm_U24_Shape", "epick$Shape"),
    "two modules'": ("two$mod_U24_la_U24_Shape_Jmod_U24_lb_U24_Shape",
                     "two$la.Shape_Jlb.Shape"),
    "a module's in a type argument": (
        "g$Box_Lmod_U24_la_U24_Shape_R", "g$Box_LShape_R"),
}


@pytest.mark.parametrize("name", list(_SPELLINGS))
def test_a_suffix_qualifies_a_type_where_another_of_its_name_meets_it(
        name: str) -> None:
    from vera.binding import display_clone_types

    text, shown = _SPELLINGS[name]
    assert display_clone_types(text) == (shown,)
