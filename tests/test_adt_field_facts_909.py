"""A fact about a value holds through a data type's field (#909).

A fact the verifier holds about a value (a callee's `ensures`, a refined
return type, a refined or `@Nat` parameter) is a fact about that value
wherever it goes.  Stored in a constructor field and read back by a `match`,
it is still the same value, so a postcondition resting on the fact is proved
at Tier 1.  #909 recorded the opposite as a limitation: the box-then-unbox
program fell to a runtime check.  The verifier proves it, and nothing pinned
that, so the limitation's rows could be removed and the behaviour lost again
with every gate green.

Each positive cell stores such a value and asserts the caller's `ensures`
is `verified`.  The controls keep a cell from passing for a reason other
than the fact: a postcondition stronger than the fact, a field that holds a
value no contract speaks of, the other field of a nested constructor (which
holds `-7`, so reading the wrong field cannot pass), and a box returned by a
callee whose contract is `ensures(true)` are each `violated` (E500) through
the same field read.

The issue reproduced the gap with a callee in another module as well, so two
cells call an imported `mag`, by its bare name and by its module's path, with
the stronger postcondition as their control.

A value the function did not build is another class: the `Nat` component of
an `@Tuple<Nat, Nat>` parameter read at `@Int` carries no `>= 0` (#1814).
"""

from __future__ import annotations

import textwrap
from pathlib import Path

import pytest

from tests.module_fixture_helpers import verify_multi_module
from tests.verifier_helpers import _verify

MAG = textwrap.dedent("""\
    private fn mag(@Int -> @Int)
      requires(true)
      ensures(@Int.result >= 0)
      effects(pure)
    {
      if @Int.0 < 0 then {
        0 - @Int.0
      } else {
        @Int.0
      }
    }
    """)

BOX = "private data Box { MkBox(Int) }\n"

POS = "type PosInt = { @Int | @Int.0 > 0 };\n"

NESTED = (
    "private data Pair { MkPair(Int, Int) }\n"
    "private data Outer { MkOuter(Pair) }\n"
)

#: The issue's reproduction, as filed.
REPRO = BOX + MAG + textwrap.dedent("""\
    public fn main(@Unit -> @Int)
      requires(true)
      ensures(@Int.result >= 0)
      effects(pure)
    {
      let @Box = MkBox(mag(-5));
      match @Box.0 {
        MkBox(@Int) -> @Int.0
      }
    }
    """)

#: The shapes a value reaches a field through, each read back in `f`.
SHAPES: dict[str, str] = {
    "a parameter boxed": BOX + MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Box = MkBox(mag(@Int.0));
          match @Box.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
    "a generic box at Int": "private data Box<T> { MkBox(T) }\n" + MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Box<Int> = MkBox(mag(@Int.0));
          match @Box<Int>.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
    "an Option": MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Option<Int> = Some(mag(@Int.0));
          match @Option<Int>.0 {
            Some(@Int) -> @Int.0,
            None -> 0
          }
        }
        """),
    # The second field is negative, so the cell passes only where the arm
    # reads the first: `@Int.1`, the binding before the most recent.
    "a nested constructor": NESTED + MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Outer = MkOuter(MkPair(mag(@Int.0), -7));
          match @Outer.0 {
            MkOuter(MkPair(@Int, @Int)) -> @Int.1
          }
        }
        """),
    "a constructor in each arm of an if": MAG + textwrap.dedent("""\
        public fn f(@Int, @Bool -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Option<Int> = if @Bool.0 then {
            Some(mag(@Int.0))
          } else {
            None
          };
          match @Option<Int>.0 {
            Some(@Int) -> @Int.0,
            None -> 0
          }
        }
        """),
    "an array literal": MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Array<Int> = [mag(@Int.0)];
          @Array<Int>.0[0]
        }
        """),
    "a refined parameter boxed": POS + BOX + textwrap.dedent("""\
        public fn f(@PosInt -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          let @Box = MkBox(@PosInt.0);
          match @Box.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
    "a refined return boxed": POS + BOX + textwrap.dedent("""\
        private fn pos(@Int -> @PosInt)
          requires(@Int.0 > 0)
          ensures(true)
          effects(pure)
        {
          @Int.0
        }

        public fn f(@Int -> @Int)
          requires(@Int.0 > 0)
          ensures(@Int.result > 0)
          effects(pure)
        {
          let @Box = MkBox(pos(@Int.0));
          match @Box.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
    "a Nat parameter boxed": BOX + textwrap.dedent("""\
        public fn f(@Nat -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Box = MkBox(@Nat.0);
          match @Box.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
}

#: Programs the same field read must NOT prove.
CONTROLS: dict[str, str] = {
    "a postcondition stronger than the fact": BOX + MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          let @Box = MkBox(mag(@Int.0));
          match @Box.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
    "a field holding a value no contract speaks of": BOX + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Box = MkBox(@Int.0);
          match @Box.0 {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
    "the other field of a nested constructor": NESTED + MAG + textwrap.dedent("""\
        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          let @Outer = MkOuter(MkPair(mag(@Int.0), -7));
          match @Outer.0 {
            MkOuter(MkPair(@Int, @Int)) -> @Int.0
          }
        }
        """),
    "a box from a callee whose contract is ensures(true)": BOX + MAG + textwrap.dedent("""\
        private fn wrap(@Int -> @Box)
          requires(true)
          ensures(true)
          effects(pure)
        {
          MkBox(mag(@Int.0))
        }

        public fn f(@Int -> @Int)
          requires(true)
          ensures(@Int.result >= 0)
          effects(pure)
        {
          match wrap(@Int.0) {
            MkBox(@Int) -> @Int.0
          }
        }
        """),
}


def _ensures(source: str, fn: str) -> tuple[list[str], list[str]]:
    """The statuses of *fn*'s `ensures` obligations in *source*, and the
    codes of the run's error diagnostics."""
    result = _verify(source)
    statuses = [o.status for o in result.obligations
                if o.kind == "ensures" and o.fn_name == fn]
    errors = [d.error_code for d in result.diagnostics
              if d.severity == "error"]
    return statuses, errors


def test_repro_box_then_unbox_proves() -> None:
    """The program #909 filed: `MkBox(mag(-5))` matched back proves
    `ensures(@Int.result >= 0)` on `main`."""
    statuses, errors = _ensures(REPRO, "main")
    assert statuses == ["verified"]
    assert errors == []


@pytest.mark.parametrize("shape", sorted(SHAPES))
def test_fact_holds_through_a_field(shape: str) -> None:
    statuses, errors = _ensures(SHAPES[shape], "f")
    assert statuses == ["verified"], shape
    assert errors == [], shape


@pytest.mark.parametrize("control", sorted(CONTROLS))
def test_field_read_proves_nothing_the_fact_does_not(control: str) -> None:
    statuses, errors = _ensures(CONTROLS[control], "f")
    assert statuses == ["violated"], control
    assert errors == ["E500"], control


# =====================================================================
# The callee in another module
# =====================================================================

#: `mag`, exported by a module of its own.
MAGNITUDE = "module magnitude;\n\n" + MAG.replace(
    "private fn mag", "public fn mag")

_IMPORTER = "import magnitude(mag);\n\n" + BOX + textwrap.dedent("""\
    public fn f(@Int -> @Int)
      requires(true)
      ensures(POST)
      effects(pure)
    {
      let @Box = MkBox(CALL);
      match @Box.0 {
        MkBox(@Int) -> @Int.0
      }
    }
    """)


def _imported(tmp_path: Path, call: str, post: str) -> tuple[list[str], list[str]]:
    """The statuses of `f`'s `ensures` and the error codes, where `f` boxes
    *call*, a call of the imported `mag`, and promises *post*."""
    assert "public fn mag" in MAGNITUDE
    files = {
        "magnitude.vera": MAGNITUDE,
        "main.vera": _IMPORTER.replace("CALL", call).replace("POST", post),
    }
    _diagnostics, result = verify_multi_module(tmp_path, files)
    statuses = [o.status for o in result.obligations
                if o.kind == "ensures" and o.fn_name == "f"]
    errors = [d.error_code for d in result.diagnostics
              if d.severity == "error"]
    return statuses, errors


@pytest.mark.parametrize("call", ["mag(@Int.0)", "magnitude::mag(@Int.0)"])
def test_fact_from_an_imported_callee_holds_through_a_field(
    tmp_path: Path, call: str,
) -> None:
    statuses, errors = _imported(tmp_path, call, "@Int.result >= 0")
    assert statuses == ["verified"], call
    assert errors == [], call


def test_imported_callee_proves_nothing_its_contract_does_not(
    tmp_path: Path,
) -> None:
    statuses, errors = _imported(tmp_path, "mag(@Int.0)", "@Int.result > 0")
    assert statuses == ["violated"]
    assert errors == ["E500"]
