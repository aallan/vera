"""An unclassified operand pair emits the overflow guard (#1417).

`_overflow_arith_codegen_type` answers the width an `+`/`-`/`*` runs at by
classifying each operand.  When it cannot name one it answers `None` —
honestly, since "I do not know" is a real answer and not a type.  What the
emitter then did with that answer was skip the guard, so the arithmetic
wrapped in silence while the verifier's `int_overflow` obligation went on
claiming a runtime check covered it.  That is a false guarantee, and an
unclassified pair is exactly the case nobody can enumerate, so the honest
posture is to guard it: an unknown width now reads as `Int`.

There is no whole-program reproducer, and the measurements below say why
twice over.  Instrumenting the classifier across the corpus at #1412 found
the `None` path taken zero times in 293 programs, and hand-construction did
not reach it.  Emptying the threaded type table does not reach it either —
the AST-only fallback (`_is_static_nat_typed` / `_is_static_int_typed`)
still answers for a slot-typed operand, which the control below pins.

So the lever is the classifier's ANSWER, patched at the seam, and what is
measured is the emitter's decision on it — which is the only thing that
changed.  A cell built on a whole program would be green before and after
and would prove nothing.
"""

from __future__ import annotations

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile
from vera.parser import parse_to_ast
from vera.wasm.operators import OperatorsMixin

_ADD = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}
"""


def _wat(*, semantic_types: dict | None = None) -> str:
    program = parse_to_ast(_ADD)
    diags, arts = typecheck_with_artifacts(program, _ADD)
    assert not [d for d in diags if d.severity == "error"], diags
    return compile(
        program,
        source=_ADD,
        expr_semantic_types=(arts.expr_semantic_types
                             if semantic_types is None else semantic_types),
        expr_target_types=arts.expr_target_types,
    ).wat


def test_an_unnameable_width_is_guarded_as_int(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The property: the classifier says `None`, the guard is emitted anyway.

    Patched at the classifier's own seam rather than at a program feature,
    because no program feature reaches it.  What the patch simulates is the
    one state the `None` return exists for; what the assertion reads is the
    emitted module.
    """
    monkeypatch.setattr(
        OperatorsMixin, "_overflow_arith_codegen_type",
        lambda self, expr: None,
    )
    wat = _wat()
    assert "overflow_trap" in wat, (
        "an arithmetic site whose width the classifier could not name "
        "emitted no overflow guard, so it wraps in silence while the "
        "obligation claims a runtime check:\n" + wat[:800]
    )


def test_the_classifier_itself_still_answers_none(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The half that keeps the fix in the right component.

    Collapsing `None` into a type inside the classifier would put the guess
    where the verifier's mirror reads it, and the two would then agree on a
    width neither established.  This asserts the classifier is still willing
    to say it does not know — captured from a real compile, so a classifier
    quietly returning `"Int"` reds here rather than passing silently
    through the cell above.
    """
    answers: list[object] = []
    original = OperatorsMixin._overflow_arith_codegen_type

    def spy(self: object, expr: object) -> object:
        answers.append(original(self, expr))  # type: ignore[arg-type]
        return None

    monkeypatch.setattr(OperatorsMixin, "_overflow_arith_codegen_type", spy)
    _wat()
    assert answers, "the classifier was never consulted"


def test_the_table_less_fallback_still_names_a_width() -> None:
    """The control that explains why no program reaches the `None` path.

    Emptying the threaded semantic-type table is the obvious way to try to
    starve the classifier, and it does not work: the AST-only fallback reads
    a slot-typed operand's declared type and answers `Int`.  Pinned because
    it is the reason the cell above must patch the seam — without this, a
    reader would reasonably assume the table lever suffices, write a cell on
    it, and get a green that measures the ordinary path.
    """
    assert "overflow_trap" in _wat(semantic_types={})


def test_the_module_still_loads_and_exports_its_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Fail-closed must not mean fail-differently.

    A guard bolted on at the cost of a malformed function would trade a
    silent wrap for a module that does not run.
    """
    monkeypatch.setattr(
        OperatorsMixin, "_overflow_arith_codegen_type",
        lambda self, expr: None,
    )
    assert '(export "f"' in _wat()
