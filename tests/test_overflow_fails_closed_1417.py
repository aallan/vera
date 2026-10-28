"""An unclassified operand pair emits the overflow guard (#1417).

`_overflow_arith_codegen_type` answers the width an `+`/`-`/`*` runs at by
classifying each operand.  When it cannot name one it answers `None` —
honestly, since "I do not know" is a real answer and not a type.  What the
emitter then did with that answer was skip the guard, so the arithmetic
wrapped in silence while the verifier's `int_overflow` obligation went on
claiming a runtime check covered it.  That is a false guarantee, and an
unclassified pair is exactly the case nobody can enumerate, so the honest
posture is to guard it: an unknown width now reads as `Int`.

There is no whole-program reproducer.  Instrumenting the classifier across
the corpus at #1412 found the `None` path taken zero times in 293 programs,
and hand-construction did not reach it: the classifier reads the checker's
type of each operand, which every operand of a checked program has.

So the lever is the classifier's ANSWER, patched at the seam, and what is
measured is the emitter's decision on it — which is the only thing that
changed.  A cell built on a whole program would be green before and after
and would prove nothing.
"""

from __future__ import annotations

import dataclasses

from vera.typed import build as build_typed

import pytest

from tests.pipeline import checks
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


_SUB = _ADD.replace("@Int.0 + 1", "@Int.0 - 1")


def _compiled(*, semantic_types: dict | None = None, source: str = _ADD):
    """Compile *source* (`_ADD`) through the checker artefacts, as the CLI
    does.

    `module_artifacts` is threaded too (CR PR-review): this helper exists to
    exercise the real pipeline, and a compile that silently drops one of the
    artefact channels is a different pipeline from the one the cells are
    about.
    """
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source,
                                           collect_module_artifacts=True)
    assert not [d for d in diags if d.severity == "error"], diags
    typed = build_typed(program, [], arts)
    if semantic_types is not None:
        # The cell's own fault: the table the guards read, replaced.
        typed = dataclasses.replace(typed, semantic=semantic_types)
    return compile(typed, source=source)


def _wat(*, semantic_types: dict | None = None) -> str:
    return _compiled(semantic_types=semantic_types).wat


def test_an_unnameable_width_is_guarded_as_int(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The property: the classifier says `None`, the guard is emitted anyway.

    Patched at the classifier's own seam rather than at a program feature,
    because no program feature reaches it.  What the patch simulates is the
    one state the `None` return exists for; what the assertion reads is the
    emitted module.  The unpatched classifier is read first, at the same
    site: it names `Int` there, so the guard below is the `or "Int"`
    default's and not a width the classifier named.
    """
    answers: list[str | None] = []
    original = OperatorsMixin._overflow_arith_codegen_type

    def recording(self: OperatorsMixin, expr: object) -> str | None:
        answers.append(original(self, expr))  # type: ignore[arg-type]
        return answers[-1]

    with monkeypatch.context() as patch:
        patch.setattr(
            OperatorsMixin, "_overflow_arith_codegen_type", recording)
        _compiled()
    assert answers == ["Int"], answers
    monkeypatch.setattr(
        OperatorsMixin, "_overflow_arith_codegen_type",
        lambda self, expr: None,
    )
    result = _compiled()
    wat = result.wat
    assert checks(result, kind="overflow"), (
        "an arithmetic site whose width the classifier could not name "
        "emitted no overflow guard, so it wraps in silence while the "
        "obligation claims a runtime check:\n" + wat[:800]
    )
    # And the SIGNED sequence specifically: the sign-agreement test with
    # `i64.xor`, never an unsigned wrap with `i64.lt_u`.  The sequence is
    # not the default's to pick: `_emit_overflow_guard` checks a `Nat`'s
    # range as an `Int`'s (spec §2.2).  The default is read at one place,
    # the subtraction cell below.
    assert "i64.xor" in wat, (
        "the guard emitted is not the signed sequence, so the site is "
        "checked against the unsigned range:\n" + wat[:800]
    )
    assert "i64.lt_u" not in wat, wat[:800]


def test_an_unnameable_subtraction_is_guarded_as_int(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The one place the fail-closed default is read: a subtraction the
    classifier names `Nat` is left to the `nat_sub` underflow check and
    takes no overflow guard, so an unknown width read as `Nat` would leave
    an unclassified subtraction unguarded.  Read as `Int`, it is guarded.
    The unpatched classifier names this site `Int` first, as above."""
    answers: list[str | None] = []
    original = OperatorsMixin._overflow_arith_codegen_type

    def recording(self: OperatorsMixin, expr: object) -> str | None:
        answers.append(original(self, expr))  # type: ignore[arg-type]
        return answers[-1]

    with monkeypatch.context() as patch:
        patch.setattr(
            OperatorsMixin, "_overflow_arith_codegen_type", recording)
        _compiled(source=_SUB)
    assert answers == ["Int"], answers
    monkeypatch.setattr(
        OperatorsMixin, "_overflow_arith_codegen_type",
        lambda self, expr: None,
    )
    result = _compiled(source=_SUB)
    assert checks(result, kind="overflow"), (
        "a subtraction whose width the classifier could not name took the "
        "`Nat` exclusion and no overflow guard:\n" + result.wat[:800]
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

    # And it still ANSWERS `None` when it cannot name a width, rather than
    # guessing one.  Asserted on the classifier's own contract, because the
    # answers captured above are the real ones — `Int` for a classifiable
    # pair — and no program produces the unclassifiable case (CR PR-review).
    monkeypatch.setattr(
        OperatorsMixin, "_overflow_codegen_type", lambda self, expr: None)
    from vera import ast

    add = ast.BinaryExpr(
        op=ast.BinOp.ADD,
        left=ast.IntLit(value=1),
        right=ast.IntLit(value=2),
    )
    assert original(_Probe(), add) is None, (
        "the classifier named a width with no operand type to name it from, "
        "which would put the guess where the verifier's mirror reads it"
    )


class _Probe(OperatorsMixin):
    """The classifier's own `self`, with nothing else installed.

    The two operand lookups it makes are patched out above, so the only
    behaviour under test is what it does with two `None` answers.
    """



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
    # Instantiated, not merely read: WAT text saying `(export "f")` is not
    # evidence that the binary loads or that the export resolves, and a
    # malformed guard would show up here rather than in the text
    # (CR PR-review).
    from vera.codegen.api import execute

    out = execute(_compiled(), fn_name="f", args=[3])
    assert out.value == 4, out


def test_the_verifier_fails_closed_on_the_same_answer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Both legs, not just the emitter (R-1412 F5).

    The emitter reading an unknown width as `Int` is half the fix: the
    verifier gated its OBLIGATION on the same `is not None`, so a site the
    emitter now guards would carry no record to count it — the desync one
    component over from the one #1417 describes.

    Patched at the classifier's seam for the reason the emitter cell gives:
    no program reaches the `None` answer, so the only way to exercise the
    branch is to hand it that answer.
    """
    from vera.verifier import ContractVerifier

    monkeypatch.setattr(
        ContractVerifier, "_overflow_arith_type",
        lambda self, expr: None,
    )
    program = parse_to_ast(_ADD)
    diags, arts = typecheck_with_artifacts(program, _ADD)
    assert not [d for d in diags if d.severity == "error"], diags
    from vera.verifier import verify

    result = verify(build_typed(program, [], arts), _ADD)
    kinds = [o.kind for o in result.obligations]
    assert "int_overflow" in kinds, (
        f"the verifier dropped the overflow obligation for operands it "
        f"could not classify, so the guard the emitter now plants at that "
        f"site is counted by nothing: {kinds}"
    )
