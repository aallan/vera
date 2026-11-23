"""The `vera/proposeEdit` gate over the whole status table (#1610).

The rule (LSP_SERVER.md, `vera/proposeEdit`): an edit applies, without
`force`, only if every obligation it leaves is `verified` or is what it
was.  An obligation the edit introduces has no `before`, so it must be
`verified`; one it keeps, at the same span or moved (paired on the
span-insensitive key), must be `verified` or hold the status it had.  A
check the solver did not finish is not a proof (DESIGN.md, "Contracts as
the source of truth": the compiler verifies what the solver can decide
and checks the rest at run time), so `timeout` is judged as `tier3` is.

The class is the table: every `before` (none, and each status) against
every `after`, at a fixed span and moved one line.  The gate is run
through the real `propose_edit`, with a stand-in session returning the
speculative stream: a `timeout` is the solver's whim, not a property of a
source text, so no fixture reaches it reliably.
"""

from __future__ import annotations

import types

import pytest

from vera.lsp.workflows import propose_edit
from vera.obligations.core import ProofObligation

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of its parametrised cells, and all of them when it changes this file or a
# module that decides the verdict: the gate, and the delta it reads.
pytestmark = pytest.mark.matrix(decides=[
    "vera/lsp/workflows.py",
    "vera/lsp/extensions.py",
])

STATUSES = ("verified", "violated", "tier3", "timeout", "tier3_unguarded")
URI = "file:///p.vera"


class _Stub:
    """A session whose speculative run returns *obligations*."""

    def __init__(self, obligations: list[ProofObligation]) -> None:
        self._obligations = obligations

    def verify_source(
        self, text: str, file: str | None = None,
    ) -> types.SimpleNamespace:
        return types.SimpleNamespace(
            ok=True, obligations=self._obligations, diagnostics=[],
        )


def _ob(status: str, line: int = 5, fn: str = "f") -> ProofObligation:
    return ProofObligation(
        fn_name=fn, kind="ensures", expr_text="p", status=status,
        line=line, column=3, file="/p.vera",
    )


#: An obligation proved on both sides, so neither stream is ever empty.
_ANCHOR = ProofObligation(
    fn_name="g", kind="ensures", expr_text="q", status="verified",
    line=1, column=3, file="/p.vera",
)


def _applies(before: str | None, after: str) -> bool:
    """The rule, stated once: verified, or what it was."""
    return after == "verified" or after == before


_CELLS = [
    (before, after, shape)
    for before in (None,) + STATUSES
    for after in STATUSES
    for shape in ("same", "moved")
    if not (before is None and shape == "moved")
]


@pytest.mark.parametrize(("before", "after", "shape"), _CELLS)
def test_the_gate_over_the_status_table(
    before: str | None, after: str, shape: str,
) -> None:
    baseline = [_ANCHOR] + ([_ob(before)] if before is not None else [])
    speculative = [_ANCHOR, _ob(after, line=5 if shape == "same" else 6)]
    applied, response = propose_edit(
        _Stub(speculative), baseline, URI, "-- text",  # type: ignore[arg-type]
    )
    assert applied is _applies(before, after), (before, after, shape)
    assert response["applied"] is applied
    # `force` overrides every refusal in the table.
    forced, _ = propose_edit(
        _Stub(speculative), baseline, URI, "-- text",  # type: ignore[arg-type]
        force=True,
    )
    assert forced is True


def test_repro_1610_an_introduced_timeout_is_refused() -> None:
    """The issue's shape: a baseline with one verified function, and a
    speculative stream of that plus one `ensures` that timed out.  It
    applied; an introduced `tier3` beside it was refused."""
    for status in ("timeout", "tier3"):
        applied, response = propose_edit(
            _Stub([_ANCHOR, _ob(status)]), [_ANCHOR],  # type: ignore[arg-type]
            URI, "-- text",
        )
        assert applied is False, status
        assert response["proof_delta"]["proof_regressions"] == []


def test_repro_1610_a_relocated_tier3_that_times_out_is_refused() -> None:
    """The issue's second shape: `tier3 -> timeout` across a moved line."""
    applied, response = propose_edit(
        _Stub([_ANCHOR, _ob("timeout", line=6)]),  # type: ignore[arg-type]
        [_ANCHOR, _ob("tier3", line=5)], URI, "-- inserted\n",
    )
    assert applied is False
    (item,) = response["proof_delta"]["timed_out"]
    assert (item["status_before"], item["status_after"]) == (
        "tier3", "timeout")


def test_an_unchanged_timeout_still_applies() -> None:
    """The neighbour the rule keeps: an obligation that timed out before
    and times out after took nothing away, moved or not."""
    for line in (5, 6):
        applied, _ = propose_edit(
            _Stub([_ANCHOR, _ob("timeout", line=line)]),  # type: ignore[arg-type]
            [_ANCHOR, _ob("timeout", line=5)], URI, "-- text",
        )
        assert applied is True, line
