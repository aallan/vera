"""`safe_divide`, the flagship example, proves its division whole.

`@Int.0 / @Int.1` traps on two divisors: zero, and -1 under `INT_MIN`, whose
quotient leaves the `Int` range.  The verifier obligates the first (E526)
and, until #1598's row, not the second, so a `requires` that excludes only
zero left one input to a trap while the landing page says the clause makes
the division proved.  `requires(@Int.1 > 0)` excludes both: the stand-in for
the missing obligation below proves at Tier 1 under it.  Every document that
shows the example shows the same clause.
"""

from __future__ import annotations

import re
from pathlib import Path

from tests import pipeline

ROOT = Path(__file__).resolve().parent.parent
EXAMPLE = ROOT / "examples" / "safe_divide.vera"

#: The condition the verifier will obligate for `INT_MIN / -1` (#1598),
#: written as an assertion the solver can be asked today.
_STAND_IN = "assert(!(@Int.0 == -9223372036854775807 - 1 && @Int.1 == -1));"

#: The hand-kept documents that show the example (`docs/index.md` is written
#: from `scripts/build_site.py`, and `docs/SKILL.md` from SKILL.md).
_DOCS = (
    "README.md", "SKILL.md", "EXAMPLES.md", "FAQ.md", "PYPI_README.md",
    "docs/index.md", "scripts/build_site.py", *sorted(
        str(p.relative_to(ROOT).as_posix())
        for p in (ROOT / "spec").glob("*.md")),
)


def _requires_line(text: str) -> str:
    match = re.search(r"^\s*(requires\(.*\))\s*$", text, flags=re.M)
    assert match, "no requires clause"
    return match.group(1)


def test_repro_the_int_min_quotient_is_proved_under_the_example_s_requires(
    tmp_path: Path,
) -> None:
    """The stand-in assertion, the first statement of the example's body,
    is `verified` (Tier 1): under the example's own `requires`, no input
    reaches `INT_MIN / -1`."""
    source = EXAMPLE.read_text(encoding="utf-8")
    body = source.index("{\n") + 2
    probe = source[:body] + "  " + _STAND_IN + "\n" + source[body:]
    path = tmp_path / "safe_divide_probe.vera"
    path.write_text(probe, encoding="utf-8")
    verified = pipeline.verify(path)
    assert verified.ok, [d.description for d in verified.errors]
    asserts = [o for o in verified.obligations if o.kind == "assert"]
    assert [o.status for o in asserts] == ["verified"], asserts


def test_every_document_shows_the_example_s_requires() -> None:
    """Each block defining `fn safe_divide` in the hand-kept documents
    carries the clause the example does."""
    want = _requires_line(EXAMPLE.read_text(encoding="utf-8"))
    seen = 0
    for name in _DOCS:
        text = (ROOT / name).read_text(encoding="utf-8")
        for block in re.findall(
                r"fn safe_divide\(@Int, @Int -> @Int\)\n(.*?)\{", text,
                flags=re.S):
            seen += 1
            assert _requires_line(block) == want, (name, block)
    assert seen >= 10, seen


def test_the_example_still_divides() -> None:
    """`safe_divide(2, 10)` is 5, as every document's run marker says."""
    ran = pipeline.run(EXAMPLE, "safe_divide", [2, 10])
    assert ran.trap is None and ran.execution.value == 5
