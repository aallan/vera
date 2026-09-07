"""Pins for `examples/ephemeris.vera` — the tree's only floating-point program.

`scripts/check_examples_run.py` registers this example as a bare `RunSpec()`, so
the gate asserts a trap-free exit and *some* output.  That is deliberately weak:
per the CHANGELOG, output pinning "stays in the dedicated tests that already do
it, so the gate does not go red on a cosmetic edit to an example", and `expect=`
sentinels are reserved for the three examples that reach outside the process.

But a bare `RunSpec()` leaves this particular example under-covered in the one
way that matters.  A float codegen regression could perturb `sin` in the last
bits, move the right ascension by an arcsecond, and the gate would stay green —
on the single example whose entire purpose is floating-point correctness.  So the
numbers are pinned here instead, following the `examples/effect_handler.vera`
pattern in `test_codegen_effects.py`.

Three jobs, deliberately separated:

  - `test_output_pinned` is the exact-string pin.  It fails on ANY drift,
    including bit-level float differences, and it is the tripwire.
  - `test_agrees_with_erfa` re-derives the angles from that output and checks
    them against an INDEPENDENT reference (ERFA's analytic model, via astropy).
    It is redundant while the pin holds, and that is the point: if someone
    legitimately changes the algorithm and updates the pinned string, this test
    independently establishes that the new string is still astronomically
    correct.  Do not delete it as duplicated coverage.
  - `test_wrap_deg_proves_at_tier_1` pins the example's headline claim.

Note what is pinned and what is not.  The example agrees with ERFA only to ~19
arcsec, because the JPL low-precision element set is an arcminute-accurate model;
the *arithmetic*, however, is deterministic to the last digit.  The exact-string
pin therefore asserts REPRODUCIBILITY of the computation, not ACCURACY of the
model.  If a better ephemeris ever motivates changing these digits, that is a
change to the model and the pin should be updated with the reference values
recomputed — not "fixed" toward some more precise source while leaving the
element set alone.
"""

from __future__ import annotations

import re
from math import acos, cos, radians, sin
from pathlib import Path

import pytest

from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from vera.verifier import verify

from tests.codegen_helpers import _compile, _run_io

EXAMPLE = Path(__file__).parent.parent / "examples" / "ephemeris.vera"

# Independent reference: ERFA's analytic model at JD 2461456.5 TT, obtained via
# astropy's `get_sun` / `get_body` on the offline 'builtin' ephemeris.  Degrees.
ERFA_REFERENCE = {
    "Sun": (332.783333, -11.214167),
    "Mars": (153.957083, +15.553333),
}

# The element set is documented as arcminute-accurate over 1800-2050, so 30
# arcsec is a tight-but-honest bound on agreement rather than a rounding fudge.
AGREEMENT_TOLERANCE_ARCSEC = 30.0


@pytest.fixture(scope="module")
def source() -> str:
    return EXAMPLE.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def obligations(source: str) -> list:
    """Verify once and share the obligation stream.

    Verifying this example is a full Z3 pass over 450 lines with float theory in
    play, so it is module-scoped rather than repeated per test.
    """
    ast = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(ast, source)
    # A type error makes every downstream obligation meaningless -- the stream
    # would still be produced, and the tier pins below would then be asserting
    # things about a program that does not compile.  Fail here instead, where
    # the message names the real cause.
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, (
        "ephemeris.vera failed to type-check, so its obligation stream is "
        f"meaningless: {[(d.error_code, d.description) for d in errors]}"
    )
    result = verify(
        ast,
        source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    return list(result.obligations)


def _obligations_at_budget(source: str, timeout_ms: int) -> list:
    """The obligation stream re-derived under an explicit solver budget."""
    ast = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(ast, source)
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, (
        "ephemeris.vera failed to type-check, so its obligation stream is "
        f"meaningless: {[(d.error_code, d.description) for d in errors]}"
    )
    result = verify(
        ast,
        source,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        timeout_ms=timeout_ms,
    )
    return list(result.obligations)


def _angular_separation_arcsec(
    ra1: float, dec1: float, ra2: float, dec2: float
) -> float:
    """Great-circle separation between two equatorial positions, in arcsec."""
    r1, d1, r2, d2 = (radians(v) for v in (ra1, dec1, ra2, dec2))
    cos_sep = sin(d1) * sin(d2) + cos(d1) * cos(d2) * cos(r1 - r2)
    return acos(min(1.0, max(-1.0, cos_sep))) * 206264.806247


def _parse_row(line: str) -> tuple[str, float, float]:
    """Recover (body, RA degrees, Dec degrees) from one output row.

    Deliberately parses the *rendered* text rather than calling the example's
    internals, so a formatting bug that produces a well-formed but wrong string
    is caught here rather than silently passing.
    """
    m = re.match(
        r"\s*(\w+)\s+RA\s+(\d{2})h(\d{2})m([\d.]+)s"
        r"\s+Dec\s+([+-])(\d{2})d(\d{2})m(\d{2})s",
        line,
    )
    assert m is not None, f"unparseable output row: {line!r}"
    body, rh, rm, rs, sign, dd, dm, ds = m.groups()
    ra = (int(rh) + int(rm) / 60.0 + float(rs) / 3600.0) * 15.0
    dec = int(dd) + int(dm) / 60.0 + int(ds) / 3600.0
    return body, ra, (-dec if sign == "-" else dec)


class TestEphemerisExample:
    """`examples/ephemeris.vera` compiles, runs, and holds its numbers."""

    def test_compiles(self, source: str) -> None:
        """The example compiles without errors."""
        assert _compile(source).ok

    def test_output_pinned(self, source: str) -> None:
        """Exact stdout.  Any drift — including in the last float bit — fails.

        Cross-checked against `test_agrees_with_erfa`; see the module docstring
        before updating these digits.
        """
        assert _run_io(source, fn="main") == (
            "Geocentric positions for JD 2461456.5 (2027 February 20.0 TT)\n"
            "\n"
            "  Sun    RA 22h11m09.2s   Dec -11d12m43s   0.988616 AU\n"
            "  Mars   RA 10h15m49.5s   Dec +15d33m16s   0.677839 AU\n"
        )

    def test_agrees_with_erfa(self, source: str) -> None:
        """Rendered positions match an independent model to within 30 arcsec.

        Independent of `test_output_pinned` by design: this establishes that the
        numbers are astronomically right, not merely unchanged.
        """
        rows = [
            ln for ln in _run_io(source, fn="main").splitlines()
            if "RA" in ln and "Dec" in ln
        ]
        assert len(rows) == len(ERFA_REFERENCE), f"expected two rows, got {rows}"

        for line in rows:
            body, ra, dec = _parse_row(line)
            assert body in ERFA_REFERENCE, f"unexpected body {body!r}"
            ref_ra, ref_dec = ERFA_REFERENCE[body]
            sep = _angular_separation_arcsec(ra, dec, ref_ra, ref_dec)
            assert sep < AGREEMENT_TOLERANCE_ARCSEC, (
                f"{body}: {sep:.1f} arcsec from the ERFA reference "
                f"(limit {AGREEMENT_TOLERANCE_ARCSEC}); computed "
                f"RA={ra:.6f} Dec={dec:+.6f}, reference "
                f"RA={ref_ra:.6f} Dec={ref_dec:+.6f}"
            )

    def test_distances_pinned(self, source: str) -> None:
        """Geocentric distances, to the printed precision.

        Note what this does NOT catch: reversing the operand order in `vec_sub`
        leaves both distances bit-identical, because a vector and its negation
        have the same magnitude.  Verified by perturbation — that bug moves the
        Sun 648,000 arcsec and does not budge either distance.  It is caught by
        `test_output_pinned` and `test_agrees_with_erfa`, not here.

        What this does catch is a wrong *pairing* — subtracting the wrong body's
        position, or dropping the geocentric step entirely.  Mars is near
        opposition at this epoch, so the Earth-Mars distance is close to its
        minimum; dropping the geocentric step makes Mars print Earth's own
        0.988616 AU (verified by perturbation) instead of 0.677839.
        """
        out = _run_io(source, fn="main")
        assert "0.988616 AU" in out, "Sun distance changed"
        assert "0.677839 AU" in out, "Mars distance changed"


class TestEphemerisVerification:
    """The example's contracts land in the tiers its header claims."""

    def test_eccentricity_bounds_prove_at_tier_1(self, obligations: list) -> None:
        """The `Ecc` bounds are PROVED, and cheaply — the construction story.

        `earth_elements` and `mars_elements` guard the eccentricity with
        exactly the `Ecc` predicate, so the then-branch discharges by path
        condition and the else-branch by constant folding.  That replaced an
        earlier design which inherited the bound from refined `Julian` /
        `Century` types and carried it through a division chain: correct, but
        it cost ~9-11 s against the 10 s default budget, so the reported tier
        depended on machine load.

        Pinning these two as VERIFIED is what stops that regressing.  If the
        guard is loosened, or the date types are re-refined and the bound goes
        back through the division, this test still passes only while the proof
        stays cheap enough to land — and the corpus pin in
        `test_verifier_adt_decreases.py` runs at the DEFAULT budget precisely
        so a return to the expensive shape shows up as a failure rather than
        as flakiness.

        The guard's else branch is verification-side coverage only: the
        published element sets keep e near 0.0167 and 0.0934, so it is
        provably unreachable at run time and no execution test can cover it.
        That is the point of proving the bound rather than testing it.
        """
        binds = [o for o in obligations if o.kind == "refine_bind"]
        # WHOSE binds, not just how many.  A count-and-status pin passes
        # unchanged if the guard is deleted from one element function and an
        # unrelated refined bind appears elsewhere -- same arity, same
        # statuses, different program.  Naming the two functions is what makes
        # the pin about the construction story rather than about arithmetic.
        #
        # The CONSTRUCTION story is these two functions'.  `main` also carries
        # refined binds since #1410 -- it passes an `Elements` (whose fields
        # are refined) to `helio`, and a call argument now has to establish the
        # refinements written inside its parameter's type -- but those are
        # about the argument boundary, so they are pinned separately below and
        # excluded here rather than allowed to slacken this set into "whatever
        # the program happens to raise".
        story = [
            o for o in binds
            if o.fn_name in ("earth_elements", "mars_elements")
        ]
        assert {o.fn_name for o in story} == {
            "earth_elements", "mars_elements"
        }, [(o.fn_name, o.kind, o.status) for o in binds]
        assert len(story) == 2, [
            (o.fn_name, o.kind, o.status) for o in binds
        ]
        assert all(o.status == "verified" for o in story), [
            (o.fn_name, o.status) for o in story
        ]

    def test_element_arguments_prove_at_the_call_boundary(
        self, obligations: list,
    ) -> None:
        """`helio(earth_elements(...))` establishes `Elements`' refined fields.

        Since #1410 an argument whose parameter type writes a refinement on a
        component carries the obligation the construction position already
        had; `main` makes two such calls.  `Elements` has ONE refined field,
        `Ecc` — the other five are plain `Float64` aliases — so these two
        obligations carry that bound and nothing else.  Both PROVE, because the producing
        function's declared return type carries exactly those refinements and
        its own construction discharged them at Tier 1 -- the modular rule the
        callee's single proof leans on, now recorded rather than assumed.
        A demotion here would mean the element functions stopped establishing
        their own fields.
        """
        arg_binds = [
            o for o in obligations
            if o.kind == "refine_bind" and o.fn_name == "main"
        ]
        assert len(arg_binds) == 2, [
            (o.fn_name, o.status, o.line) for o in arg_binds
        ]
        assert all(o.status == "verified" for o in arg_binds), [
            (o.fn_name, o.status) for o in arg_binds
        ]

    def test_wrap_deg_proves_at_tier_1(self, obligations: list) -> None:
        """`wrap_deg`'s [0, 360) range is PROVED, not runtime-checked.

        This is the example's headline claim and the reason it is worth having:
        a static proof that an angle-wrap bug cannot occur for any input.  If a
        verifier change silently demotes it to Tier 3 the example still runs and
        still prints the right answer, but its header becomes false — so the
        claim is pinned rather than left to prose.

        Note this asserts the STATUS of one named function's contracts, not a
        corpus-wide tier count.  Obligation totals move legitimately as the
        soundness work adds obligations (see the #779/#985 CHANGELOG entry), so
        pinning 48/3 here would be brittle noise.  This is the load-bearing bit.
        """
        wrap = [
            o for o in obligations
            if o.fn_name == "wrap_deg" and o.kind == "ensures"
        ]
        assert wrap, "no ensures obligation recorded for wrap_deg"
        assert all(o.status == "verified" for o in wrap), [
            (o.kind, o.status, o.expr_text) for o in wrap
        ]

    def test_transcendental_contracts_are_tier_3(self, obligations: list) -> None:
        """`declination` does NOT prove, and that asymmetry is the point.

        `right_ascension` and `declination` assert the same shape of range claim
        on an angle.  The first proves because its value returns through
        `wrap_deg`; the second cannot, because `asin` sits between the claim and
        the evidence.  Float builtins are opaque to the solver by design (#797
        maps `@Float64` to `z3.FPSort(11, 53)`), so if this ever starts proving,
        something has changed about that boundary and the example's discussion of
        it needs revisiting.
        """
        dec = [
            o for o in obligations
            if o.fn_name == "declination" and o.kind == "ensures"
        ]
        assert dec, "no ensures obligation recorded for declination"
        # EXACTLY `tier3` -- the categorical `asin` demotion, runtime-guarded.
        # `!= "verified"` would also accept `tier3_unguarded` (the guard was
        # lost, and nothing checks the range at run time either) and `timeout`
        # (the obligation stopped being categorical and is now merely slow).
        # Both are regressions this pin exists to catch.
        assert all(o.status == "tier3" for o in dec), [
            (o.kind, o.status) for o in dec
        ]

        ra = [
            o for o in obligations
            if o.fn_name == "right_ascension" and o.kind == "ensures"
        ]
        assert ra, "no ensures obligation recorded for right_ascension"
        assert all(o.status == "verified" for o in ra), [
            (o.kind, o.status) for o in ra
        ]

    @pytest.mark.parametrize("budget_ms", [1_000, 10_000, 60_000])
    def test_transcendentals_stay_tier_3_at_any_budget(
        self, source: str, budget_ms: int
    ) -> None:
        """The two Tier-3s are CATEGORICAL, which is a different claim.

        The example's header says "no solver budget reaches them", and the
        sibling test above only shows they are Tier 3 at the default.  A claim
        about every budget needs more than one budget, so this re-verifies at
        a smaller and a much larger one.  Being budget-parameterised, it also
        cannot flake the way a wall-clock assertion would: nothing here
        measures elapsed time, only which tier the solver lands on.

        `sqrt` and `asin` are opaque to the SMT translation by design, so more
        time cannot help.  Exact `tier3` matters in both directions:
        `verified` at 60 s would falsify the header, and `timeout` would mean
        the demotion had stopped being categorical and become merely slow.
        """
        obligations = _obligations_at_budget(source, budget_ms)
        opaque = {
            o.fn_name: o.status
            for o in obligations
            if o.fn_name in ("vec_norm", "declination") and o.kind == "ensures"
        }
        assert opaque == {
            "vec_norm": "tier3",
            "declination": "tier3",
        }, (budget_ms, opaque)

    def test_kepler_solve_termination_proves(self, obligations: list) -> None:
        """The `decreases` metric on the Newton-Raphson loop is discharged.

        The solver's termination does not depend on numerical convergence — the
        fuel counter is what bounds it, and that bound is proved.
        """
        dec = [
            o for o in obligations
            if o.fn_name == "kepler_solve" and o.kind == "decreases"
        ]
        assert dec, "no decreases obligation recorded for kepler_solve"
        assert all(o.status == "verified" for o in dec), [
            (o.kind, o.status) for o in dec
        ]
