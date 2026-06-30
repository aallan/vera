"""Unit tests for `scripts/check_diagnostic_fields.py` (#682).

The script enforces spec/00-introduction.md §0.5.1 "Diagnostic
Structure": every diagnostic MUST carry an error code, a rationale,
a fix, and a spec reference.  It AST-parses every `Diagnostic(...)`
constructor and every `self._error(...)` / `self._warning(...)` call
in `vera/` and fails when a required field is missing without an
explicit, reasoned exemption.

Design (grounded in DESIGN.md §"Explicitness over convenience" — the
exemption surface is explicit and reasoned, never silently inferred):

- **Required by default:** rationale, fix, spec_ref (the three content
  fields of spec §0.5.1, per #682's AC; error_code is a tracked follow-up).
- **Severity rule:** a `warning` carries no corrected-code template,
  so `fix` is not required of warnings.
- **Structural registry:** the codegen `_error`/`_warning` helpers
  build internal-compiler (E699) / "function skipped" diagnostics
  that have no user fix or spec section — exempt from `fix`/`spec_ref`,
  declared once with a written reason in the script.
- **Per-call opt-out:** `# diag-fields-exempt: <reason>` on the call,
  reason mandatory (AC3).
- **Plumbing skip:** the `Diagnostic(...)` construction *inside* an
  `_error`/`_warning` helper def is not an independent site; its
  call sites + the registry govern it.

The script lives at `scripts/check_diagnostic_fields.py`.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT_PATH = ROOT / "scripts" / "check_diagnostic_fields.py"


@pytest.fixture(scope="module")
def mod() -> object:
    spec = importlib.util.spec_from_file_location(
        "check_diagnostic_fields", SCRIPT_PATH)
    assert spec is not None and spec.loader is not None
    m = importlib.util.module_from_spec(spec)
    sys.modules["check_diagnostic_fields"] = m
    spec.loader.exec_module(m)
    return m


def _missing(violations: list, line_contains: str) -> set:
    """Return the set of missing-field names for the violation whose
    source is on the (unique) line containing `line_contains`."""
    hits = [v for v in violations if line_contains in (v.snippet or "")]
    assert len(hits) == 1, f"expected 1 site matching {line_contains!r}, got {len(hits)}"
    return set(hits[0].missing)


# =====================================================================
# Fully-tagged sites pass
# =====================================================================

class TestFullyTagged:
    def test_complete_error_call_passes(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'desc', error_code='E140',\n"
            "                    rationale='r', fix='x', spec_ref='Ch4')\n"
        )
        assert mod.check_source(src, "vera/checker/expressions.py") == []

    def test_complete_direct_diagnostic_passes(self, mod: object) -> None:
        src = (
            "d = Diagnostic(description='d', location=loc, error_code='E001',\n"
            "               rationale='r', fix='x', spec_ref='Ch1')\n"
        )
        assert mod.check_source(src, "vera/errors.py") == []


# =====================================================================
# Missing fields are flagged
# =====================================================================

class TestMissingFlagged:
    def test_bare_error_call_flags_three(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'desc', error_code='E140')\n"
        )
        v = mod.check_source(src, "vera/checker/expressions.py")
        assert _missing(v, "self._error") == {"rationale", "fix", "spec_ref"}

    def test_empty_string_counts_as_missing(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'd', error_code='E1', rationale='',\n"
            "                    fix='x', spec_ref='Ch4')\n"
        )
        assert _missing(mod.check_source(src, "vera/checker/calls.py"), "self._error") == {"rationale"}

    def test_error_code_not_enforced_by_this_gate(self, mod: object) -> None:
        """#682 scopes the gate to rationale/fix/spec_ref.  A site carrying
        those three but no error_code passes — error_code enforcement is a
        deliberate, documented follow-up, not part of this gate."""
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'd', rationale='r', fix='x', spec_ref='Ch4')\n"
        )
        assert mod.check_source(src, "vera/checker/calls.py") == []

    def test_bare_direct_diagnostic_flags_all(self, mod: object) -> None:
        src = "d = Diagnostic(description='d', location=loc)\n"
        assert _missing(mod.check_source(src, "vera/transform.py"), "Diagnostic(") == {
            "rationale", "fix", "spec_ref"}


# =====================================================================
# Severity rule: warnings carry no fix
# =====================================================================

class TestSeverityRule:
    def test_warning_call_not_required_to_have_fix(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._warning(node, 'd', error_code='E520', rationale='r',\n"
            "                      spec_ref='Ch6')\n"
        )
        assert mod.check_source(src, "vera/verifier.py") == []

    def test_warning_still_needs_rationale_and_spec_ref(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._warning(node, 'd', error_code='E520')\n"
        )
        assert _missing(mod.check_source(src, "vera/verifier.py"), "self._warning") == {
            "rationale", "spec_ref"}

    def test_direct_warning_diagnostic_exempt_from_fix(self, mod: object) -> None:
        src = (
            "d = Diagnostic(description='d', location=loc, severity='warning',\n"
            "               error_code='W001', rationale='r', spec_ref='Ch3')\n"
        )
        assert mod.check_source(src, "vera/tester.py") == []


# =====================================================================
# Structural registry: codegen helpers are fix/spec_ref-exempt
# =====================================================================

class TestCodegenRegistry:
    def test_codegen_error_exempt_from_fix_and_spec_ref(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'internal', error_code='E699', rationale='r')\n"
        )
        assert mod.check_source(src, "vera/codegen/functions.py") == []

    def test_codegen_error_still_needs_rationale(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'internal', error_code='E699')\n"
        )
        assert _missing(mod.check_source(src, "vera/codegen/functions.py"), "self._error") == {
            "rationale"}

    def test_checker_error_NOT_exempt_like_codegen(self, mod: object) -> None:
        """The codegen exemption must not bleed into the checker."""
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'd', error_code='E140', rationale='r')\n"
        )
        assert _missing(mod.check_source(src, "vera/checker/expressions.py"), "self._error") == {
            "fix", "spec_ref"}

    def test_direct_diagnostic_in_codegen_NOT_auto_exempt(self, mod: object) -> None:
        """A direct Diagnostic() in a codegen file is not covered by the
        helper registry — it must backfill or carry a per-call opt-out."""
        src = "d = Diagnostic(description='d', location=loc, error_code='E699', rationale='r')\n"
        assert _missing(mod.check_source(src, "vera/codegen/core.py"), "Diagnostic(") == {
            "fix", "spec_ref"}


# =====================================================================
# Per-call opt-out: # diag-fields-exempt: <reason>
# =====================================================================

class TestOptOut:
    def test_exempt_with_reason_suppresses(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'fallback', error_code='E010')  # diag-fields-exempt: defensive internal invariant\n"
        )
        assert mod.check_source(src, "vera/transform.py") == []

    def test_exempt_without_reason_is_itself_a_violation(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'fallback', error_code='E010')  # diag-fields-exempt\n"
        )
        v = mod.check_source(src, "vera/transform.py")
        assert len(v) == 1 and v[0].missing == ["<opt-out reason>"]


# =====================================================================
# Plumbing skip: Diagnostic() inside an _error/_warning helper def
# =====================================================================

class TestPlumbingSkip:
    def test_diagnostic_inside_helper_def_is_skipped(self, mod: object) -> None:
        src = (
            "class C:\n"
            "    def _error(self, node, description, *, rationale='', error_code=''):\n"
            "        self.errors.append(Diagnostic(\n"
            "            description=description, location=loc,\n"
            "            rationale=rationale, error_code=error_code))\n"
        )
        assert mod.check_source(src, "vera/codegen/core.py") == []


# =====================================================================
# spec_ref validity: a present spec_ref must cite a real spec section
# =====================================================================

class TestSpecRefValidity:
    def _v(self, mod: object, ref: str) -> list:
        src = f"self._error(node, 'd', spec_ref='{ref}')\n"
        return mod.spec_ref_violations_in_source(src, "vera/checker/x.py")

    def test_valid_section_ref_passes(self, mod: object) -> None:
        assert self._v(mod, 'Chapter 4, Section 4.4 "Arithmetic Expressions"') == []

    def test_nonexistent_section_flagged(self, mod: object) -> None:
        v = self._v(mod, 'Chapter 4, Section 4.99 "Nope"')
        assert len(v) == 1 and "does not exist" in v[0].missing[0]

    def test_wrong_title_right_section_flagged(self, mod: object) -> None:
        # §4.3 is "Slot References", not "Operators" — the canonical drift bug.
        v = self._v(mod, 'Chapter 4, Section 4.3 "Operators"')
        assert len(v) == 1 and "Slot References" in v[0].missing[0]

    def test_cosmetic_title_drift_is_tolerated(self, mod: object) -> None:
        # Actual title is "Anonymous Functions (Closures)"; the lenient norm
        # drops the parenthetical, so a cosmetic re-title does not break.
        assert self._v(mod, 'Chapter 5, Section 5.7 "Anonymous Functions"') == []

    def test_valid_chapter_only_ref_passes(self, mod: object) -> None:
        assert self._v(mod, 'Chapter 6, "Contracts"') == []

    def test_typed_hole_section_exists(self, mod: object) -> None:
        # §4.17 was added by this change; W001 / E614 cite it.
        assert self._v(mod, 'Chapter 4, Section 4.17 "Typed Holes"') == []


# =====================================================================
# Integration: the live vera/ tree must be fully tagged AND every
# spec_ref must resolve to a real spec section.
# =====================================================================

class TestLiveTree:
    def test_live_vera_tree_is_clean(self, mod: object) -> None:
        files = mod.iter_vera_files(ROOT / "vera")
        violations = mod.check_paths(files) + mod.spec_ref_violations(files)
        report = "\n".join(
            f"  {v.file}:{v.line} {v.target} {v.missing}" for v in violations)
        assert violations == [], f"{len(violations)} diagnostic problem(s):\n{report}"
