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

    def test_nonconstant_severity_is_flagged(self, mod: object) -> None:
        """A non-literal `severity=` can't be resolved statically, so the gate
        flags it rather than silently assuming 'error' (which would wrongly
        demand a fix of a possibly-warning diagnostic)."""
        src = "d = Diagnostic(description='d', location=loc, severity=lvl)\n"
        v = mod.check_source(src, "vera/tester.py")
        assert len(v) == 1 and "not a string literal" in v[0].missing[0]


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

    def test_marker_inside_a_string_does_not_exempt(self, mod: object) -> None:
        """The opt-out is comment-only: the marker text appearing inside a
        string literal (e.g. a description) must NOT suppress the site."""
        src = "d = Diagnostic(description='see # diag-fields-exempt: x', location=loc)\n"
        v = mod.check_source(src, "vera/transform.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_unanchored_marker_does_not_exempt(self, mod: object) -> None:
        """The directive must be anchored: a near-miss (`-foo` suffix) or a
        mid-comment mention must NOT disable the gate."""
        # (a) suffix near-miss
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'x', error_code='E1')  # diag-fields-exempt-not-really\n"
        )
        v = mod.check_source(src, "vera/transform.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}
        # (b) mid-comment mention — marker not at the start of the comment
        src2 = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'x', error_code='E1')  # note diag-fields-exempt later\n"
        )
        v2 = mod.check_source(src2, "vera/transform.py")
        assert len(v2) == 1
        assert set(v2[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_tab_separated_optout_is_honored(self, mod: object) -> None:
        """An anchored directive whose boundary is a TAB (not a space, and no
        colon) must still be honored — the boundary check accepts any
        whitespace, not just a literal space."""
        # NB: a bare tab directly after the marker — no colon, so this exercises
        # the whitespace boundary and NOT the `OPT_OUT + ":"` path.
        src = (
            "class C:\n"
            "    def f(self, node):\n"
            "        self._error(node, 'x', error_code='E1')  # diag-fields-exempt\tdefensive internal branch\n"
        )
        assert mod.check_source(src, "vera/transform.py") == []
        # and the reason is captured (not blank → not itself a violation)
        reasons = mod._optout_lines(src)
        assert any("defensive internal branch" == r for r in reasons.values())


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


class TestPlumbingSkipNarrowed:
    """#827: the plumbing-skip must key on the helper's *own single* ctor, not
    on the helper's NAME.  A stray/second ``Diagnostic(...)`` inside an
    ``_error``/``_warning`` helper — the exact shape below, straight from the
    #826 adversarial review — must still be inspected.

    This class covers the field-presence and ``spec_ref``-validity passes; the
    third consumer of the skip (``error_code`` registration) is covered by
    ``TestPlumbingSkipCountsEveryOwnScopeCtor`` and
    ``TestSkipWiringPinnedInAllThreePasses``.

    Faults A and B are deliberately ``return`` ctors (a naive "skip the
    return/append child" rule would swallow them), while the legit fully-tagged
    construction is a distractor bound to ``d`` (a rule that counted only
    return/append ctors would see the strays as the helper's *only* ctors and
    elect one of them — see ``TestPlumbingSkipCountsEveryOwnScopeCtor``)."""

    # Two faults inside a helper: A (return, missing `rationale`) and B
    # (return, spec_ref cites a real section under a WRONG title).  §4.3 IS
    # "Slot References", so the first two spec_refs resolve; only B's is bogus.
    SOURCE = (
        "class Compiler:\n"
        "    def _error(self, node, description):\n"
        "        d = Diagnostic(description=description, rationale='r', fix='f',\n"
        "                       spec_ref='Chapter 4, Section 4.3 \"Slot References\"')\n"
        "        if node is None:\n"
        "            # Fault A: real diagnostic missing `rationale`\n"
        "            return Diagnostic(description='real bug', fix='f',\n"
        "                              spec_ref='Chapter 4, Section 4.3 \"Slot References\"')\n"
        "        # Fault B: real diagnostic with a WRONG spec_ref title\n"
        "        return Diagnostic(description='real bug', rationale='r', fix='f',\n"
        "                          spec_ref='Chapter 4, Section 4.3 \"Made Up Title\"')\n"
    )
    # The same body under a name that never triggered the skip — the maintainer's
    # control: it always flagged both, so equal output here proves it was the
    # name-based skip, not the checks, that swallowed the faults.
    CONTROL = SOURCE.replace("def _error", "def _normal")

    def test_stray_presence_fault_flagged(self, mod: object) -> None:
        v = mod.check_source(self.SOURCE, "x.py")
        # Only Fault A (the missing-`rationale` return ctor) — the legit
        # `d = Diagnostic(...)` and Fault B (fully present) stay clean here.
        assert len(v) == 1
        assert v[0].missing == ["rationale"] and "real bug" in (v[0].snippet or "")

    def test_stray_spec_ref_fault_flagged(
        self, mod: object, tmp_path: Path) -> None:
        # Self-contained: pin §4.3's title in an inline fixture spec so the
        # assertion can't break on a live-spec re-title.  The legit ctor +
        # Fault A cite §4.3 correctly (resolve); only Fault B cites it under a
        # WRONG title, so exactly one violation is expected.
        spec_dir = tmp_path / "spec"
        spec_dir.mkdir()
        (spec_dir / "04-x.md").write_text(
            "# Chapter 4: Expressions\n\n### 4.3 Slot References\n",
            encoding="utf-8")
        v = mod.spec_ref_violations_in_source(
            self.SOURCE, "x.py", spec_dir=spec_dir)
        assert len(v) == 1 and "Slot References" in v[0].missing[0]
        assert "Made Up Title" in (v[0].snippet or "")

    def test_matches_non_helper_control(self, mod: object) -> None:
        # The narrowed skip makes the _error span behave like a plain function.
        pres_h = mod.check_source(self.SOURCE, "x.py")
        pres_n = mod.check_source(self.CONTROL, "x.py")
        ref_h = mod.spec_ref_violations_in_source(self.SOURCE, "x.py")
        ref_n = mod.spec_ref_violations_in_source(self.CONTROL, "x.py")
        assert [(x.line, x.missing) for x in pres_h] == \
               [(x.line, x.missing) for x in pres_n]
        assert [(x.line, x.missing) for x in ref_h] == \
               [(x.line, x.missing) for x in ref_n]

    def test_sole_plumbing_ctor_still_skipped(self, mod: object) -> None:
        # Guard against over-correction: a real one-ctor helper (append arg with
        # a threaded, unresolvable spec_ref) must remain skipped by both the
        # presence and the spec_ref pass.
        src = (
            "class C:\n"
            "    def _error(self, node, description, *, rationale='', spec_ref=''):\n"
            "        self.errors.append(Diagnostic(\n"
            "            description=description, location=loc,\n"
            "            rationale=rationale, fix='f', spec_ref=spec_ref))\n"
        )
        assert mod.check_source(src, "vera/checker/core.py") == []
        assert mod.spec_ref_violations_in_source(src, "vera/checker/core.py") == []


class TestPlumbingSkipRequiresMethod:
    """#827: the plumbing-skip keyed on the function NAME, so a NON-helper
    *module-level* function coincidentally named ``_error`` / ``_warning`` with a
    single ``Diagnostic(...)`` was silently skipped — re-opening the
    under-reporting path this gate closes.  The skip now also requires a genuine
    helper *method* (a class member with a ``self`` receiver): every real
    ``_error`` / ``_warning`` helper (codegen/checker/verifier) is one, so a
    module-level look-alike is inspected, not exempted."""

    def test_module_level_error_lookalike_is_flagged(self, mod: object) -> None:
        # #827's exact repro: a module-level `_error` returning an incomplete
        # Diagnostic must NOT be exempted just because it's named `_error`.
        src = (
            "def _error(node, description):\n"
            "    return Diagnostic(description=description)\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}
        assert "Diagnostic(" in (v[0].snippet or "")

    def test_module_level_warning_lookalike_is_flagged(self, mod: object) -> None:
        # Same for a module-level `_warning` (warnings are fix-exempt, so the
        # missing set is rationale + spec_ref).
        src = (
            "def _warning(node, description):\n"
            "    return Diagnostic(description=description, severity='warning')\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "spec_ref"}

    def test_nested_scope_ctor_not_attributed_to_helper(self, mod: object) -> None:
        # A Diagnostic in a NESTED def inside the helper must NOT be counted
        # among the helper's own ctors — else the helper looks ambiguous (2
        # ctors) and its OWN legit plumbing ctor gets wrongly inspected.  This
        # codegen helper's own append omits fix/spec_ref (legit: the codegen
        # E699 structural exemption), and the nested return is fully tagged.
        # With the old `ast.walk`, the nested return pushed the count to 2,
        # un-skipped the outer ctor, and FALSELY flagged it for the missing
        # fix/spec_ref — so this assertion goes RED without the fix.
        src = (
            "class C:\n"
            "    def _error(self, node, description, *, rationale='', error_code=''):\n"
            "        def _inner():\n"
            "            return Diagnostic(description='nested', rationale='r',\n"
            "                              fix='f', spec_ref='Ch1')\n"
            "        self.diagnostics.append(Diagnostic(description=description,\n"
            "            rationale=rationale, error_code=error_code))\n"
        )
        assert mod.check_source(src, "vera/codegen/core.py") == []

    def test_real_helper_method_still_skipped(self, mod: object) -> None:
        # The contrast case: a genuine helper *method* (self receiver) threading
        # its fields from params is still plumbing and stays skipped.
        src = (
            "class C:\n"
            "    def _error(self, node, description, *, rationale='', fix='',\n"
            "               spec_ref=''):\n"
            "        return Diagnostic(description=description, rationale=rationale,\n"
            "                          fix=fix, spec_ref=spec_ref)\n"
        )
        assert mod.check_source(src, "vera/checker/core.py") == []

    def test_staticmethod_lookalike_is_flagged(self, mod: object) -> None:
        # `self` as the first parameter of a @staticmethod is an ordinary
        # positional, not a receiver — one keystroke from the module-level
        # look-alike above, and it must be inspected for the same reason.
        src = (
            "class C:\n"
            "    @staticmethod\n"
            "    def _error(self, node, description):\n"
            "        return Diagnostic(description=description)\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_positional_only_self_receiver_is_still_a_helper(self, mod: object) -> None:
        # `def _error(self, /, node)` puts `self` in `fn.args.posonlyargs`, NOT in
        # `fn.args.args`.  Reading only `args` would miss the receiver, treat a
        # real helper as a look-alike, and inspect its threaded plumbing ctor —
        # a false positive on `spec_ref is not a string literal`.
        #
        # Fail-closed rather than an escape, which is why nothing caught it:
        # dropping `posonlyargs` was the one mutant to survive the whole battery.
        src = (
            "class C:\n"
            "    def _error(self, /, node, description, *, rationale='', fix='',\n"
            "               spec_ref=''):\n"
            "        return Diagnostic(description=description, rationale=rationale,\n"
            "                          fix=fix, spec_ref=spec_ref)\n"
        )
        f = "vera/checker/core.py"
        assert mod.check_source(src, f) == []
        assert mod.spec_ref_violations_in_source(src, f) == []

    def test_class_member_without_self_receiver_is_flagged(self, mod: object) -> None:
        # Pins the `self`-receiver conjunct ON ITS OWN.  This `def _error` IS a
        # direct class-body member and carries no decorator, so `class_methods`
        # and `_not_an_instance_method` both wave it through — only the receiver
        # name distinguishes it from a real helper.
        #
        # Why it needs its own test: mutating the whole of `_is_helper_method` to
        # `return True` breaks the class-member guard too, so the module-level
        # look-alike test reddens and the suite reports "killed" while the
        # receiver check stays unexercised.  Dropping ONLY
        # `params[0].arg == "self"` was a mutant that survived all 64 tests, and
        # under it this source drops from 1 violation to 0 (PR #952 review).
        src = (
            "class C:\n"
            "    def _error(cls, node, description):\n"
            "        return Diagnostic(description=description)\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1, [(x.line, x.missing) for x in v]
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_classmethod_lookalike_is_flagged(self, mod: object) -> None:
        # `@classmethod` binds to the class, so a first parameter named `self` is
        # not an instance receiver.  (Ordinarily it would be `cls`, which the
        # `self` check already rejects — this pins the decorator half.)
        src = (
            "class C:\n"
            "    @classmethod\n"
            "    def _error(self, node, description):\n"
            "        return Diagnostic(description=description)\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_dotted_staticmethod_lookalike_is_flagged(self, mod: object) -> None:
        # `@builtins.staticmethod` is an `ast.Attribute`, not an `ast.Name` — a
        # decorator check matching only the bare name would exempt it.
        src = (
            "class C:\n"
            "    @builtins.staticmethod\n"
            "    def _error(self, node, description):\n"
            "        return Diagnostic(description=description)\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_def_nested_inside_a_method_is_not_a_class_member(self, mod: object) -> None:
        # `_class_scoped_functions` elects only *direct* members of a class body.
        # A `def _error(self, ...)` nested inside a method is a local function,
        # not a bound method, so it is inspected — even though it is lexically
        # inside the `class` statement and names its first parameter `self`.
        #
        # Pins the scoping: relaxing the election to `ast.walk(class_node)` (the
        # natural-looking widening) makes this nested def a "class member", elects
        # its ctor as plumbing, and lets an under-tagged Diagnostic through — a
        # mutant that survived the rest of the suite (PR #952 review).
        src = (
            "class C:\n"
            "    def check(self, node):\n"
            "        def _error(self, description):\n"
            "            return Diagnostic(description=description)\n"
            "        return _error(self, 'd')\n"
        )
        v = mod.check_source(src, "vera/foo.py")
        assert len(v) == 1, [(x.line, x.missing) for x in v]
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}


class TestPlumbingSkipCountsEveryOwnScopeCtor:
    """The ambiguity guard counts **every** ``Diagnostic(...)`` in the helper's
    own scope, not only the one structurally ``return``ed or ``.append(...)``-ed.

    #827's fault class is a *stray* ctor living alongside the helper's real one.
    A rule that recognised only the return/append shape would miss a helper whose
    real construction is bound to a local first (``d = Diagnostic(...)``, then
    ``self.errors.append(d)``): the stray would be the lone *recognised*
    construction, be elected as "the helper's own", and get skipped — re-opening
    the very hole this gate closes.  #827 named counting-all as its second
    suggested option; these tests pin it in both directions.

    The escape is not hypothetical: with the return/append rule, ``check_source``
    on ``test_local_bound_real_ctor_elects_no_stray``'s source returns **zero**
    violations."""

    # A helper whose real ctor is bound to a local, plus ONE stray direct ctor.
    # Return-form stray: it is the only `return Diagnostic(...)` in the body.
    STRAY_RETURN = (
        "class C:\n"
        "    def _error(self, node, description, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        if node is None:\n"
        "            return Diagnostic(description='stray', fix='f',\n"
        "                              spec_ref='Chapter 4, Section 4.3 "
        '"Slot References"\')\n'
        "        d = Diagnostic(description=description, rationale=rationale,\n"
        "                       fix=fix, spec_ref=spec_ref)\n"
        "        self.errors.append(d)\n"
    )

    # Append-form stray carrying a bogus spec_ref AND an unregistered code, so
    # all three passes have something to find on the SAME node.
    STRAY_APPEND = (
        "class C:\n"
        "    def _error(self, node, description, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        self.errors.append(Diagnostic(description='stray',\n"
        "            spec_ref='Chapter 99, Section 99.1 \"Nope\"',\n"
        "            error_code='E9999'))\n"
        "        d = Diagnostic(description=description, rationale=rationale,\n"
        "                       fix=fix, spec_ref=spec_ref)\n"
        "        return d\n"
    )

    def test_local_bound_real_ctor_elects_no_stray(self, mod: object) -> None:
        # Two own-scope ctors → ambiguous → skip neither.  The stray (missing
        # `rationale`) is caught by the presence pass.  Under a return/append
        # rule the stray is the lone *recognised* ctor, gets elected as the
        # helper's plumbing, and this returns [] — the #827 escape.
        v = mod.check_source(self.STRAY_RETURN, "vera/checker/core.py")
        assert len(v) == 1, [(x.line, x.missing) for x in v]
        assert set(v[0].missing) == {"rationale"}
        assert "stray" in (v[0].snippet or "")

    def test_ambiguous_helper_inspects_its_own_ctor_too(self, mod: object) -> None:
        # The deliberate consequence of "ambiguous → skip neither": the helper's
        # *legit* local-bound ctor is inspected as well, and its threaded
        # `spec_ref=spec_ref` trips "not a string literal".  Loud, not silent —
        # the author must disambiguate the helper.  Pinned so a future widening
        # of the skip cannot quietly re-exempt it.
        v = mod.spec_ref_violations_in_source(
            self.STRAY_RETURN, "vera/checker/core.py")
        assert len(v) == 1
        assert "not a string literal" in v[0].missing[0]
        assert "spec_ref=spec_ref" in (v[0].snippet or "")

    def test_stray_append_caught_by_all_three_passes(self, mod: object) -> None:
        f = "vera/checker/core.py"
        pres = mod.check_source(self.STRAY_APPEND, f)
        refs = mod.spec_ref_violations_in_source(self.STRAY_APPEND, f)
        codes = mod.error_code_registration_violations_in_source(
            self.STRAY_APPEND, f, {"E130"})
        assert len(pres) == 1 and set(pres[0].missing) == {"rationale", "fix"}
        # Two spec_ref hits: the stray's bogus literal, plus the un-skipped legit
        # ctor's threaded value (see test_ambiguous_helper_inspects_its_own_ctor).
        bogus = [v for v in refs if "§99.1" in v.missing[0]]
        assert len(refs) == 2 and len(bogus) == 1
        assert len(codes) == 1 and "E9999" in codes[0].missing[0]

    def test_lone_local_bound_ctor_is_still_skipped(self, mod: object) -> None:
        # The other direction — no false positive.  A helper whose SOLE own-scope
        # ctor happens to be bound to a local is still plumbing.  Under a
        # return/append rule this hoist-to-a-local refactor turns the gate RED on
        # `spec_ref is not a string literal`, whose suggested fix ("make it a
        # literal") is impossible: it is a parameter.
        src = (
            "class C:\n"
            "    def _error(self, node, description, rationale='', fix='',\n"
            "               spec_ref=''):\n"
            "        d = Diagnostic(description=description, rationale=rationale,\n"
            "                       fix=fix, spec_ref=spec_ref)\n"
            "        self.errors.append(d)\n"
        )
        f = "vera/checker/core.py"
        assert mod.check_source(src, f) == []
        assert mod.spec_ref_violations_in_source(src, f) == []


class TestPlumbingSkipRequiresReachability:
    """The skip additionally requires the helper's sole own-scope ctor to be
    reachable as the helper's *result* — return-ed, appended, or bound to a
    local that is later return-ed/appended (#956).

    A ctor merely constructed and handed to something else (e.g. dispatched
    via a bound attribute) is not plumbing: nothing threads its literal
    fields through a call site, so it must be inspected.  Before this fix,
    "sole own-scope construction" alone was sufficient to elect a ctor as
    plumbing, so a helper that builds a ``Diagnostic`` and hands it to
    ``self.dispatch(...)`` (never returning or appending it) escaped every
    pass despite carrying a bogus ``spec_ref`` and an unregistered
    ``error_code``."""

    F = "vera/checker/core.py"

    # Sole own-scope ctor, but handed to self.dispatch — never returned or
    # appended, so never reachable as the helper's result.
    DISPATCHED_NOT_RETURNED = (
        "class C:\n"
        "    def _error(self, node, description, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        d = Diagnostic(description=description, rationale='ok',\n"
        "                       fix='ok',\n"
        '                       spec_ref=\'Chapter 99, Section 99.1 "Nope"\',\n'
        "                       error_code='E9999')\n"
        "        self.dispatch(d)\n"
    )

    # Control: identical fields, but appended — the legitimately-exempt shape.
    # This is the mutation-kill for the reachability rule: a neutered
    # `_ctor_is_reachable_as_result` that always returns True must fail
    # `test_dispatched_ctor_is_inspected_not_skipped` below while this test
    # keeps passing either way.
    APPENDED = (
        "class C:\n"
        "    def _error(self, node, description, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        d = Diagnostic(description=description, rationale='ok',\n"
        "                       fix='ok',\n"
        '                       spec_ref=\'Chapter 99, Section 99.1 "Nope"\',\n'
        "                       error_code='E9999')\n"
        "        self.errors.append(d)\n"
    )

    def test_check_source_stays_clean_all_fields_literal_present(
            self, mod: object) -> None:
        # Presence pass stays clean regardless: every field is a non-empty
        # string literal.  The reachability rule only affects spec_ref/
        # error_code validity, not field presence.
        assert mod.check_source(self.DISPATCHED_NOT_RETURNED, self.F) == []

    def test_dispatched_ctor_is_inspected_not_skipped(self, mod: object) -> None:
        refs = mod.spec_ref_violations_in_source(
            self.DISPATCHED_NOT_RETURNED, self.F)
        assert len(refs) == 1
        assert "§99.1" in refs[0].missing[0]

        codes = mod.error_code_registration_violations_in_source(
            self.DISPATCHED_NOT_RETURNED, self.F, {"E130"})
        assert len(codes) == 1
        assert "E9999" in codes[0].missing[0]

    def test_appended_control_stays_exempt(self, mod: object) -> None:
        assert mod.check_source(self.APPENDED, self.F) == []
        assert mod.spec_ref_violations_in_source(self.APPENDED, self.F) == []
        assert mod.error_code_registration_violations_in_source(
            self.APPENDED, self.F, {"E130"}) == []

    # A ctor bound to a local that is later REASSIGNED before the return: the
    # name-based check has no real data-flow, so on its own it cannot tell
    # that `d` no longer holds the ctor by the time it's returned.  Being
    # conservative (not exempting whenever the name is reassigned at all)
    # keeps a genuinely swapped-out ctor from silently escaping as plumbing.
    REASSIGNED_BEFORE_RETURN = (
        "class C:\n"
        "    def _error(self, node, description, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        d = Diagnostic(description=description, rationale='ok',\n"
        "                       fix='ok',\n"
        '                       spec_ref=\'Chapter 99, Section 99.1 "Nope"\',\n'
        "                       error_code='E9999')\n"
        "        d = self.template\n"
        "        return d\n"
    )

    def test_reassigned_local_is_not_reachable_as_result(self, mod: object) -> None:
        refs = mod.spec_ref_violations_in_source(
            self.REASSIGNED_BEFORE_RETURN, self.F)
        assert len(refs) == 1
        assert "§99.1" in refs[0].missing[0]

    # A `for` loop target rebinds the same name without being an ast.Assign —
    # a plain-Assign-only rebind check misses this and would still treat the
    # name as reachable via the trailing `return d`.
    REBOUND_VIA_FOR_LOOP = (
        "class C:\n"
        "    def _error(self, node, description, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        d = Diagnostic(description=description, rationale='ok',\n"
        "                       fix='ok',\n"
        '                       spec_ref=\'Chapter 99, Section 99.1 "Nope"\',\n'
        "                       error_code='E9999')\n"
        "        for d in ():\n"
        "            pass\n"
        "        return d\n"
    )

    def test_for_loop_rebound_local_is_not_reachable_as_result(
            self, mod: object) -> None:
        refs = mod.spec_ref_violations_in_source(
            self.REBOUND_VIA_FOR_LOOP, self.F)
        assert len(refs) == 1
        assert "§99.1" in refs[0].missing[0]


class TestOwnScopeExcludesEnclosingScopeExpressions:
    """"Own scope" means the helper's ``body`` — not everything hanging off its
    ``FunctionDef`` node.

    ``ast.iter_child_nodes(fn)`` also yields ``decorator_list``, the ``arguments``
    node (carrying parameter defaults) and the ``returns`` annotation.  All three
    are evaluated in the *enclosing* scope, so a ``Diagnostic(...)`` written there
    is not the helper's plumbing.  Seeding the walk from ``iter_child_nodes``
    swept them in, and where the helper had **no body ctor** the intruder became
    the *sole* candidate — elected as the helper's plumbing and skipped by all
    three passes.  An under-tagged diagnostic then escaped the gate entirely
    (PR #952 review; ``main`` and the pre-fix PR both caught these shapes).

    The escape was invisible to the whole-``vera/`` exempt-set differential,
    because no real helper is decorated with a ``Diagnostic``-bearing decorator.
    A gate must be probed with the code it will one day see, not only the code
    it sees today.
    """

    F = "vera/checker/core.py"
    GOOD_REF = 'Chapter 4, Section 4.3 "Slot References"'

    def test_decorator_arg_ctor_is_not_the_helpers_plumbing(self, mod: object) -> None:
        # A decorator expression runs in the CLASS BODY, before `_error` exists.
        # Its Diagnostic must be inspected, never elected as the helper's own.
        src = (
            "class C:\n"
            "    @memo(fallback=Diagnostic(description='in a decorator'))\n"
            "    def _error(self, node, description):\n"
            "        self.errors.append(self._build(description))\n"
        )
        v = mod.check_source(src, self.F)
        assert len(v) == 1, [(x.line, x.missing) for x in v]
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}
        assert "@memo(" in (v[0].snippet or "")

    def test_param_default_ctor_is_not_the_helpers_plumbing(self, mod: object) -> None:
        # Parameter defaults are evaluated once, at def time, in the enclosing
        # scope — same argument as the decorator.
        src = (
            "class C:\n"
            "    def _error(self, node, tpl=Diagnostic(description='in a default')):\n"
            "        self.errors.append(self._build(tpl))\n"
        )
        v = mod.check_source(src, self.F)
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_return_annotation_ctor_is_not_the_helpers_plumbing(self, mod: object) -> None:
        # `returns` is likewise an enclosing-scope expression node.
        src = (
            "class C:\n"
            "    def _error(self, node) -> Diagnostic(description='in an annotation'):\n"
            "        self.errors.append(self._build(node))\n"
        )
        v = mod.check_source(src, self.F)
        assert len(v) == 1
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}

    def test_decorated_helper_still_skips_its_real_plumbing_ctor(self, mod: object) -> None:
        # The other direction: a decorator ctor must not inflate the count and
        # un-skip the helper's genuine, threaded plumbing construction.  Here the
        # decorator's Diagnostic is fully tagged, so the only way this can report
        # a violation is if the body ctor was wrongly inspected.
        src = (
            "class C:\n"
            "    @memo(fallback=Diagnostic(description='d', rationale='r', fix='f',\n"
            f"                              spec_ref='{self.GOOD_REF}'))\n"
            "    def _error(self, node, description, *, rationale='', fix='',\n"
            "               spec_ref=''):\n"
            "        self.errors.append(Diagnostic(description=description,\n"
            "            rationale=rationale, fix=fix, spec_ref=spec_ref))\n"
        )
        assert mod.check_source(src, self.F) == []
        assert mod.spec_ref_violations_in_source(src, self.F) == []


class TestSkipWiringPinnedInAllThreePasses:
    """The skip is consumed by three passes; each must apply it to the elected
    plumbing ctor **and to that ctor only**.

    The three predicates the skip is built from are pinned elsewhere.  What this
    class pins is the *wiring*: that each consumer actually consults the set,
    per-node.  Coarsening any consumer's ``node in plumbing`` to a file-wide
    ``if plumbing:`` is a non-equivalent mutant that survives every other test in
    this module, because no other fixture builds a source where the skip *fires*
    for a real helper while an independent under-tagged ``Diagnostic(...)`` exists
    elsewhere in the same file (CLAUDE.md: "green with it does not prove added
    code does anything").

    A related mutant — reverting the error_code pass to ``main``'s name-span skip
    — is *not* caught here (this fixture's under-tagged ctors live outside the
    helper's span, which a name-span skip would not exempt either).  It is caught
    by ``TestPlumbingSkipCountsEveryOwnScopeCtor``'s stray-inside-the-helper
    fixture, which is the only test in the module that kills it."""

    SRC = (
        "class C:\n"
        "    def _error(self, node, description, *, rationale='', fix='',\n"
        "               spec_ref=''):\n"
        "        self.errors.append(Diagnostic(description=description,\n"
        "            rationale=rationale, fix=fix, spec_ref=spec_ref))\n"
        "\n"
        "    def check(self, node):\n"
        "        self.errors.append(Diagnostic(description='independent'))\n"
        "        self.errors.append(Diagnostic(description='bad', rationale='r',\n"
        "            fix='f', spec_ref='Chapter 99, Section 99.1 \"Nope\"',\n"
        "            error_code='E9999'))\n"
    )
    F = "vera/checker/core.py"

    def test_presence_pass_skips_only_the_plumbing_ctor(self, mod: object) -> None:
        v = mod.check_source(self.SRC, self.F)
        assert len(v) == 1, [(x.line, x.missing) for x in v]
        assert set(v[0].missing) == {"rationale", "fix", "spec_ref"}
        assert "independent" in (v[0].snippet or "")

    def test_spec_ref_pass_skips_only_the_plumbing_ctor(self, mod: object) -> None:
        # The helper's threaded `spec_ref=spec_ref` must stay exempt while the
        # sibling's bogus literal is flagged.
        v = mod.spec_ref_violations_in_source(self.SRC, self.F)
        assert len(v) == 1 and "§99.1" in v[0].missing[0]

    def test_error_code_pass_skips_only_the_plumbing_ctor(self, mod: object) -> None:
        v = mod.error_code_registration_violations_in_source(
            self.SRC, self.F, {"E130"})
        assert len(v) == 1 and "E9999" in v[0].missing[0]


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

    def test_section_under_wrong_chapter_flagged(self, mod: object) -> None:
        # §4.4 is real and the title matches, but it lives in Chapter 4, not 5.
        v = self._v(mod, 'Chapter 5, Section 4.4 "Arithmetic Expressions"')
        assert len(v) == 1 and "not in Chapter 5" in v[0].missing[0]

    def test_unrecognised_format_flagged(self, mod: object) -> None:
        v = self._v(mod, 'see the spec please')
        assert len(v) == 1 and "unrecognised" in v[0].missing[0]

    def test_chapter_only_wrong_title_flagged(self, mod: object) -> None:
        # Chapter 6 exists but is "Contracts", not "Wibble".
        v = self._v(mod, 'Chapter 6, "Wibble"')
        assert len(v) == 1 and "Contracts" in v[0].missing[0]

    def test_valid_multi_section_ref_passes(self, mod: object) -> None:
        # A spec_ref may cite two sections (this is a real shape in verifier.py).
        # Both citations are correct, so it must pass.
        assert self._v(
            mod,
            'Chapter 4, Section 4.7 "Let Bindings" and '
            'Chapter 11, Section 11.2.1 "Nat as i64"') == []

    def test_wrong_second_citation_flagged(self, mod: object) -> None:
        # First citation correct, SECOND bogus — must NOT ship silently
        # (`.search()` would only have validated the first).
        v = self._v(
            mod,
            'Chapter 4, Section 4.7 "Let Bindings" and '
            'Chapter 11, Section 11.9999 "Bogus"')
        assert len(v) == 1 and "11.9999" in v[0].missing[0]

    def test_garbage_around_citation_rejected(self, mod: object) -> None:
        # `.search()` tolerates a non-citation prefix; the residue check rejects it.
        v = self._v(mod, 'LIES Chapter 4, Section 4.4 "Arithmetic Expressions"')
        assert len(v) == 1 and "unrecognised text" in v[0].missing[0]

    def test_non_literal_spec_ref_flagged(self, mod: object) -> None:
        # A spec_ref threaded through a variable passes the *presence* check
        # (any non-constant counts as present) but cannot be validated against
        # the spec — it must be flagged, mirroring the non-literal-severity rule.
        src = "self._error(node, 'd', spec_ref=COMMON_REF)\n"
        v = mod.spec_ref_violations_in_source(src, "vera/checker/x.py")
        assert len(v) == 1 and "not a string literal" in v[0].missing[0]

    def test_plumbing_spec_ref_skipped(self, mod: object) -> None:
        # The Diagnostic() construction *inside* an _error helper is plumbing,
        # not a site, and the validity pass must skip it.  Use a LITERAL but
        # INVALID spec_ref so this assertion goes RED whenever the helper-skip
        # is removed — via the literal validity path, INDEPENDENT of the
        # (co-shipped) non-literal-flagging code.  (A threaded `spec_ref=spec_ref`
        # would only flip red if the non-literal path were also present, so the
        # two fixes would mask each other — the "green before and after" trap.)
        src_literal = (
            "class C:\n"
            "    def _error(self, node, description, *, spec_ref=''):\n"
            "        self.diagnostics.append(Diagnostic(\n"
            "            description=description, location=loc,\n"
            "            spec_ref='Chapter 99, \"Nope\"'))\n"
        )
        assert mod.spec_ref_violations_in_source(
            src_literal, "vera/checker/core.py") == []
        # The original threaded-param (non-literal) shape is also skipped.
        src_threaded = (
            "class C:\n"
            "    def _error(self, node, description, *, spec_ref=''):\n"
            "        self.diagnostics.append(Diagnostic(\n"
            "            description=description, location=loc,\n"
            "            spec_ref=spec_ref))\n"
        )
        assert mod.spec_ref_violations_in_source(
            src_threaded, "vera/checker/core.py") == []


# =====================================================================
# error_code registration: every literal code must be in ERROR_CODES (#828)
# =====================================================================

class TestErrorCodeRegistration:
    REG = {"E130", "E216", "W001"}

    def test_unregistered_literal_flagged(self, mod: object) -> None:
        src = "self._error(node, 'd', error_code='E999')\n"
        v = mod.error_code_registration_violations_in_source(
            src, "vera/checker/x.py", self.REG)
        assert len(v) == 1 and "E999" in v[0].missing[0]

    def test_registered_literal_passes(self, mod: object) -> None:
        src = "self._error(node, 'd', error_code='E130')\n"
        assert mod.error_code_registration_violations_in_source(
            src, "vera/checker/x.py", self.REG) == []

    def test_non_literal_code_skipped(self, mod: object) -> None:
        # A threaded error_code (variable) cannot be checked statically.
        src = "self._error(node, 'd', error_code=code)\n"
        assert mod.error_code_registration_violations_in_source(
            src, "vera/checker/x.py", self.REG) == []

    def test_plumbing_literal_code_skipped(self, mod: object) -> None:
        # A literal code inside an _error helper def is plumbing, not a site.
        src = (
            "class C:\n"
            "    def _error(self, node, *, error_code=''):\n"
            "        self.diagnostics.append(Diagnostic(\n"
            "            description='d', location=loc, error_code='E999'))\n"
        )
        assert mod.error_code_registration_violations_in_source(
            src, "vera/checker/core.py", self.REG) == []

    def test_load_error_codes_reads_live_registry(self, mod: object) -> None:
        codes = mod._load_error_codes(ROOT / "vera" / "errors.py")
        assert {"E130", "E618", "W001", "E002"} <= codes
        assert "E999" not in codes


# =====================================================================
# _load_spec caches per resolved spec_dir
# =====================================================================

class TestSpecDirCache:
    def test_cache_is_per_spec_dir(self, mod: object, tmp_path: Path) -> None:
        """A later call with a different spec_dir must validate against that
        directory's files, not reuse an earlier directory's cached map."""
        ref = 'Chapter 4, Section 4.4 "Arithmetic Expressions"'
        src = f"self._error(node, 'd', spec_ref='{ref}')\n"

        d1 = tmp_path / "spec_a"
        d1.mkdir()
        (d1 / "04-x.md").write_text(
            "# Chapter 4: Expressions\n\n### 4.4 Arithmetic Expressions\n",
            encoding="utf-8")
        d2 = tmp_path / "spec_b"
        d2.mkdir()
        (d2 / "04-x.md").write_text(
            "# Chapter 4: Expressions\n\n### 4.4 Something Else\n",
            encoding="utf-8")

        # Valid against d1 (title matches there)...
        assert mod.spec_ref_violations_in_source(
            src, "vera/x.py", spec_dir=d1) == []
        # ...but invalid against d2 — a shared global cache would wrongly reuse
        # d1's map here and pass.
        v = mod.spec_ref_violations_in_source(src, "vera/x.py", spec_dir=d2)
        assert len(v) == 1 and "Something Else" in v[0].missing[0]


# =====================================================================
# Integration: the live vera/ tree must be fully tagged AND every
# spec_ref must resolve to a real spec section.
# =====================================================================

class TestLiveTree:
    def test_live_vera_tree_is_clean(self, mod: object) -> None:
        files = mod.iter_vera_files(ROOT / "vera")
        registry = mod._load_error_codes(ROOT / "vera" / "errors.py")
        violations = (mod.check_paths(files)
                      + mod.spec_ref_violations(files)
                      + mod.error_code_registration_violations(files, registry))
        report = "\n".join(
            f"  {v.file}:{v.line} {v.target} {v.missing}" for v in violations)
        assert violations == [], f"{len(violations)} diagnostic problem(s):\n{report}"
