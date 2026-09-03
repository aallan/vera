"""Tests for the Vera type checker — errors (error codes, resolution diagnostics, contracts, error accumulation).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

import pytest

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.checker.expressions import _SCOPE_TABLE_MAX_ROWS
from vera.parser import parse_to_ast

from tests.checker_helpers import (
    _check,
    _check_err,
    _check_ok,
    _errors,
    _warnings,
)


# =====================================================================
# Error code tests
# =====================================================================

class TestErrorCodes:
    """Verify that diagnostics carry stable error codes."""

    def test_error_code_in_format_output(self) -> None:
        """Error codes appear in formatted diagnostic output."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
            error_code="E130",
        )
        formatted = d.format()
        assert "[E130]" in formatted

    def test_error_code_in_json_output(self) -> None:
        """Error codes appear in to_dict() JSON output."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
            error_code="E130",
        )
        data = d.to_dict()
        assert data["error_code"] == "E130"

    def test_no_error_code_omitted_from_format(self) -> None:
        """Diagnostics without codes don't show empty brackets."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
        )
        formatted = d.format()
        assert "[" not in formatted.split("\n")[0]

    def test_no_error_code_omitted_from_json(self) -> None:
        """Diagnostics without codes don't include error_code in JSON."""
        from vera.errors import Diagnostic, SourceLocation
        d = Diagnostic(
            description="test error",
            location=SourceLocation(line=1, column=1),
        )
        data = d.to_dict()
        assert "error_code" not in data

    def test_error_codes_registry_format_and_size(self) -> None:
        """Every code in ERROR_CODES matches the Exxx/Wxxx pattern.

        Does NOT assert key uniqueness — `ERROR_CODES` is a `dict`, so
        its keys are unique by construction and iterating them can
        never find a duplicate; that used to be exactly what this test
        asserted, so the check could never fail (#828). The property
        that actually needs enforcing — one code emitted by exactly
        one diagnostic CONCEPT, not just one dict entry — is a
        source-level question `ERROR_CODES` alone cannot answer, and
        is covered by `test_error_code_collision_gate_is_clean` below
        via `scripts/check_diagnostic_fields.py`.
        """
        import re
        from vera.errors import ERROR_CODES
        pattern = re.compile(r"^[EW]\d{3}$")
        for code in ERROR_CODES:
            assert pattern.match(code), f"Invalid code format: {code}"
        assert len(ERROR_CODES) >= 70  # sanity: we defined ~80 codes

    def test_error_code_collision_gate_is_clean(self) -> None:
        """The MEANINGFUL uniqueness property: no error_code is emitted
        from more than one distinct (file, function) site unless that
        exact site set is declared (and human-verified) in
        `scripts/check_diagnostic_fields.py`'s
        `KNOWN_MULTI_SITE_ERROR_CODES` — the collision shape that let
        E130/E210/E320/E600 each mean two unrelated things before
        #682's manual audit caught them (#828)."""
        import importlib.util
        import sys
        from pathlib import Path

        root = Path(__file__).resolve().parent.parent
        script_path = root / "scripts" / "check_diagnostic_fields.py"
        spec = importlib.util.spec_from_file_location(
            "check_diagnostic_fields", script_path)
        assert spec is not None and spec.loader is not None
        mod = importlib.util.module_from_spec(spec)
        sys.modules.setdefault("check_diagnostic_fields", mod)
        spec.loader.exec_module(mod)

        files = mod.iter_vera_files(root / "vera")
        violations = mod.error_code_collision_violations(files)
        report = "\n".join(
            f"  {v.file}:{v.line} {v.missing[0]}" for v in violations)
        assert violations == [], f"{len(violations)} collision(s):\n{report}"

    def test_slot_ref_error_has_code_E130(self) -> None:
        """Unresolved slot reference produces E130."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E130" for d in diags)

    def test_decimal_type_args_is_E134_not_E130(self) -> None:
        """`Decimal<...>` (a non-generic type given type arguments) is E134 —
        distinct from the E130 slot-resolution error it previously collided
        with (#826).  The `not E130` assertion is the collision-regression."""
        src = """\
private fn f(@Decimal<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E134" for d in diags)
        assert not any(d.error_code == "E130" for d in diags)

    def test_empty_tuple_is_E216_not_E210(self) -> None:
        """`Tuple()` with no fields is E216 — distinct from the E210
        unknown-constructor error it previously collided with (#826)."""
        src = """\
private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ let @Tuple = Tuple(); 0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E216" for d in diags)
        assert not any(d.error_code == "E210" for d in diags)

    def test_body_type_mismatch_has_code_E121(self) -> None:
        """Function body type mismatch produces E121."""
        src = """\
private fn f(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E121" for d in diags)

    def test_if_condition_not_bool_has_code_E300(self) -> None:
        """If condition not Bool produces E300."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ if @Int.0 then { 1 } else { 0 } }
"""
        diags = _errors(src)
        assert any(d.error_code == "E300" for d in diags)

    def test_unresolved_function_has_code_E200(self) -> None:
        """Unresolved function produces E200 (warning)."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ unknown_fn(@Int.0) }
"""
        diags = _check(src)
        assert any(d.error_code == "E200" for d in diags)

    def test_requires_not_bool_has_code_E123(self) -> None:
        """requires() with non-Bool predicate produces E123."""
        src = """\
private fn f(@Int -> @Int)
  requires(@Int.0) ensures(true) effects(pure)
{ @Int.0 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E123" for d in diags)

    def test_let_binding_mismatch_has_code_E170(self) -> None:
        """Let binding type mismatch produces E170."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = @Int.0;
  @Int.0
}
"""
        diags = _errors(src)
        assert any(d.error_code == "E170" for d in diags)

    def test_assert_not_bool_has_code_E172(self) -> None:
        """assert() with non-Bool produces E172."""
        src = """\
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  assert(@Int.0);
  @Int.0
}
"""
        diags = _errors(src)
        assert any(d.error_code == "E172" for d in diags)

    def test_arithmetic_non_numeric_has_code_E140(self) -> None:
        """Arithmetic on non-numeric produces E140."""
        src = """\
private fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 + 1 }
"""
        diags = _errors(src)
        assert any(d.error_code == "E140" for d in diags)

    def test_E140_carries_a_fix_paragraph_682(self) -> None:
        """#682 AC5: the operator-type-mismatch diagnostic (E140) must
        carry a concrete `Fix:` paragraph, not just a description +
        rationale — this is the canonical example from the issue."""
        src = """\
private fn f(@Bool, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Bool.0 + @Int.0 }
"""
        e140 = [d for d in _errors(src) if d.error_code == "E140"]
        assert e140, "expected an E140 diagnostic for `@Bool.0 + @Int.0`"
        assert e140[0].fix.strip(), "E140 must carry a non-empty fix"
        assert "Fix:" in e140[0].format()


# =====================================================================
# #558 — E130 carries the in-scope slot table
# =====================================================================


class TestSlotTableInE130:
    """#558 option (a): an unresolved-slot error lists every binding in
    scope at the error position with its resolved `@T.n`, so the right
    index can be read off the diagnostic instead of reconstructed by
    writing a typed hole and re-running.  Same rendering as the W001
    hole hint ("Available bindings: ...")."""

    @pytest.mark.parametrize("src,expected", [
        pytest.param("""\
private fn f(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.3 }
""", "Available bindings: @Int.0: Int; @Int.1: Int.",
            id="index_out_of_range"),
        pytest.param("""\
private fn f(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "Available bindings: @Bool.0: Bool.",
            id="no_binding_of_that_type"),
        pytest.param("""\
private fn f(-> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", None,
            id="empty_scope_lists_nothing"),
    ])
    def test_e130_fix_lists_scope_bindings(
        self, src: str, expected: str | None,
    ) -> None:
        e130 = [d for d in _errors(src) if d.error_code == "E130"]
        assert e130, "expected an E130 diagnostic"
        if expected is None:
            assert "Available bindings" not in e130[0].fix, \
                f"nothing is in scope, got: {e130[0].fix!r}"
        else:
            assert e130[0].fix.endswith(expected), \
                f"expected fix ending {expected!r}, got: {e130[0].fix!r}"

    def test_e130_in_match_arm_lists_arm_bindings(self) -> None:
        """The issue's motivating case: deep in a match arm the slot stack
        has grown past the signature, which is all `--explain-slots` shows.
        The arm's own binding must appear in the table alongside the
        parameter it shadows."""
        e130 = [d for d in _errors("""
private data Term { Var(Int), Abs(Term), App(Term, Term) }

private fn f(@Term -> @Int)
  requires(true) ensures(true) effects(pure)
{
  match @Term.0 {
    Var(@Int) -> 0,
    Abs(@Term) -> @Int.9,
    App(@Term, @Term) -> 0
  }
}
""") if d.error_code == "E130"]
        assert e130, "expected an E130 diagnostic in the Abs arm"
        assert "@Term.0: Term" in e130[0].fix, \
            f"arm binding missing from the table: {e130[0].fix!r}"
        assert "@Term.1: Term" in e130[0].fix, \
            f"shadowed parameter missing from the table: {e130[0].fix!r}"

    def test_e130_table_covers_the_indices_it_calls_valid(self) -> None:
        """The table and the index range in the same diagnostic must
        describe one scope.  `@Unit.1` against `(@Unit, @Int)` reports
        "valid indices: 0..0" and offers a lower index, so `@Unit.0` has
        to be in the table — omitting it makes the one diagnostic say both
        that a Unit binding exists and that none does, and the reader who
        believes the table writes a different wrong index."""
        e130 = [d for d in _errors("""\
private fn f(@Unit, @Int -> @Unit)
  requires(true) ensures(true) effects(pure)
{ @Unit.1 }
""") if d.error_code == "E130"]
        assert e130, "expected an E130 diagnostic"
        assert "valid indices: 0..0" in e130[0].description
        assert "@Unit.0: Unit" in e130[0].fix, \
            f"the index the message calls valid is not in the table: " \
            f"{e130[0].fix!r}"

    def test_e130_and_w001_tables_agree(self) -> None:
        """Same label, same scope position, so the same set: the E130 fix
        and the W001 hole hint both render `_collect_scope_bindings()`
        whole.  Two "Available bindings:" lists that disagree are worse
        than one of them not existing."""
        sig = """\
private fn f(@Unit, @Bool -> @Int)
  requires(true) ensures(true) effects(pure)
"""
        e130 = [d for d in _errors(sig + "{ @Int.0 }")
                if d.error_code == "E130"]
        w001 = [d for d in _warnings(sig + "{ ? }")
                if d.error_code == "W001"]
        assert e130 and w001, "expected both diagnostics"
        table = "Available bindings: @Bool.0: Bool; @Unit.0: Unit."
        assert e130[0].fix.endswith(table), f"E130: {e130[0].fix!r}"
        assert w001[0].fix.endswith(table), f"W001: {w001[0].fix!r}"

    def test_handler_state_hint_keeps_its_guidance_and_gains_the_table(
        self,
    ) -> None:
        """The append runs after *every* fix branch, including the two
        specialised ones, so each has to keep its tailored text.

        #973's handler-state branch fires only at count == 0, and the
        table is still worth appending there: it is what shows the reader
        that `@Unit.0` is the one thing actually in scope.  Asserting
        both halves means neither the append nor the tailored text can
        regress without a failure — a table-only assertion would stay
        green if the specialised branch were flattened to the generic
        message."""
        e130 = [d for d in _errors("""\
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) } with @Int = @Int.0
  } in {
    @Int.0
  }
}
""") if d.error_code == "E130"]
        assert e130, "expected E130 for the handler-state slot read"
        assert "get(())" in e130[0].fix, \
            f"tailored handler-state guidance lost: {e130[0].fix!r}"
        assert e130[0].fix.endswith("Available bindings: @Unit.0: Unit."), \
            f"table not appended after the handler-state fix: {e130[0].fix!r}"

    def test_where_helper_hint_keeps_its_guidance_and_gains_the_table(
        self,
    ) -> None:
        """The other specialised branch, same two-sided assertion.

        #969's where-helper branch also fires only at count == 0.  Here
        the table is the more useful half: it names the helper's own
        parameter, which is what the reader has to pass the outer value
        into."""
        e130 = [d for d in _errors("""\
private fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(true) }
where {
  fn helper(@Bool -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 }
}
""") if d.error_code == "E130"]
        assert e130, "expected E130 for the outer-slot read in the helper"
        assert "param-rooted" in e130[0].fix, \
            f"tailored where-helper guidance lost: {e130[0].fix!r}"
        assert e130[0].fix.endswith("Available bindings: @Bool.0: Bool."), \
            f"table not appended after the where-helper fix: {e130[0].fix!r}"

    def test_result_is_not_a_binding_and_stays_out_of_the_table(self) -> None:
        """SKILL.md tells the reader `@T.result` never appears in the
        table, `ensures` included.  Pin both halves of that claim, or a
        `_collect_scope_bindings()` change falsifies the docs silently.

        The table has to omit `.result` *and* `@Int.result` has to keep
        resolving: a table listing it would send the reader looking for a
        slot index that does not exist, and a `.result` that stopped
        resolving would make the sentence true for the wrong reason."""
        ensures = "ensures(@Int.result == @Int.{})"
        e130 = [d for d in _errors(f"""\
private fn f(@Int -> @Int)
  requires(true)
  {ensures.format(9)}
  effects(pure)
{{ @Int.0 }}
""") if d.error_code == "E130"]
        assert e130, "expected E130 for the out-of-range slot in ensures"
        assert ".result" not in e130[0].fix, \
            f"`.result` leaked into the table: {e130[0].fix!r}"
        assert e130[0].fix.endswith("Available bindings: @Int.0: Int."), \
            f"expected the parameter table only, got: {e130[0].fix!r}"
        # The same `ensures` with the index the table offers: `@Int.result`
        # resolves, so the omission is about what a slot binding IS, not
        # about `.result` being unavailable in `ensures`.
        _check_ok(f"""\
private fn f(@Int -> @Int)
  requires(true)
  {ensures.format(0)}
  effects(pure)
{{ @Int.0 }}
""")


# =====================================================================
# #558 — the slot table is capped
# =====================================================================


def _wide_fn(params: int, index: int) -> str:
    """A signature binding `params` Int slots, reading `@Int.index`."""
    return (
        f"private fn wide({', '.join(['@Int'] * params)} -> @Int)\n"
        f"  requires(true) ensures(true) effects(pure)\n"
        f"{{ @Int.{index} }}\n"
    )


def _table_of(fix: str) -> str:
    """The `Available bindings:` segment of a fix, without its full stop."""
    _, _, table = fix.partition("Available bindings: ")
    return table.rstrip(".")


class TestSlotTableCap:
    """The table is rendered at most `_SCOPE_TABLE_MAX_ROWS` rows wide.

    Unbounded, it grows with the scope — and the LSP concatenates the
    fix into the hover message, so a wide function turns one diagnostic
    into a wall of rows nobody reads.  The cap is one rule applied to
    the rendering, not to `_collect_scope_bindings()`: the LSP's
    typed-hole completion consumes the same set as structured data and
    must keep every row.
    """

    def test_cap_leaves_the_measured_corpus_untouched(self) -> None:
        """The cap has to sit above real scopes, not in the middle of
        them.  Measured over the 2,080 slot-reference positions in
        `tests/**/*.vera` and `examples/`, the table is 7 rows at p95 and
        11 at p99, so a cap at 12 renders every site through the 99th
        percentile complete and bites only the tail.

        Pinned by equality rather than by a floor.  Every other test in
        this class derives its expectation from the constant, so they
        follow a cap change silently; a floor here follows it too, in
        the one direction the cap exists to prevent — a raised cap
        re-widens the hover and no test in the file objects.  `== 12`
        makes moving the cap an edit to this line, with the corpus
        measurement above it to re-derive the new value from."""
        assert _SCOPE_TABLE_MAX_ROWS == 12, \
            "the cap is pinned to the corpus-derived value: at or below " \
            "the p99 (11 rows) it truncates ordinary diagnostics, and " \
            "above it the hover re-widens — re-measure, then update this pin"

    def test_table_is_complete_at_the_cap(self) -> None:
        """At exactly the cap every row is present and nothing is
        elided — the boundary belongs to the complete side."""
        n = _SCOPE_TABLE_MAX_ROWS
        e130 = [d for d in _errors(_wide_fn(n, n)) if d.error_code == "E130"]
        assert e130, "expected an E130 diagnostic"
        expected = "; ".join(f"@Int.{i}: Int" for i in range(n))
        assert e130[0].fix.endswith(f"Available bindings: {expected}."), \
            f"table not complete at the cap: {e130[0].fix!r}"
        assert "…" not in e130[0].fix, \
            f"overflow marker at the cap: {e130[0].fix!r}"

    @pytest.mark.parametrize("extra", [1, 5, 18], ids=["one", "five", "18"])
    def test_table_overflows_past_the_cap(self, extra: int) -> None:
        """One row past the cap the suffix appears, and `K` counts the
        rows the reader is not being shown — not the scope size, and not
        the cap."""
        n = _SCOPE_TABLE_MAX_ROWS + extra
        e130 = [d for d in _errors(_wide_fn(n, n)) if d.error_code == "E130"]
        assert e130, "expected an E130 diagnostic"
        shown = "; ".join(
            f"@Int.{i}: Int" for i in range(_SCOPE_TABLE_MAX_ROWS)
        )
        assert e130[0].fix.endswith(
            f"Available bindings: {shown}; … and {extra} more."), \
            f"expected {extra} rows elided, got: {e130[0].fix!r}"

    def test_every_rendered_row_still_resolves(self) -> None:
        """Truncation must drop rows off the end, never renumber the
        ones it keeps.  Take the review's measured shape — 30 same-typed
        params — and feed each rendered row back as the body: a shifted
        index would type-check to the wrong parameter, or not at all."""
        e130 = [d for d in _errors(_wide_fn(30, 99)) if d.error_code == "E130"]
        assert e130, "expected an E130 diagnostic"
        rows = _table_of(e130[0].fix).split("; ")
        assert rows[-1] == "… and 18 more", f"unexpected tail: {rows[-1]!r}"
        for row in rows[:-1]:
            ref, _, ty = row.partition(": ")
            assert ty == "Int", f"row reports the wrong type: {row!r}"
            _check_ok(
                f"private fn wide({', '.join(['@Int'] * 30)} -> @Int)\n"
                f"  requires(true) ensures(true) effects(pure)\n"
                f"{{ {ref} }}\n"
            )

    def test_e130_and_w001_agree_past_the_cap(self) -> None:
        """The two renderings share one cap for the same reason they
        share one set: a hole and an unresolved slot at the same scope
        position must not disagree about what is in scope."""
        params = ", ".join(["@Int"] * (_SCOPE_TABLE_MAX_ROWS + 3))
        sig = (f"private fn wide({params} -> @Int)\n"
               f"  requires(true) ensures(true) effects(pure)\n")
        e130 = [d for d in _errors(sig + "{ @Int.99 }")
                if d.error_code == "E130"]
        w001 = [d for d in _warnings(sig + "{ ? }")
                if d.error_code == "W001"]
        assert e130 and w001, "expected both diagnostics"
        assert _table_of(e130[0].fix) == _table_of(w001[0].fix), \
            f"E130: {e130[0].fix!r}\nW001: {w001[0].fix!r}"
        assert _table_of(e130[0].fix).endswith("… and 3 more")

    def test_completion_data_keeps_every_binding(self) -> None:
        """The cap is a rendering rule.  `_collect_scope_bindings()` feeds
        the LSP typed-hole completion (#222 Phase D) as a list, where a
        missing row is a missing completion item, so the collector itself
        stays uncapped."""
        n = _SCOPE_TABLE_MAX_ROWS + 8
        src = (
            f"private fn wide({', '.join(['@Int'] * n)} -> @Int)\n"
            f"  requires(true) ensures(true) effects(pure)\n"
            f"{{ ? }}\n"
        )
        _diags, arts = typecheck_with_artifacts(parse_to_ast(src), src)
        assert len(arts.holes) == 1, \
            f"expected one hole site, got {len(arts.holes)}"
        assert len(arts.holes[0].bindings) == n, \
            f"completion lost rows to the cap: " \
            f"{len(arts.holes[0].bindings)} of {n}"


# =====================================================================
# Resolution mixin — coverage for uncovered branches
# =====================================================================


class TestResolutionCoverage:
    """Tests targeting uncovered lines in checker/resolution.py."""

    # Line 48: _resolve_type returning UnknownType for unknown TypeExpr
    def test_resolve_type_unknown_type_expr(self) -> None:
        """Directly calling _resolve_type with an unrecognised TypeExpr
        node returns UnknownType."""
        from vera.checker.core import TypeChecker
        from vera.types import UnknownType
        from vera.environment import TypeEnv

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        # Create a TypeExpr subclass that is none of the known kinds
        bogus = ast.TypeExpr(span=None)
        result = checker._resolve_type(bogus)
        assert isinstance(result, UnknownType)

    # Lines 66-68: Type alias with type args (parameterised alias)
    def test_parameterised_type_alias(self) -> None:
        """A parameterised type alias resolves type args via substitution."""
        _check_ok("""
type Wrapper<T> = Option<T>;

private fn wrap(@Int -> @Wrapper<Int>)
  requires(true) ensures(true) effects(pure)
{ Some(@Int.0) }
""")

    def test_alias_arity_mismatch_too_few_e133(self) -> None:
        """`#660` — `vera check` rejects `@Pair<Int>` when
        `Pair<A, B>` is declared with two type parameters.

        Pre-fix the checker silently accepted this and the `zip`
        in `_resolve_type` truncated, leaving the alias body's
        `B` unsubstituted.  Downstream codegen leaked literal
        `B` into mono suffixes (`option_map$Int_JB`) → runtime
        `call_indirect` trap.  Post-fix the checker rejects with
        `[E133]` ("Type alias arity mismatch") at compile time.

        Pin both the message AND the error code so a future
        refactor that re-routes through a sibling diagnostic with
        the same text but a different code is caught.
        """
        errs = _check_err("""
type Pair<A, B> = fn(A -> B) effects(pure);

public fn main(@Pair<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""", "expects 2 type argument(s) but 1 supplied")
        e133 = [e for e in errs if e.error_code == "E133"]
        assert e133, (
            f"Expected at least one diagnostic with error_code=E133; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_alias_arity_mismatch_too_many_e133(self) -> None:
        """Symmetric case: too many type-args also rejected with E133."""
        errs = _check_err("""
type Single<T> = Option<T>;

public fn main(@Single<Int, Bool> -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
""", "expects 1 type argument(s) but 2 supplied")
        e133 = [e for e in errs if e.error_code == "E133"]
        assert e133, (
            f"Expected at least one diagnostic with error_code=E133; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_alias_zero_args_when_zero_expected_ok(self) -> None:
        """A non-parameterised alias accepts no type-args.  Pin
        the arity check doesn't false-positive on the
        zero-expected / zero-supplied case."""
        _check_ok("""
type Year = Int;

public fn current(@Unit -> @Year)
  requires(true) ensures(true) effects(pure)
{ 2026 }
""")

    # =================================================================
    # #648 — cyclic type aliases must produce [E132] at check time
    # =================================================================

    def test_cyclic_alias_two_way_e132(self) -> None:
        """`type A = B; type B = A` produces [E132] at check time
        instead of crashing codegen with RecursionError (#648).

        Also pins the diagnostic *payload* (cycle path + fix
        message) on this representative test — the other cyclic-
        alias tests below check error_code only, since the
        payload-shape contract is uniform across them.
        """
        errs = _check_err("""
type A = B;
type B = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )
        # Pin the cycle-path rendering in the description and the
        # `data`-as-alternative suggestion in the fix hint.  A
        # future refactor that changes the rendering would still
        # emit E132 but the payload contract these messages embody
        # — "you can tell *which* aliases form the cycle" and
        # "here's the alternative that supports self-reference" —
        # would silently regress without these assertions.
        assert "A -> B -> A" in e132[0].description, (
            f"Expected cycle path 'A -> B -> A' in description; "
            f"got: {e132[0].description!r}"
        )
        assert "data" in e132[0].fix, (
            f"Expected fix hint to suggest `data` as the alternative "
            f"for self-referential types; got: {e132[0].fix!r}"
        )

    def test_cyclic_alias_self_e132(self) -> None:
        """`type A = A` is the degenerate self-cycle case (#648)."""
        errs = _check_err("""
type A = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_cyclic_alias_three_way_e132(self) -> None:
        """`A -> B -> C -> A` three-way cycle also flagged (#648)."""
        errs = _check_err("""
type A = B;
type B = C;
type C = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_cyclic_alias_refinement_e132(self) -> None:
        """Cycles through a `RefinementType` wrapper (`type A = { @B
        | true }; type B = A`) also flagged.  Pins the
        `_referenced_aliases` helper's `RefinementType.base_type`
        recursion — codegen's `_type_expr_to_wasm_type` recurses
        through refinements unconditionally, so a cycle hidden
        behind one is still a codegen-crash cycle (#648)."""
        errs = _check_err("""
type A = { @B | true };
type B = A;

public fn id(@A -> @A)
  requires(true) ensures(true) effects(pure)
{
  @A.0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    # -----------------------------------------------------------------
    # #1059 — cycles buried in a type ARGUMENT.  The #648 walk followed
    # only bare `type A = B` references, so a self-reference through a
    # generic's type_arg (`Future<F>`, `Array<L>`) slipped past `check`
    # and either crashed codegen with a RecursionError (the Future
    # spellings, which `_type_expr_to_wasm_type` recurses through) or
    # compiled to a degenerate type inhabited only by `[]` (`Array<L>`).
    # The acyclicity rule (spec 2.6.3) is structural, so all cyclic
    # spellings are rejected uniformly at check time.
    # -----------------------------------------------------------------

    def test_cyclic_alias_self_through_future_arg_e132(self) -> None:
        """`type F = Future<F>` — self-reference through a `Future`
        type argument — is E132, not an admitted alias that later
        crashes `_type_expr_to_wasm_type` with RecursionError (#1059)."""
        errs = _check_err("""
type F = Future<F>;

private fn use_it(@F -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )
        assert "F -> F" in e132[0].description, (
            f"Expected cycle path 'F -> F' in description; "
            f"got: {e132[0].description!r}"
        )

    def test_cyclic_alias_mutual_through_future_arg_e132(self) -> None:
        """`type A = Future<B>; type B = Future<A>` — mutual cycle
        threaded through `Future` type arguments — is E132 (#1059)."""
        errs = _check_err("""
type A = Future<B>;
type B = Future<A>;

private fn use_it(@A -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )
        assert "A -> B -> A" in e132[0].description, (
            f"Expected cycle path 'A -> B -> A' in description; "
            f"got: {e132[0].description!r}"
        )

    def test_cyclic_alias_self_through_array_arg_e132(self) -> None:
        """`type L = Array<L>` — self-reference through an `Array` type
        argument — is E132 (#1059).  `Array<L>` does not crash codegen
        (it stops at an i32_pair) and is inhabited by `[]`, but the
        acyclicity rule is structural, so it is rejected uniformly
        with the `Future` spellings."""
        errs = _check_err("""
type L = Array<L>;

private fn use_it(@L -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )

    def test_cyclic_alias_nested_compound_type_arg_e132(self) -> None:
        """`type A = Future<Array<B>>; type B = A` — the cycle edge sits
        two compound levels deep (a type argument OF a type argument),
        so the reference walk must descend the full nesting, not one
        level (#1059, PR #1066 review)."""
        errs = _check_err("""
type A = Future<Array<B>>;
type B = A;

private fn use_it(@A -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )
        assert "A -> B -> A" in e132[0].description, (
            f"Expected cycle path 'A -> B -> A' in description; "
            f"got: {e132[0].description!r}"
        )

    def test_alias_chain_deep_worst_case_order_checks(self) -> None:
        """A 1,500-alias LEGAL chain declared deepest-first must check
        clean.  The cycle DFS visits an unexplored predecessor per hop
        before anything is marked safe, so with recursive traversal this
        input overflowed Python's call stack — a checker crash
        (RecursionError) on valid input, the acyclic sibling of the
        #1059 crash (PR #1066 review).  The explicit-stack DFS bounds it
        by memory instead."""
        n = 1500
        decls = "\n".join(f"type A{i} = A{i - 1};" for i in range(n - 1, 0, -1))
        _check_ok(decls + "\ntype A0 = Int;\n" + """
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_fn_type_alias_self_reference_accepted(self) -> None:
        """`type FA = fn(FA -> Int) effects(pure);` is NOT an E132
        cycle: a function
        value is a table-index (pointer) indirection, so the alias's
        representation never recursively expands — the same exemption
        spec 2.6.3 grants `data` ADTs.  The reference walk deliberately
        does not descend fn-type parameter/return positions (PR #1066
        review; self-APPLICATION is separately bounded by finite alias
        unfolding, E170 at the binding site, so nothing in this family
        is silent)."""
        _check_ok("""
type FA = fn(FA -> Int) effects(pure);

private fn use_it(@FA -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")

    def test_cyclic_alias_through_discarded_type_arg_e132(self) -> None:
        """`type Wrap<T> = Int; type C = Wrap<C>` — a self-reference
        inside a type argument the generic alias never uses — is E132
        (#1059).  This pins the decision that the acyclicity rule is
        structural: the checker rejects the cycle without analyzing
        whether `Wrap` consumes `T`, even though this spelling would
        resolve to `Int` and run.  A future change that adds
        usage-analysis to admit it must revisit spec 2.6.3 first."""
        errs = _check_err("""
type Wrap<T> = Int;
type C = Wrap<C>;

private fn use_it(@C -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""", "Cyclic type alias")
        e132 = [e for e in errs if e.error_code == "E132"]
        assert e132, (
            f"Expected at least one diagnostic with error_code=E132; "
            f"got: {[(e.error_code, e.description) for e in errs]}"
        )
        assert "C -> C" in e132[0].description, (
            f"Expected cycle path 'C -> C' in description; "
            f"got: {e132[0].description!r}"
        )

    def test_acyclic_alias_through_future_arg_ok(self) -> None:
        """`type A = Future<Int>; type B = Future<A>` is a legal
        *acyclic* nesting through `Future` type arguments — the #1059
        walk must recurse into type_args without false-positiving a
        finite chain that merely mentions another alias (#1059)."""
        _check_ok("""
type A = Future<Int>;
type B = Future<A>;

private fn use_it(@B -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""")

    def test_generic_alias_param_not_cycle_ok(self) -> None:
        """A generic alias's own type parameter is bound locally and is
        never a reference to a like-named alias: `type T = Int; type
        Box<T> = Array<T>` must not read `Box`'s `<T>` as pointing at
        the alias `T` and manufacture a spurious cycle (#1059)."""
        _check_ok("""
type T = Int;
type Box<T> = Array<T>;

private fn use_it(@Box<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{
  0
}
""")

    def test_acyclic_alias_chain_ok(self) -> None:
        """`type IntAlias = Int; type Pair = IntAlias` is an
        acyclic chain — must pass without false-positive E132 (#648)."""
        _check_ok("""
type IntAlias = Int;
type Pair = IntAlias;

public fn id(@Pair -> @Pair)
  requires(true) ensures(true) effects(pure)
{
  @Pair.0
}
""")

    # Line 84: Array/Tuple without type_args
    def test_array_without_type_args(self) -> None:
        """Bare Array (no type args) is accepted as AdtType(Array, ())."""
        _check_ok("""
private fn f(@Array -> @Array)
  requires(true) ensures(true) effects(pure)
{ @Array.0 }
""")

    def test_tuple_without_type_args(self) -> None:
        """Bare Tuple (no type args) is accepted as AdtType(Tuple, ())."""
        _check_ok("""
private fn f(@Tuple -> @Tuple)
  requires(true) ensures(true) effects(pure)
{ @Tuple.0 }
""")

    # Lines 117-118: EffectSet with type variable (effect row variable)
    def test_effect_set_with_type_variable(self) -> None:
        """A forall type variable used in an effect set becomes a row var."""
        _check_ok("""
effect Console {
  op print(String -> Unit);
}

private forall<E> fn f(@Int -> @Int)
  requires(true) ensures(true) effects(<Console, E>)
{ @Int.0 }
""")

    # Lines 123-127: QualifiedEffectRef in effect set
    def test_qualified_effect_ref_in_effect_set(self) -> None:
        """Module-qualified effect ref in effects(<Mod.Effect>) is accepted."""
        _check_ok("""
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(<IO.Write>)
{ @Int.0 }
""")

    # Line 130: _resolve_effect_row fallback to PureEffectRow
    # This is a defensive branch for unknown EffectRow types.
    # Hard to trigger from source, so test via unit API.
    def test_resolve_effect_row_unknown_returns_pure(self) -> None:
        """Unknown EffectRow type falls back to PureEffectRow."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv
        from vera.types import PureEffectRow

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        bogus_row = ast.EffectRow(span=None)
        result = checker._resolve_effect_row(bogus_row)
        assert isinstance(result, PureEffectRow)

    # Lines 139-144: QualifiedEffectRef in _resolve_effect_ref
    def test_resolve_effect_ref_qualified(self) -> None:
        """_resolve_effect_ref handles QualifiedEffectRef."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv
        from vera.types import EffectInstance

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        ref = ast.QualifiedEffectRef(
            module="IO", name="Write", type_args=None, span=None,
        )
        result = checker._resolve_effect_ref(ref)
        assert isinstance(result, EffectInstance)
        assert result.name == "IO.Write"
        assert result.type_args == ()

    def test_resolve_effect_ref_unknown_returns_none(self) -> None:
        """_resolve_effect_ref returns None for unknown node types."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        bogus = ast.EffectRefNode(span=None)
        result = checker._resolve_effect_ref(bogus)
        assert result is None

    # Line 169: _slot_type_name with no type_args — returns bare name
    def test_slot_type_name_no_type_args(self) -> None:
        """_slot_type_name with no type_args returns the bare type name."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        assert checker._slot_type_name("Int", None) == "Int"
        assert checker._slot_type_name("Bool", ()) == "Bool"

    # Lines 187-189: FunctionType unification in _unify_for_inference
    def test_function_type_unification_inference(self) -> None:
        """_unify_for_inference with FunctionType patterns unifies
        parameter and return types."""
        from vera.checker.core import TypeChecker
        from vera.environment import TypeEnv
        from vera.types import (
            FunctionType, PureEffectRow, Type, TypeVar, PRIMITIVES,
        )

        checker = TypeChecker.__new__(TypeChecker)
        checker.env = TypeEnv()
        checker._reported_alias_errors: set[str] = set()

        INT = PRIMITIVES["Int"]
        BOOL = PRIMITIVES["Bool"]

        tv_a = TypeVar("A")
        tv_b = TypeVar("B")
        pattern = FunctionType((tv_a,), tv_b, PureEffectRow())
        concrete = FunctionType((INT,), BOOL, PureEffectRow())

        mapping: dict[str, Type] = {}
        checker._unify_for_inference(pattern, concrete, mapping)
        assert mapping == {"A": INT, "B": BOOL}


# =====================================================================
# Contracts
# =====================================================================

class TestContracts:

    def test_requires_bool(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_requires_non_bool_error(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(@Int.0) ensures(true) effects(pure)
{ @Int.0 }
""", "requires() predicate must be Bool")

    def test_ensures_bool(self) -> None:
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Int.0 }
""")

    def test_ensures_non_bool_error(self) -> None:
        _check_err("""
private fn bad(@Int -> @Int)
  requires(true) ensures(@Int.result) effects(pure)
{ @Int.0 }
""", "ensures() predicate must be Bool")

    def test_decreases(self) -> None:
        _check_ok("""
private fn count(@Nat -> @Nat)
  requires(true) ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then { 0 }
  else { 1 + count(@Nat.0 - 1) }
}
""")

    def test_multiple_contracts(self) -> None:
        _check_ok("""
private fn clamp_to_range(@Int, @Int, @Int -> @Int)
  requires(@Int.1 <= @Int.2)
  ensures(@Int.result >= @Int.1)
  ensures(@Int.result <= @Int.2)
  effects(pure)
{
  if @Int.0 < @Int.1 then { @Int.1 }
  else {
    if @Int.0 > @Int.2 then { @Int.2 }
    else { @Int.0 }
  }
}
""")

    def test_old_new_in_ensures(self) -> None:
        _check_ok("""
private fn incr(@Unit -> @Unit)
  requires(true)
  ensures(new(State<Int>) == old(State<Int>) + 1)
  effects(<State<Int>>)
{
  let @Int = get(());
  put(@Int.0 + 1);
  ()
}
""")

    def test_old_outside_ensures_error(self) -> None:
        _check_err("""
private fn bad(@Unit -> @Unit)
  requires(old(State<Int>) > 0)
  ensures(true)
  effects(<State<Int>>)
{ () }
""", "old() is only valid inside ensures")


# =====================================================================
# Error accumulation and edge cases
# =====================================================================

class TestErrorAccumulation:

    def test_multiple_errors(self) -> None:
        """Multiple type errors in one file are all reported."""
        errs = _errors("""
private fn bad(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = 42;
  @Int.0
}
""")
        # At least one error expected (let type mismatch or unresolved slot)
        assert len(errs) >= 1

    def test_empty_program(self) -> None:
        """An empty program type-checks cleanly."""
        _check_ok("")

    def test_data_only_program(self) -> None:
        """A program with only data declarations type-checks cleanly."""
        _check_ok("""
private data Color { Red, Green, Blue }
private data Option<T> { None, Some(T) }
""")

    def test_type_error_has_location(self) -> None:
        """Type errors include source location."""
        errs = _errors("""
private fn bad(@Int -> @Bool)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert len(errs) >= 1
        assert errs[0].location.line > 0
