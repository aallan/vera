"""Tests for vera.codegen — interpolation (string interpolation and the E615 loud inference-fallthrough channel).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re
from unittest import mock

import pytest

from tests import pipeline
from tests.codegen_helpers import (
    _compile_ok,
    _run_io,
)


# =====================================================================
# String interpolation
# =====================================================================


class TestStringInterpolation:
    """String interpolation compiles and executes correctly."""

    def test_basic_string(self) -> None:
        """Interpolating a String value into a literal."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "world";
  IO.print("hello \\(@String.0)")
}
"""
        assert _run_io(source, fn="main") == "hello world"

    def test_int_convert(self) -> None:
        """Int expressions are auto-converted to String."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 42;
  IO.print("x = \\(@Int.0)")
}
"""
        assert _run_io(source, fn="main") == "x = 42"

    def test_bool_convert(self) -> None:
        """Bool expressions are auto-converted to String."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Bool = true;
  IO.print("flag: \\(@Bool.0)")
}
"""
        assert _run_io(source, fn="main") == "flag: true"

    def test_multiple_parts(self) -> None:
        """Multiple interpolated expressions."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 1;
  let @Int = 2;
  IO.print("a=\\(@Int.1), b=\\(@Int.0)")
}
"""
        assert _run_io(source, fn="main") == "a=1, b=2"

    def test_only_expr(self) -> None:
        """Interpolation with only an expression, no literal text."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "hello";
  IO.print("\\(@String.0)")
}
"""
        assert _run_io(source, fn="main") == "hello"

    def test_empty_fragments(self) -> None:
        """Adjacent interpolations with no text between them."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Int = 1;
  let @Int = 2;
  IO.print("\\(@Int.1)\\(@Int.0)")
}
"""
        assert _run_io(source, fn="main") == "12"

    def test_nat_convert(self) -> None:
        """Nat auto-conversion works."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Nat = string_length("abc");
  IO.print("len=\\(@Nat.0)")
}
"""
        assert _run_io(source, fn="main") == "len=3"

    def test_float_convert(self) -> None:
        """Float64 auto-conversion works."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Float64 = 3.14;
  IO.print("pi=\\(@Float64.0)")
}
"""
        out = _run_io(source, fn="main")
        assert out.startswith("pi=3.14")

    def test_nested_fn_call(self) -> None:
        """Function call inside interpolation."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @String = "hello";
  IO.print("len=\\(string_length(@String.0))")
}
"""
        assert _run_io(source, fn="main") == "len=5"

    def test_string_returning_fncall_inside_interpolation_602(self) -> None:
        """#602 — interpolating a String-returning function call directly.

        Pre-fix: `_infer_fncall_vera_type` had no `i32_pair` branch in
        the WAT-type → Vera-type fallback, so a user fn returning
        `String` mapped to `None` here.  `_translate_interpolated_string`
        then fell through to the `to_string(...)` Int-conversion
        wrapper, which reads its arg as `i64` — but the FnCall pushed
        `i32_pair`.  WASM validation rejected the module with
        `expected i64, found i32` at the offending offset.

        Post-fix: the inference path consults `_fn_ret_type_exprs`
        (the same registry added by #614) when WAT type is `i32_pair`,
        returns the proper `String` Vera-type name, and the
        interpolation desugars to `string_concat(make_str(()), "\\n")`
        with both args correctly typed as i32_pair.
        """
        source = """\
private fn make(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_array_returning_fncall_indexed_inside_interpolation(self) -> None:
        """Sibling case: an `Array<T>`-returning fn indexed into Int,
        used in interpolation.  Same `i32_pair` return type as the
        String case but the index strips back to an `Int` element —
        exercises both halves of the inference path together.
        """
        source = """\
private fn make_arr(@Unit -> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_arr(())[0])")
}
"""
        assert _run_io(source, fn="main") == "10"

    def test_inline_refinement_string_in_interpolation(self) -> None:
        """A fn declared with an inline refinement return type
        (`@{ @String | predicate }`) used in interpolation.

        Surfaced during PR #627's review (CodeRabbit, third trigger
        in the same bug class as #602 and the type-alias case).
        `_register_fn` stores the literal AST, so `_fn_ret_type_exprs`
        holds a `RefinementType` directly.  My initial alias-resolving
        fix only handled `NamedType` — `isinstance(ret_te, ast.NamedType)`
        was False for a `RefinementType`, fell through to None, same
        original #602 trap.

        Fix: extracted the inference into `_resolve_i32_pair_ret_te`
        which handles both `NamedType` (with alias resolution) and
        `RefinementType` (unwrap to base, then resolve).
        """
        source = """\
private fn make(@Unit -> @{ @String | string_length(@String.0) > 0 })
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_nested_refinement_string_in_interpolation(self) -> None:
        """Fifth trigger of the #602 bug class — surfaced by the
        silent-failure-hunter agent during PR #629's review.

        The grammar admits `refinement_type` over any `type_expr`, so
        a return type can wrap refinements in refinements:
        `@{ @{ @String | p1 } | p2 }`.  PR #629's initial fix used
        `if isinstance(ret_te, ast.RefinementType): base = ret_te.base_type`
        — only one level of unwrap.  A nested refinement still fell
        through to None, reproducing the original #602 trap.

        Fix (in this PR's review pass): replaced the one-level unwrap
        with a `while` loop that handles arbitrary nesting depth.
        Same change applied symmetrically to the IndexExpr-of-FnCall
        inference path.
        """
        source = """\
private fn make(@Unit -> @{ @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 })
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_nested_refinement_in_interpolation(self) -> None:
        """Seventh trigger of the #602 bug class — surfaced by the
        silent-failure-hunter agent during PR #629's review.

        Path: `apply_fn(@FnAlias.0, ())` inside an interpolation,
        where the `FnType` alias's return type is a *nested*
        refinement.  Three separate inference sites in
        `vera/wasm/inference.py` all walk the FnType's
        `return_type` and only handled `NamedType` directly:

        - `_infer_fncall_vera_type` (apply_fn branch) — for the
          interpolation argument's vera-type lookup
        - `_resolve_generic_fn_return` — for generic-instantiated
          FnType returns
        - `_fn_type_return_wasm` — for the WASM-canonical return type

        Pre-fix, the apply_fn branch returned None for nested
        refinements, the interpolation fell through to the
        `to_string(...)` wrapper, and at validation time WASM
        rejected the i32→i64 mismatch (`expected i64, found i32`)
        that's been the canonical surface of this bug class since
        #602.

        Fix: `while isinstance(ret, ast.RefinementType): ret =
        ret.base_type` at all three sites — same shape as the
        FnCall path, applied symmetrically to the FnType-alias
        path.
        """
        source = """\
type Maker = fn(Unit -> { @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 }) effects(pure);

private fn make_maker(@Unit -> @Maker)
  requires(true) ensures(true) effects(pure)
{ fn(@Unit -> @String) effects(pure) { "hello" } }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Maker = make_maker(());
  IO.print("\\(apply_fn(@Maker.0, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_anon_inline_string_in_interpolation(self) -> None:
        """Ninth trigger of the #602 bug class — surfaced by
        CodeRabbit during PR #629's final review pass, less than an
        hour after filing #630 (the structural close-out for this
        bug class).  Empirical confirmation that the trigger rate
        outpaces local fix throughput — exactly the argument made
        for centralising canonicalisation.

        Path: `apply_fn(fn(@Unit -> @String) effects(pure) { ... },
        ())` — apply_fn called directly on an inline `AnonFn`
        literal rather than a `SlotRef` to a let-bound closure.
        Pre-fix `_infer_fncall_vera_type` only handled the SlotRef
        arg shape; the AnonFn case fell through, return value was
        None, and downstream interpolation re-triggered the canonical
        `expected i64, found i32` WASM-validation surface.

        Fix: added an `elif isinstance(closure_arg, ast.AnonFn)`
        branch alongside the SlotRef branch in
        `_infer_fncall_vera_type`.  Simpler than the SlotRef path
        (no alias substitution — AnonFn has `return_type: TypeExpr`
        directly), but the same RefinementType-unwrap +
        `_format_named_type_canonical` shape applies.
        """
        source = """\
private fn helper(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(apply_fn(fn(@Unit -> @String) effects(pure) { helper(()) }, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_anon_nested_refinement_in_interpolation(
        self,
    ) -> None:
        """Tenth trigger of the #602 bug class — surfaced by
        CodeRabbit on PR #629 immediately after the 9th was fixed.
        Inverse surface: `expected i32, found i64` rather than the
        usual `expected i64, found i32`, because this site is on
        the *WASM-type* inference half of the dispatcher
        (`_infer_apply_fn_return_type`, which infers the
        `call_indirect` sig) rather than the Vera-type-name half
        (`_infer_fncall_vera_type`, which the 9th trigger hit).

        Path: `apply_fn(fn(@Unit -> @{ @{ @String | p1 } | p2 })
        effects(pure) { ... }, ())` — inline `AnonFn` declaring a
        nested-refinement return.  Pre-fix
        `_infer_apply_fn_return_type`'s `AnonFn` branch had a
        single-level `if isinstance(ret, ast.RefinementType): base
        = ret.base_type` unwrap with a `# pragma: no cover —
        closure returns are not refinement types` claim — both
        empirically disproved.  Single-level unwrap on a nested
        refinement leaves `base` as another `RefinementType`, the
        `NamedType` check misses, and the method falls through to
        `return "i64"` — the call site emitted `i32_pair`, hence
        the inverse-direction WASM-validation surface.

        Fix: replaced the single-level `if`-unwrap with the
        established `while`-loop shape used at every other
        type-walking site, and removed the disproven
        `# pragma: no cover` claim.

        Queued for obsolescence by [#630](https://github.com/aallan/vera/issues/630)
        when the centralised `_canonical_vera_type` lands; this
        test will continue to pin the trigger through that
        refactor.
        """
        source = """\
private fn helper(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(apply_fn(fn(@Unit -> @{ @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 }) effects(pure) { helper(()) }, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_apply_fn_aliased_string_in_interpolation(self) -> None:
        """Eighth trigger of the #602 bug class — surfaced by
        CodeRabbit during PR #629's final review pass.

        Path: `apply_fn(@Maker.0, ())` inside an interpolation,
        where `Maker = fn(Unit -> Str) effects(pure)` and
        `type Str = String;`.  Pre-fix `_infer_fncall_vera_type`'s
        apply_fn branch called `_format_named_type` on
        `NamedType("Str")` which returned the alias name "Str" —
        downstream `_translate_interpolated_string` checks
        `vera_type == "String"`, the alias name missed, and the
        value fell through to the `to_string(...)` wrapper over an
        `i32_pair`, reproducing the canonical `expected i64, found
        i32` WASM-validation surface of this bug class.

        Fix: introduced `_format_named_type_canonical` (resolves
        `te.name` through the alias chain via
        `_resolve_base_type_name`, then formats with original
        `type_args`).  Replaced both `_format_named_type` calls in
        the apply_fn branch — substitution and fallback — with the
        canonical variant, mirroring the canonicalisation already
        done in `_resolve_i32_pair_ret_te` for the regular FnCall
        path.
        """
        source = """\
type Str = String;
type Maker = fn(Unit -> Str) effects(pure);

private fn make_maker(@Unit -> @Maker)
  requires(true) ensures(true) effects(pure)
{ fn(@Unit -> @String) effects(pure) { "hello" } }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Maker = make_maker(());
  IO.print("\\(apply_fn(@Maker.0, ()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_refinement_over_type_alias_in_interpolation(self) -> None:
        """Sibling case to nested-refinement — refinement applied to a
        type alias.  Worked already because `_resolve_base_type_name`
        recursively follows alias chains.  Test pins the working
        behaviour so a future change to the alias-resolution path
        can't regress it silently.
        """
        source = """\
type Str = String;

private fn make(@Unit -> @{ @Str | string_length(@Str.0) > 0 })
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_inline_refinement_array_in_indexed_interpolation(self) -> None:
        """A fn declared with a *nested* refinement return type over
        `Array<T>`, indexed inside an interpolation.

        Parallel instance of the same RefinementType gap, but in
        `_infer_index_element_type_expr`'s FnCall branch (the path
        added by #614).  Pre-fix the IndexExpr-of-FnCall element-type
        inference failed for refinement-returning fns, the enclosing
        function got dropped from the output module, and at top level
        the symptom was the [E602] "main body contains unsupported
        expressions — skipped" warning.

        Uses the nested-refinement shape (`@{ @{ @Array<Int> | p1 } |
        p2 }`) so this test exercises the `while`-loop unwrap added
        in PR #629's review pass alongside the parallel string-side
        nested test — without the loop, the array branch would only
        peel one level and fall through.

        Fix: same RefinementType `while`-loop unwrap applied to
        `_infer_index_element_type_expr`'s FnCall branch.
        """
        source = """\
private fn make(@Unit -> @{ @{ @Array<Int> | array_length(@Array<Int>.0) > 0 } | array_length(@Array<Int>.0) < 100 })
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(())[1])\\n")
}
"""
        assert _run_io(source, fn="main") == "20\n"

    def test_type_alias_string_in_interpolation(self) -> None:
        """A fn returning a type alias of `String` (e.g. `type Str =
        String; fn make(@Unit -> @Str)`) used in interpolation.

        Surfaced during PR #627's review (CodeRabbit, post-#602 fix):
        my initial fix returned `ret_te.name` directly from the
        `_fn_ret_type_exprs` registry — which stores the *declared*
        TypeExpr `NamedType("Str")`, not the resolved
        `NamedType("String")`.  Downstream `_translate_interpolated_string`
        checks `vera_type == "String"` (and the conversion-map check)
        — both miss for `"Str"` — so the value fell through to the
        `to_string(...)` fallback wrapper, reproducing the original
        #602 trap (`expected i64, found i32` at WASM validation) for
        a *different* trigger.

        Fix: resolve aliases via `_resolve_base_type_name` before
        returning.  Same shape applies symmetrically to the generic-
        branch `i32_pair` lookup added in `d78b4dc`, which now also
        canonicalises (currently latent — see code comment).
        """
        source = """\
type Str = String;

private fn make(@Unit -> @Str)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make(()))\\n")
}
"""
        assert _run_io(source, fn="main") == "hello\n"

    def test_no_to_string_wrap_on_string_returning_fncall_602(self) -> None:
        """Structural assertion for the #602 fix.

        Pre-fix: `_infer_fncall_vera_type` returned None for a user fn
        whose WAT return type was `i32_pair`, so
        `_translate_interpolated_string` wrapped the FnCall with
        `to_string(...)`.  That wrapping was the *cause* of the WASM
        validation trap (`to_string` reads its arg as `i64` but
        `i32_pair` is two `i32`s).

        Post-fix the wrap should never occur for a `String`-returning
        FnCall — the inference walker now returns `"String"`, the
        early `vera_type == "String"` branch fires, and the FnCall
        flows directly into `string_concat` un-wrapped.

        This is a *structural* test that locks the fix at the codegen
        layer.  The companion runtime test
        (`test_string_returning_fncall_inside_interpolation_602`)
        catches behavioural regressions; this one catches inference
        regressions whose downstream output happens to look right by
        coincidence.
        """
        source = """\
private fn make(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  -- Two parts so the desugar produces `string_concat(make(()), "\\n")`
  -- (a single-part interpolation short-circuits to `translate_expr(p)`
  -- without going through string_concat).
  IO.print("\\(make(()))\\n")
}
"""
        wat = _compile_ok(source).wat
        # Pull out main's body so a `to_string` reference elsewhere
        # in the module (e.g. helper fns from the prelude) doesn't
        # produce a false negative.
        main_match = re.search(
            r"\(func \$:main.*?(?=\n\s*\(func |\n\s*\)\s*$)",
            wat,
            re.DOTALL,
        )
        assert main_match is not None, "main function not found in WAT"
        main_body = main_match.group(0)
        # `to_string` was the bug's wrapper — its absence is the
        # load-bearing structural property of the fix.  (`string_concat`
        # is inlined as byte-copy loops in the WAT rather than emitted
        # as a separate `call $:string_concat`, so we don't assert on
        # it directly.)
        assert "call $:to_string" not in main_body, (
            "Pre-#602 bug shape: `String`-returning FnCall in "
            "interpolation should NOT be wrapped with `to_string`. "
            "If this assertion fires, `_infer_fncall_vera_type` has "
            "regressed for `i32_pair` returns."
        )

    def test_escaped_backslash_before_paren_is_literal(self) -> None:
        r"""``"\\("`` (a literal backslash followed by a literal
        ``(``) must be treated as two literal characters, NOT as an
        interpolation opener.

        Pre-#649-review-pass-2 the two helpers in
        ``vera/transform.py`` disagreed: ``_has_interpolation``
        correctly skipped escaped pairs (so a string with only
        ``\\(`` was treated as having no interpolation at all), but
        ``_split_interpolation`` rescanned the second character as a
        fresh start and mis-parsed the ``\\(`` as the opener of an
        interpolation segment.  The result for a string like
        ``"a\\(b"`` was a parse-time crash (no matching ``)``) where
        the user expected a literal ``a\(b``.  CodeRabbit flagged
        the divergence on PR #649.

        This test verifies the escape-skipping logic is now
        consistent across both helpers by compiling a program that
        prints a literal backslash-paren sequence and asserting the
        output preserves the literal characters.
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("a\\\\(b)c")
}
"""
        # In the Python source above, "a\\\\(b)c" is a 9-char Python
        # string literal that produces the 7-char Vera source-text
        # `a\\(b)c` — which is the 5-char Vera string value
        # `a\(b)c` after escape decoding.  The compiler must accept
        # this without trying to interpret `\(` as an interpolation
        # opener (because the preceding `\\` already consumed the
        # backslash).
        assert _run_io(source, fn="main") == "a\\(b)c", (
            "Expected literal `a\\(b)c`; the `\\\\(` escape pair "
            "should be two literal characters, not an interpolation "
            "opener."
        )


class TestE615LoudInterpolationFallthrough630:
    """[#630](https://github.com/aallan/vera/issues/630) Tier 2 — the
    `_translate_interpolated_string` silent-fallthrough path now emits
    a specific [E615] diagnostic and drops the function with [E602]
    instead of silently miscompiling.

    Pre-#630: when `_infer_vera_type` returned None or a name not in
    `_INTERP_TO_STRING`, the segment got wrapped in `to_string(...)`
    which reads its argument as `i64`.  An `i32_pair` (String/Array)
    or any non-`i64`-shaped value then produced invalid WASM at
    validation (`expected i64, found i32`) — the load-bearing
    silent-amplifier behind the ten triggers of the #602 bug class
    accumulated across PRs #627, #629.

    Post-#630: the canonicaliser closes most of the inference gaps
    on the producer side (Tier 1).  This test pins the consumer-side
    half (Tier 2): for a residual gap the canonicaliser doesn't
    cover, the failure manifests as a clean compile-time skip with
    a specific E-code, not invalid WASM.
    """

    def test_an_adt_in_interpolation_is_refused_at_check(self) -> None:
        """Interpolating an ADT-typed slot — `IO.print("\\(@Option<Int>.0)")` —
        is refused at check (E148), so code generation's E615 fallthrough is
        never reached."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  IO.print("\\(@Option<Int>.0)\\n")
}
"""
        errors = pipeline.check(source).errors
        assert [d.error_code for d in errors] == ["E148"], errors

    def test_an_adt_in_a_closure_body_interpolation_is_refused_at_check(self) -> None:
        """The same interpolation inside a closure body is refused at check
        (E148) too."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  apply_fn(fn(@Unit -> @Unit) effects(<IO>) {
    IO.print("\\(@Option<Int>.0)\\n")
  }, ())
}
"""
        errors = pipeline.check(source).errors
        assert [d.error_code for d in errors] == ["E148"], errors

    def test_one_function_s_unconvertible_interpolation_is_refused(self) -> None:
        """The one unconvertible interpolation, in `dirty` between two clean
        functions, is refused at check at its segment (E148); the
        per-function failure list behind code generation's E615 is never
        reached."""
        source = """\
public fn clean_before(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("clean_before\\n")
}

public fn dirty(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  IO.print("\\(@Option<Int>.0)\\n")
}

public fn clean_after(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("clean_after\\n")
}
"""
        errors = pipeline.check(source).errors
        assert [d.error_code for d in errors] == ["E148"], errors
        assert errors[0].location.line == 11, errors[0].location

    def test_a_result_in_interpolation_is_refused_at_check(self) -> None:
        """Interpolating a `Result` slot is refused at check (E148)."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Int, String> = Ok(42);
  IO.print("\\(@Result<Int, String>.0)\\n")
}
"""
        errors = pipeline.check(source).errors
        assert [d.error_code for d in errors] == ["E148"], errors

    def test_every_unconvertible_segment_of_one_interpolation_is_refused(self) -> None:
        """Every unconvertible segment of one interpolation is refused at check,
        each with its own E148."""
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(1);
  let @Result<Int, String> = Ok(2);
  IO.print("\\(@Option<Int>.0) and \\(@Result<Int, String>.0)\\n")
}
"""
        errors = pipeline.check(source).errors
        assert [d.error_code for d in errors] == ["E148", "E148"], errors

    def test_canonical_named_type_terminal_args_propagation(
        self,
    ) -> None:
        """The canonicaliser preserves `type_args` from the
        *terminal* `NamedType`, not the outermost — and walks
        through parameterised alias substitution to get there.
        For `type Box<T> = Array<T>`, indexing a fn that returns
        `@Box<Int>` must resolve to the `Int` element type: the
        walker substitutes the alias's `T` parameter with the
        concrete `Int` from the call site, follows to
        `Array<Int>`, and reports `Int` as the IndexExpr element
        type.

        Pre-PR-#631-review-pass the walker captured
        `outer_type_args` from the first NamedType reached and
        ignored `_type_alias_params` entirely.  Both gaps closed
        in this PR's review pass — the walker now (a) reads
        type_args from the terminal NamedType and (b) substitutes
        parameterised-alias type params before continuing.

        Note: a more direct test using `type Id<T> = T;` (per
        CodeRabbit's suggestion) hits a parallel
        parameterised-alias gap in `_type_expr_to_wasm_type`
        (codegen/core.py compilability check) that was outside
        #630's scope — since fixed by #635.  `Box<T> =
        Array<T>` exercises the walker substitution path
        end-to-end via the IndexExpr-of-FnCall element-type
        lookup, which doesn't go through the compilability
        check.

        (CodeRabbit finding 3 + code-reviewer finding I1 + later
        CodeRabbit findings 1 + 5 on PR #631.)
        """
        source = """\
type Box<T> = Array<T>;

private fn make_box(@Unit -> @Box<Int>)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_box(())[1])\\n")
}
"""
        # Runs end-to-end — IndexExpr-of-FnCall element-type inference
        # walks Box<Int> → (substitute T→Int) → Array<Int> via the
        # canonicaliser, returns the Int element type, and `[1]`
        # selects 20.
        assert _run_io(source, fn="main") == "20\n"

    def test_apply_fn_on_a_closure_a_call_returns_runs(self) -> None:
        """`apply_fn(make_mapper(()), 7)` where `make_mapper` is a call
        returning a closure: the closure's type is the function type the
        checker gave the call, so the `call_indirect` signature is its
        (#1525).  #632 refused the shape with [E616], when the signature
        was read off the closure argument's syntax, which knew only a
        `SlotRef` and an `AnonFn`."""
        source = """\
type Maker = fn(Int -> String) effects(pure);

private fn make_mapper(@Unit -> @Maker)
  requires(true) ensures(true) effects(pure)
{ fn(@Int -> @String) effects(pure) { "hello" } }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(apply_fn(make_mapper(()), 7))
}
"""
        ran = pipeline.run(source, "main", [])
        assert ran.ok, (ran.trap, [d.format() for d in ran.diagnostics])
        assert ran.stdout == "hello", ran.stdout

    def test_e635_parameterised_alias_compilability(self) -> None:
        """`type Id<T> = T;` instantiated with a parameterised type
        arg — `private fn make_list(@Unit -> @Id<Array<Int>>)`.
        Pre-fix, `_type_expr_to_wasm_type` (the compilability
        check) recursed on `_type_aliases["Id"] = NamedType("T")`
        without binding `T` to `Array<Int>`, classifying the
        return type as `"unsupported"` and dropping `make_list`
        via `[E605]`.

        Closes #635 — parallel of the walker fix landed in PR #631
        for `_canonical_named_type`, applied to the compilability
        check's separate code path.  The compilability check now
        substitutes parameterised-alias type params via
        `substitute_type_vars` before recursing.
        """
        source = """\
type Id<T> = T;

private fn make_list(@Unit -> @Id<Array<Int>>)
  requires(true) ensures(true) effects(pure)
{ [10, 20, 30] }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("\\(make_list(())[1])\\n")
}
"""
        # Runs end-to-end — make_list compiles cleanly via the
        # parameterised-alias substitution, IndexExpr inference
        # walks Id<Array<Int>> → (substitute T→Array<Int>) →
        # Array<Int>, returns Int element type.
        assert _run_io(source, fn="main") == "20\n"

    def test_fntype_return_uses_closure_pointer_abi(self) -> None:
        """A higher-order fn returning a `FnType`-aliased closure
        — `type Outer = fn(Int -> Inner) effects(pure)` where
        `Inner` is itself a `FnType` alias.  Pre-fix
        `_canonical_wasm_type` returned `"i64"` (the walker
        couldn't reach a NamedType, fell to the default), producing
        a `call_indirect` sig mismatch at WASM validation.

        Closes the FnType-return half of the bug class — the
        codegen base's `_type_expr_to_wasm_type` already handled
        FnType correctly via an explicit branch; the inference
        walker's silent default to `"i64"` was the asymmetric gap.

        Fix: `_canonical_wasm_type` falls back to a `_reaches_fn_type`
        check when the walker returns None; if the walk would have
        terminated at a `FnType`, return `"i32"` (closure-pointer
        ABI) instead of the `"i64"` default.

        (CodeRabbit finding 3, third review pass on PR #631.)
        """
        source = """\
type Inner = fn(Int -> Int) effects(pure);
type Outer = fn(Int -> Inner) effects(pure);

private fn make_outer(@Unit -> @Outer)
  requires(true) ensures(true) effects(pure)
{
  fn(@Int -> @Inner) effects(pure) {
    fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
  }
}

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Outer = make_outer(());
  let @Inner = apply_fn(@Outer.0, 5);
  IO.print(int_to_string(apply_fn(@Inner.0, 3)))
}
"""
        # 5 + 3 = 8; runs end-to-end via correct closure-pointer ABI.
        assert _run_io(source, fn="main") == "8"

    def test_a_partly_unconvertible_closure_interpolation_is_refused(
        self,
    ) -> None:
        """An interpolation that fails part way inside a closure is refused at
        check (E148), so code generation never lifts the closure it would
        have had to roll back."""
        source = """\
public fn bad(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  apply_fn(fn(@Unit -> @Unit) effects(<IO>) {
    IO.print("\\(@Option<Int>.0)\\n")
  }, ())
}

public fn good(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<Int> = array_map(
    [10, 20, 30],
    fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
  );
  IO.print(int_to_string(@Array<Int>.0[1]))
}
"""
        errors = pipeline.check(source).errors
        assert [d.error_code for d in errors] == ["E148"], errors

    def test_array_map_refinement_returning_closure(self) -> None:
        """`_infer_closure_return_vera_type` in `calls_arrays.py`
        was previously bare-NamedType-only; the #630 migration
        broadened it to handle refinements + alias chains via
        `_canonical_named_type`.  This test pins the broader
        behaviour: an `array_map` over an inline closure whose
        return type is a refinement should compile and execute,
        not silently fail inference.

        Pre-PR-#631-review-pass: no test exercised this path.
        Post-fix: the canonicaliser walks the refinement to its
        base name; `array_map`'s element-type inference returns
        `"String"` and the loop emits the correct String-element
        copy operations.

        (test-analyzer finding C2 on PR #631.)
        """
        source = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Array<String> = array_map(
    [1, 2, 3],
    fn(@Int -> @{ @String | string_length(@String.0) > 0 })
      effects(pure) { "x" }
  );
  IO.print(@Array<String>.0[0])
}
"""
        # Should run cleanly — pre-fix, the closure-return inference
        # silently returned None on the refinement, leading to wrong
        # element size in the array_map loop.
        assert _run_io(source, fn="main") == "x"


# =====================================================================
# Interpolation parse-failure width (PR #1162 review)
# =====================================================================


class TestInterpolationParseFailureWidth:
    """`_parse_interp_expr` converts syntax errors, not every failure.

    The catch around the synthesized wrapper's parse used to be a blind
    `except Exception`, so a compiler bug anywhere inside `parse` was
    reported to the user as "Invalid expression in string interpolation"
    — blaming their source for something it did not cause.  `parse`
    funnels every genuine syntax failure through `ParseError`, so that is
    the only thing worth converting.
    """

    def test_syntax_error_becomes_an_interpolation_diagnostic(self) -> None:
        from vera.errors import TransformError
        from vera.transform import _parse_interp_expr

        with pytest.raises(TransformError) as excinfo:
            _parse_interp_expr("1 +", None)
        assert "string interpolation" in str(excinfo.value)

    def test_a_non_parse_failure_propagates_unconverted(self) -> None:
        """The distinguishing case: only this separates the two widths.

        A blind `except Exception` swallows the injected error and
        reports an interpolation diagnostic instead, so this test fails
        against the previous code and passes against the narrowed catch.
        """
        from vera.errors import TransformError
        from vera.transform import _parse_interp_expr

        sentinel = RuntimeError("compiler bug, not the user's source")

        def _boom(_source: str, file: str | None = None) -> None:
            raise sentinel

        # `_parse` is bound by a function-local import, so the patch has
        # to land on the source module rather than on `vera.transform`.
        with mock.patch("vera.parser.parse", _boom):
            with pytest.raises(RuntimeError) as excinfo:
                _parse_interp_expr("1 + 1", None)
        assert excinfo.value is sentinel
        assert not isinstance(excinfo.value, TransformError)
