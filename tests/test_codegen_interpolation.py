"""Tests for vera.codegen — interpolation (string interpolation and the E615 loud inference-fallthrough channel).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import re

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _compile,
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
private fn make(-> @String)
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
        source = _IO_PRELUDE + """\
private fn make_arr(-> @Array<Int>)
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
        source = _IO_PRELUDE + """\
private fn make(-> @{ @String | string_length(@String.0) > 0 })
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
        source = _IO_PRELUDE + """\
private fn make(-> @{ @{ @String | string_length(@String.0) > 0 } | string_length(@String.0) < 100 })
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
type Str = String;

private fn make(-> @{ @Str | string_length(@Str.0) > 0 })
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
        source = _IO_PRELUDE + """\
private fn make(-> @{ @{ @Array<Int> | array_length(@Array<Int>.0) > 0 } | array_length(@Array<Int>.0) < 100 })
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
        String; fn make(-> @Str)`) used in interpolation.

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
        source = _IO_PRELUDE + """\
type Str = String;

private fn make(-> @Str)
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
        source = _IO_PRELUDE + """\
private fn make(-> @String)
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
            r"\(func \$main.*?(?=\n\s*\(func |\n\s*\)\s*$)",
            wat,
            re.DOTALL,
        )
        assert main_match is not None, "main function not found in WAT"
        main_body = main_match.group(0)
        # `to_string` was the bug's wrapper — its absence is the
        # load-bearing structural property of the fix.  (`string_concat`
        # is inlined as byte-copy loops in the WAT rather than emitted
        # as a separate `call $string_concat`, so we don't assert on
        # it directly.)
        assert "call $to_string" not in main_body, (
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
        source = _IO_PRELUDE + """\
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

    def test_e615_fires_on_adt_in_interpolation(self) -> None:
        """Interpolating an ADT-typed slot — `IO.print("\\(@Option<Int>.0)")`
        — yields a non-recognised `vera_type` name (`"Option<Int>"`)
        and trips the post-#630 E615 fallthrough.

        Pre-#630 this would have wrapped the slot in `to_string(...)`
        and produced invalid WASM at instantiation; post-#630 it
        emits [E615] and the function is skipped with [E602] before
        any invalid emission.
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  IO.print("\\(@Option<Int>.0)\\n")
}
"""
        result = _compile(source)
        # No errors — the program parses + type-checks cleanly.
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, (
            f"Expected no errors, got: {errors}"
        )
        # E615 fires on the interpolation segment.
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        assert e615, (
            f"Expected an [E615] diagnostic; got warnings: {warnings}"
        )
        assert "interpolate" in e615[0].description.lower(), (
            f"E615 message should mention interpolation; got: "
            f"{e615[0].description}"
        )
        # Function gets dropped with the existing [E602] mechanism —
        # E615 is the *specific* annotation, E602 is the loud skip.
        e602 = [d for d in warnings if d.error_code == "E602"]
        assert e602, (
            f"Expected an [E602] skip diagnostic alongside E615; "
            f"warnings were: {warnings}"
        )
        # E615 must precede the *matching* E602 — the one for the
        # function that contained the offending interpolation — so
        # the specific-cause-then-generic-skip narrative reads
        # correctly per function.  Other E602s may interleave
        # (e.g. prelude combinators that are independently skipped
        # via #604), so we filter to the E602 mentioning `main` and
        # assert the per-function ordering invariant only.
        main_e602 = [d for d in e602 if "main" in d.description]
        assert main_e602, (
            f"Expected an [E602] mentioning `main`; e602: {e602}"
        )
        e615_idx = warnings.index(e615[0])
        main_e602_idx = warnings.index(main_e602[0])
        assert e615_idx < main_e602_idx, (
            f"E615 should precede the matching E602 (main) in the "
            f"warnings stream; got E615 at index {e615_idx}, "
            f"main's E602 at {main_e602_idx}"
        )
        # The E615 has a source location attached pointing at the
        # offending interpolation segment.  Source layout:
        #
        #     line 1: effect IO {
        #     line 2:   op print(String -> Unit);
        #     line 3: }
        #     line 4: public fn main(-> @Unit)
        #     line 5:   requires(true) ensures(true) effects(<IO>)
        #     line 6: {
        #     line 7:   let @Option<Int> = Some(42);
        #     line 8:   IO.print("\(@Option<Int>.0)\n")
        #     line 9: }
        #
        # The SlotRef ``@Option<Int>.0`` starts at line 8, column 15
        # (cols 1-2 indent, 3-4 ``IO``, 5 ``.``, 6-10 ``print``,
        # 11 ``(``, 12 ``"``, 13-14 ``\(``, 15 ``@``).  Pre-#634 the
        # span landed on line 3 (the synthetic parse-wrapper's
        # content line) because spans inside interpolated expressions
        # were never remapped from wrapper coordinates back to
        # original-source coordinates.  Closes #634.
        assert e615[0].location.line == 8, (
            f"E615 should point at the string literal on line 8 "
            f"(post-#634 span remap); got line "
            f"{e615[0].location.line}"
        )
        assert e615[0].location.column == 15, (
            f"E615 should point at column 15 (start of the SlotRef "
            f"inside the interpolation segment); got column "
            f"{e615[0].location.column}"
        )
        # `main` is not in exports because the body was dropped.
        assert "main" not in result.exports, (
            f"main should be skipped; exports: {result.exports}"
        )

    def test_e615_in_closure_body_emits_diagnostic(self) -> None:
        """Closure-body parallel of the top-level E615 path.
        Pre-this-PR the harvest in `_compile_fn` only ran for top-
        level functions; `_compile_lifted_closure` returned None
        without emitting [E615], silently dropping the closure from
        the function table.  The call_indirect at the use site then
        referenced a missing entry and WASM validation rejected the
        module — same silent-drop shape that #614/#615 fixed for
        translation failures, but for the post-#630 interpolation
        path inside closure bodies.

        Fix in PR #631: extracted the harvest into
        `CodeGenerator._harvest_interp_inference_failures` and
        called it from both functions.py and closures.py — closure
        bodies now emit [E615] for inference failures.

        Fix in PR #631 (review pass, closing #636):
        `_lift_pending_closures` now reports whether any closure
        body failed; `_compile_fn` checks the flag and drops the
        enclosing top-level fn with a specific [E602] noting the
        closure-failure cause.  Pre-fix the enclosing fn was
        emitted with a `call_indirect` to a missing function-table
        entry, producing a WASM-validation trap with no
        source-located parent-fn diagnostic.

        (silent-failure-hunter finding C1 + later CodeRabbit follow-up
        on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(42);
  apply_fn(fn(@Unit -> @Unit) effects(<IO>) {
    IO.print("\\(@Option<Int>.0)\\n")
  }, ())
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        # The closure-body harvest must emit at least one [E615].
        # Pre-#631 the closure was silently dropped with no [E615]
        # anywhere.
        assert e615, (
            f"Expected at least one [E615] from the closure body; "
            f"warnings were: {warnings}"
        )
        # The enclosing fn must be dropped via [E602].  Pre-#636
        # main remained in exports despite the closure failure,
        # producing a runtime WASM-validation trap; post-#636 the
        # parent is dropped cleanly.
        e602_main = [
            d for d in warnings
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602_main, (
            f"Expected an [E602] for `main` after closure failure; "
            f"warnings were: {warnings}"
        )
        assert "main" not in result.exports, (
            f"main should be dropped when its closure body fails to "
            f"compile (#636); exports: {result.exports}"
        )

    def test_per_function_isolation_of_failures_list(self) -> None:
        """`_interp_inference_failures` lives on `WasmContext`,
        which `_compile_fn` constructs fresh per top-level function.
        This test pins per-function isolation: a clean function
        compiled **after** a function that triggers E615 must not
        inherit the failure list and falsely emit E615.

        Test layout: `clean_before` → `dirty` → `clean_after`.
        Both `clean_*` functions must remain in exports.  Without
        the `clean_after` (only `clean_before`), a forward leak
        from `dirty` would never reach a clean function and the
        test would silently pass even with broken isolation —
        the pre-PR-#631-review-pass version of this test had this
        gap (CodeRabbit finding 2 on PR #631).

        Pre-#630: not testable because the silent fallthrough
        wrapped with `to_string`; cross-function leak wouldn't
        manifest as [E615] regardless.  Post-#630: load-bearing —
        if a future refactor reuses a context across functions or
        forgets to clear the failure list, this test fires.

        (comment-analyzer finding I4 + later CodeRabbit finding 2
        on PR #631.)
        """
        source = _IO_PRELUDE + """\
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
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        # E615 fires exactly once — for `dirty` (Option<Int> in
        # interpolation).  If `clean_after` inherited `dirty`'s
        # failure list, we'd see a second E615 (or `clean_after`
        # would be dropped via E602).
        assert e615, (
            f"Expected [E615] for `dirty`; got warnings: {warnings}"
        )
        assert len(e615) == 1, (
            f"Expected exactly one [E615]; got {len(e615)}: {e615}"
        )
        # Both clean functions must remain in exports.  The
        # `clean_after` assertion is the one that catches forward
        # leakage — pre-fix would still pass `clean_before` but
        # fail this.
        assert "clean_before" in result.exports, (
            f"clean_before should be exported; "
            f"exports: {result.exports}"
        )
        assert "clean_after" in result.exports, (
            f"clean_after should be exported (no inference failures "
            f"in its own body, must not inherit dirty's failure "
            f"list); exports: {result.exports}"
        )
        # `dirty` is dropped via the [E602] mechanism.
        assert "dirty" not in result.exports, (
            f"dirty should be skipped; exports: {result.exports}"
        )

    def test_e615_fires_on_result_in_interpolation(self) -> None:
        """Adjacent E615 shape — `Result<T,E>` in interpolation.
        Distinct from Option (separate ADT), pre-emptively pinned
        so that a future change to canonicalisation or interpolation
        narrowing that broadens `Option<T>` handling doesn't
        accidentally regress the parallel `Result` path.

        Pins the full loud-skip surface (parallel to the ADT test):
        E615 fires for the inference miss, E602 fires for the
        function skip, and `main` is dropped from `result.exports`.

        (test-analyzer finding C3 + later CodeRabbit follow-up on
        PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Result<Int, String> = Ok(42);
  IO.print("\\(@Result<Int, String>.0)\\n")
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        assert e615, (
            f"Expected [E615] for Result<Int, String> interpolation; "
            f"got warnings: {warnings}"
        )
        # Loud-skip surface: E602 must also fire for `main`, and
        # main must be dropped from exports.  Parallel to the ADT
        # test's assertions — without these, a regression that
        # emits E615 but fails to propagate the function-skip
        # would silently slip past this test.
        e602_main = [
            d for d in warnings
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602_main, (
            f"Expected an [E602] for `main` after Result-in-"
            f"interpolation E615; warnings: {warnings}"
        )
        assert "main" not in result.exports, (
            f"main should be skipped when interpolation E615 fires; "
            f"exports: {result.exports}"
        )

    def test_multiple_e615_in_one_interpolation(self) -> None:
        """One [E615] per failing segment — not "first failure
        aborts loop".  Pre-this-PR the silent-fallthrough returned
        None on the first failure, so a user with N bad segments
        in one interpolation got one [E615] per recompile, N
        round-trips total.  Now the loop continues and records every
        failing segment, then bails at the end if any failed.

        (silent-failure-hunter finding H2 on PR #631.)
        """
        source = _IO_PRELUDE + """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  let @Option<Int> = Some(1);
  let @Result<Int, String> = Ok(2);
  IO.print("\\(@Option<Int>.0) and \\(@Result<Int, String>.0)\\n")
}
"""
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e615 = [d for d in warnings if d.error_code == "E615"]
        # Two failing segments → exactly two distinct E615
        # diagnostics.  Pinning the exact count (rather than `>= 2`)
        # catches a duplicate-emit regression where the harvest
        # accidentally walks the failures list more than once or
        # the per-segment recording emits N>1 entries per failure.
        assert len(e615) == 2, (
            f"Expected exactly 2 [E615] diagnostics for two failing "
            f"interpolation segments; got {len(e615)}: {e615}"
        )
        # Per-segment span fidelity (#634).  Source layout:
        #
        #     line 9:   IO.print("\(@Option<Int>.0) and \(@Result<Int, String>.0)\n")
        #     cols ^^   ^^      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        #     12 ".  13-14 \(.  15 @Option starts.
        #     35-36 \(.  37 @Result starts.
        #
        # Both diagnostics must land on line 9; their columns must
        # differ and match the column of their respective SlotRef.
        # Pre-#634 both would have landed on line 3 (the synthetic
        # parse-wrapper's content line) with column 3 — the bug this
        # test pins as fixed.
        assert all(d.location.line == 9 for d in e615), (
            f"Both E615s should point at line 9; got lines "
            f"{[d.location.line for d in e615]}"
        )
        cols = sorted(d.location.column for d in e615)
        assert cols == [15, 37], (
            f"Per-segment column fidelity broken — expected first "
            f"SlotRef at col 15 (`@Option<Int>.0`) and second at col "
            f"37 (`@Result<Int, String>.0`); got {cols}"
        )

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
        (codegen/core.py compilability check) that's outside
        #630's scope and tracked as a follow-up.  `Box<T> =
        Array<T>` exercises the walker substitution path
        end-to-end via the IndexExpr-of-FnCall element-type
        lookup, which doesn't go through the compilability
        check.

        (CodeRabbit finding 3 + code-reviewer finding I1 + later
        CodeRabbit findings 1 + 5 on PR #631.)
        """
        source = _IO_PRELUDE + """\
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

    def test_e616_apply_fn_unhandled_closure_arg_shape(self) -> None:
        """`apply_fn(make_mapper(()), 7)` where `make_mapper` is a
        FnCall returning a closure — the apply_fn return-type
        dispatcher only recognises `SlotRef` (into a `FnType` alias)
        and inline `AnonFn` literals.  Any other shape (FnCall,
        IfExpr, etc.) used to default the call_indirect sig to
        `i64`, mismatching the actual `i32_pair` (or other) emit
        and producing a WASM-validation trap with no source-located
        diagnostic.

        Closes #632 — the apply_fn / call_indirect parallel of
        #630's interpolation-side `[E615]` work.  Now the failure
        records the offending closure_arg on
        `_apply_fn_inference_failures` and the harvest emits a
        specific `[E616]` before the enclosing fn is dropped via
        `[E602]`.
        """
        source = _IO_PRELUDE + """\
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
        result = _compile(source)
        warnings = [
            d for d in result.diagnostics if d.severity == "warning"
        ]
        e616 = [d for d in warnings if d.error_code == "E616"]
        assert e616, (
            f"Expected an [E616] for the unhandled apply_fn "
            f"closure-arg shape; warnings: {warnings}"
        )
        assert "apply_fn" in e616[0].description.lower() or (
            "closure" in e616[0].description.lower()
        ), (
            f"E616 message should mention apply_fn / closure; got: "
            f"{e616[0].description}"
        )
        # E616 must precede the matching E602 in the warnings
        # stream so the specific-cause-then-generic-skip narrative
        # reads correctly per function.  Filter to the E602
        # mentioning `main` so unrelated prelude E602s don't
        # confound (parallel to the E615 ordering assertion in
        # `test_e615_fires_on_adt_in_interpolation`).
        e602_main = [
            d for d in warnings
            if d.error_code == "E602" and "main" in d.description
        ]
        assert e602_main, (
            f"Expected an [E602] for `main` after E616; warnings: "
            f"{warnings}"
        )
        e616_idx = warnings.index(e616[0])
        main_e602_idx = warnings.index(e602_main[0])
        assert e616_idx < main_e602_idx, (
            f"E616 should precede the matching E602 (main) in the "
            f"warnings stream; got E616 at index {e616_idx}, main's "
            f"E602 at {main_e602_idx}"
        )
        # `main` is dropped via [E602] (the call_indirect would
        # have referenced a missing return-type signature).
        assert "main" not in result.exports, (
            f"main should be skipped when apply_fn can't infer "
            f"the closure return type; exports: {result.exports}"
        )

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
        source = _IO_PRELUDE + """\
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
        source = _IO_PRELUDE + """\
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

    def test_closure_orphans_not_committed_on_partial_fail(
        self,
    ) -> None:
        """When `_lift_pending_closures` fails on any closure in
        the worklist, the parent fn is dropped (#636) — but the
        successful sibling closures must NOT be left in the
        module-level `_closure_fns_wat` / `_closure_table` state,
        otherwise their entries shift table indices for
        *subsequent* top-level fns' closures.

        Concretely: `bad` has one closure that fails E615, `good`
        compiled afterwards has its own closure.  Without
        commit-on-success, `bad`'s would-be orphan would land in
        `_closure_table` and `good`'s closure_id would no longer
        match its actual table index, producing a `call_indirect`
        to the wrong function at runtime.

        Fix: accumulate worklist results in local buffers; only
        extend `_closure_fns_wat` / `_closure_table` /
        `_fn_source_map` / `_closure_sigs` if every closure
        succeeded.

        (CodeRabbit finding 1, third review pass on PR #631.)
        """
        source = _IO_PRELUDE + """\
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
        result = _compile(source)
        # `bad` is dropped via the closure-fail propagation (#636).
        assert "bad" not in result.exports, (
            f"bad should be dropped; exports: {result.exports}"
        )
        # `good` must remain — its closure is independent.
        assert "good" in result.exports, (
            f"good should be exported; exports: {result.exports}"
        )
        # Run `good` to confirm its closure references the correct
        # table entry.  Pre-fix `bad`'s orphan closure would have
        # been at table index 0, shifting `good`'s closure to index
        # 1 while its closure_id stored in the closure struct
        # remained 1 (because `_next_closure_id` is module-monotonic)
        # — call_indirect would target index 1 expecting `$anon_1`
        # but actually find `good`'s closure (originally meant for
        # index 1 with $anon_2 closure_id).  In this specific
        # fixture either trap or wrong output; the `_run_io` below
        # exercises the path.
        from vera.codegen import execute
        exec_result = execute(result, fn_name="good")
        # `good` is `Unit`-returning so no value to assert beyond
        # not trapping.
        assert exec_result.value is None or exec_result.value == 0, (
            f"good() should run cleanly; got: {exec_result.value!r}"
        )

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
        source = _IO_PRELUDE + """\
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
