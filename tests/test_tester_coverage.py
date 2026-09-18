"""Tests for vera.tester — Coverage gap tests.

Targets uncovered lines in vera/tester.py, focusing on:
- Functions with Float/String/ADT parameters (unsupported types)
- Functions with Bool/Byte parameters
- Unsatisfiable preconditions
- Data declarations in programs
- _type_expr_to_slot_name edge cases
- Mixed parameter types

See tester.py uncovered lines: 246-266, 342, 390, 417, 477-488, 510,
529-531, 602, 717-723, 725-727.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from vera.cli import cmd_test


# =====================================================================
# Helpers
# =====================================================================

def _write_vera(tmp_path: Path, source: str, name: str = "test.vera") -> str:
    """Write a Vera source string to a temp file and return its path."""
    p = tmp_path / name
    p.write_text(source, encoding="utf-8")
    return str(p)


# =====================================================================
# TestTesterUnsupportedParamTypes
# =====================================================================


class TestTesterUnsupportedParamTypes:
    """Cover ADT params that are still unsupported for Z3 input generation.
    String and Float64 are now supported — their tests live in TestTesterStringInput
    and TestTesterFloat64Input."""

    def test_float_param_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with Float64 param is now tested (FP sort)."""
        source = """\
public fn square(@Float64 -> @Float64)
  requires(true)
  ensures(@Float64.result >= 0.0 || float_is_nan(@Float64.0))
  decreases(0)
  effects(pure)
{
  @Float64.0 * @Float64.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out

    def test_float_param_tested_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Float64 param function in JSON mode shows tested category."""
        source = """\
public fn negate(@Float64 -> @Float64)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  0.0 - @Float64.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        tested = [f for f in funcs if f["category"] in ("tested", "verified")]
        assert len(tested) > 0

    def test_string_param_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with String param is now tested (Z3 sequence sort)."""
        source = """\
public fn identity_str(@String -> @String)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @String.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out

    def test_adt_param_skipped(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with ADT param is skipped (unsupported type).
        Covers lines 477 (_get_param_types non-primitive) and 510
        (_generate_inputs returns None)."""
        source = """\
private data Color { Red, Green, Blue }

public fn color_to_int(@Color -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  match @Color.0 {
    Red -> 0,
    Green -> 1,
    Blue -> 2
  }
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "SKIPPED" in out


# =====================================================================
# TestTesterByteParam
# =====================================================================


class TestTesterByteParam:
    """Cover lines 529-531 (Byte Z3 variable declaration) and
    line 602 (Byte boundary seeding).

    Uses a closure (lambda) in the body so the verifier cannot translate
    it to SMT, forcing Tier 3 classification."""

    def test_byte_param_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with Byte param is Tier 3 tested via closure body."""
        source = """\
type ByteFn = fn(Byte -> Int) effects(pure);

public fn byte_apply(@Byte -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @ByteFn = fn(@Byte -> @Int) effects(pure) { byte_to_int(@Byte.0) };
  apply_fn(@ByteFn.0, @Byte.0)
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=10)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out or "SKIPPED" in out

    def test_byte_param_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Byte param function in JSON shows tested/verified category."""
        source = """\
type ByteFn = fn(Byte -> Int) effects(pure);

public fn byte_apply2(@Byte -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @ByteFn = fn(@Byte -> @Int) effects(pure) { byte_to_int(@Byte.0) };
  apply_fn(@ByteFn.0, @Byte.0)
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=10)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        tested = [f for f in funcs if f["category"] in ("tested", "verified")]
        assert len(tested) > 0


# =====================================================================
# TestTesterBoolParam
# =====================================================================


class TestTesterBoolParam:
    """Cover Bool boundary seeding in _seed_boundaries.

    Uses a closure body to force Tier 3 classification."""

    def test_bool_param_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with Bool param is Tier 3 tested via closure body."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn bool_select(@Bool, @Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  if @Bool.0 then { apply_fn(@IntFn.0, @Int.0) } else { 0 }
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=10)
        assert rc == 0
        out = capsys.readouterr().out
        # May be TESTED, VERIFIED, or SKIPPED depending on Z3 analysis
        assert "Results:" in out


# =====================================================================
# TestTesterDataDeclarationSkip
# =====================================================================


class TestTesterDataDeclarationSkip:
    """Cover lines 342, 390: data declarations are skipped by _get_targets
    and _classify_functions."""

    def test_data_decl_skipped(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Program with data declarations and functions works correctly."""
        source = """\
private data Pair { MkPair(Int, Int) }

public fn make_pair(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0)
  effects(pure)
{
  @Int.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0


# =====================================================================
# TestTesterTier3NoTestableParams
# =====================================================================


class TestTesterTier3NoTestableParams:
    """Cover line 417: Unit params with non-trivial Tier 3 contracts."""

    def test_unit_param_tier3(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A unit-param function with an unverifiable ensures is skipped
        as 'Tier 3 but no testable parameters'.

        The closure is what makes the postcondition unverifiable.  This used
        to call a `helper(())` whose `ensures` was `true` — but a zero-size
        argument no longer collapses the call summary (#1214), so the helper's
        result became a fresh variable its own contract says nothing about and
        `@Int.result > 0` was REFUTED rather than deferred, classifying the
        function `failed` instead of Tier 3.
        """
        source = """\
type IntFn = fn(Unit -> Int) effects(pure);

public fn unit_tier3(-> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  let @IntFn = fn(@Unit -> @Int) effects(pure) { 42 };
  apply_fn(@IntFn.0, ())
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        # Pin the branch, not merely the exit code: a fixture whose contract
        # is REFUTED rather than deferred also produces a one-entry
        # `functions` array, and the assertion this replaces could not tell
        # the two apart.
        assert len(data["functions"]) == 1, data["functions"]
        fn = data["functions"][0]
        assert fn["category"] == "skipped", fn
        assert fn["reason"] == "Tier 3 but no testable parameters", fn


# =====================================================================
# TestTesterRefinementTypeAlias
# =====================================================================


class TestTesterRefinementTypeAlias:
    """Cover lines 725-727: RefinementType in _type_expr_to_slot_name,
    and lines 478-486 for RefinementType params in _get_param_types."""

    def test_refinement_type_alias_param(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with a refinement type alias param.

        The ensures is *false even given* the param's refinement predicate
        (`@PosInt.0 > 0` does not imply `@PosInt.0 > @PosInt.0`), so the body
        still fails verification.  This keeps the test exercising both the
        tester's RefinementType param handling AND its "verifier error →
        FAILED" classification under #746 — `double_pos`'s old
        `ensures(@Int.result > 0)` now *verifies* because the param predicate
        is assumed (the refinement-predicate feature), so it no longer drives
        the error path.
        """
        source = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn strictly_greater(@PosInt -> @Int)
  requires(true)
  ensures(@Int.result > @PosInt.0)
  effects(pure)
{
  @PosInt.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=10)
        assert rc == 1
        out = capsys.readouterr().out
        # Verifier errors are classified as failed, not silently verified.
        assert "Testing:" in out
        assert "FAILED" in out
        assert "verification error (E500)" in out


# =====================================================================
# TestTesterRuntimeFailurePaths
# =====================================================================


class TestTesterRuntimeFailurePaths:
    """Cover lines 282-317: trial execution and result processing.
    Uses closures in body to force Tier 3 classification."""

    def test_tier3_tested_with_closure(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with a closure body is Tier 3 and gets tested."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn closure_add(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  apply_fn(@IntFn.0, @Int.0)
}
"""
        path = _write_vera(tmp_path, source)
        cmd_test(path, trials=10)
        out = capsys.readouterr().out
        # Should be tested (Tier 3 because of closure body)
        assert "Testing:" in out
        assert "Results:" in out

    def test_tier3_ensures_violation_closure(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Tier 3 function with incorrect ensures produces failures."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn bad_closure(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  apply_fn(@IntFn.0, @Int.0)
}
"""
        path = _write_vera(tmp_path, source)
        cmd_test(path, trials=50)
        out = capsys.readouterr().out
        assert "Testing:" in out
        assert "Results:" in out

    def test_tier3_unsatisfiable_precondition(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A Tier 3 function with contradictory requires is skipped as
        unsatisfiable. Covers lines 270-280."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn unsat_closure(@Int -> @Int)
  requires(@Int.0 > 10)
  requires(@Int.0 < 5)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  apply_fn(@IntFn.0, @Int.0)
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        # Non-zero since #1451's premise check made an unsatisfiable premise
        # set an ERROR (E538): the contract admits no argument, so the
        # declaration is refused, and `vera test` agrees with `vera verify`
        # about the program rather than reporting a skip and exiting clean.
        assert rc == 1
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        # Still skipped rather than tested — there is no input to generate.
        assert len(funcs) > 0
        assert any(
            f.get("category") == "skipped" for f in funcs
        ), funcs

    def test_tier3_json_output(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """JSON output for Tier 3 tested function."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn closure_id(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  apply_fn(@IntFn.0, @Int.0)
}
"""
        path = _write_vera(tmp_path, source)
        cmd_test(path, as_json=True, trials=10)
        out = capsys.readouterr().out
        data = json.loads(out)
        assert "functions" in data
        assert "summary" in data
        # Should have tested or verified category (not skipped)
        funcs = data["functions"]
        active = [f for f in funcs if f["category"] in ("tested", "verified")]
        assert len(active) > 0


# =====================================================================
# TestTesterMultipleParamTypes
# =====================================================================


class TestTesterMultipleParamTypes:
    """Cover mixed param type scenarios."""

    def test_int_and_nat_params(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Function with both Int and Nat params, forced Tier 3 via closure."""
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn mixed_apply(@Int, @Nat -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 };
  let @Int = apply_fn(@IntFn.0, nat_to_int(@Nat.0));
  if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 }
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=10)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out or "SKIPPED" in out

    def test_mixed_int_string(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Function with both Int and String params is now tested (both supported)."""
        source = """\
public fn mixed_params(@Int, @String -> @Int)
  requires(@Int.0 >= 0)
  ensures(@Int.result >= 0)
  decreases(0)
  effects(pure)
{
  @Int.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out


# =====================================================================
# TestTesterGenericFunctionSkip
# =====================================================================


class TestTesterGenericFunctionSkip:
    """Cover lines 399-400: generic function classification as skipped."""

    def test_generic_function_skipped(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A public generic function is skipped with 'generic function'."""
        source = """\
public forall<A> fn identity(@A -> @A)
  requires(true)
  ensures(true)
  effects(pure)
{
  @A.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        skipped = [f for f in funcs if f["category"] == "skipped"]
        assert len(skipped) > 0


# =====================================================================
# TestTesterStringInput
# =====================================================================


class TestTesterStringInput:
    """Tests for String parameter Z3 input generation (#169)."""

    def test_string_param_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with only String param is tested (not skipped)."""
        source = """\
public fn strlen_positive(@String -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  decreases(0)
  effects(pure)
{
  string_length(@String.0)
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out

    def test_string_param_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """String param function in JSON mode shows tested/verified category."""
        source = """\
public fn echo(@String -> @String)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @String.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        tested = [f for f in funcs if f["category"] in ("tested", "verified")]
        assert len(tested) > 0


# =====================================================================
# TestTesterFloat64Input
# =====================================================================


class TestTesterFloat64Input:
    """Tests for Float64 parameter Z3 input generation (#169)."""

    def test_float64_param_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with only Float64 param is tested (not skipped)."""
        source = """\
public fn abs_float(@Float64 -> @Float64)
  requires(true)
  ensures(@Float64.result >= 0.0 || float_is_nan(@Float64.0))
  decreases(0)
  effects(pure)
{
  if @Float64.0 >= 0.0 then {
    @Float64.0
  } else {
    0.0 - @Float64.0
  }
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=5)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out or "VERIFIED" in out

    def test_fp_value_to_float_special_values(self) -> None:
        # #797 (PR #806 review): the FP model-value -> Python float extraction
        # must handle NaN / +-Inf / signed zero.  The boundary loop only seeds
        # finite values, so these branches are otherwise dead under test.
        import math

        import z3

        from vera.tester import _fp_value_to_float
        sort = z3.FPSort(11, 53)
        assert math.isnan(_fp_value_to_float(z3.fpNaN(sort)))
        assert _fp_value_to_float(z3.fpPlusInfinity(sort)) == math.inf
        assert _fp_value_to_float(z3.fpMinusInfinity(sort)) == -math.inf
        neg_zero = _fp_value_to_float(z3.fpMinusZero(sort))
        assert neg_zero == 0.0 and math.copysign(1.0, neg_zero) == -1.0
        assert _fp_value_to_float(z3.FPVal(1.5, sort)) == 1.5

    def test_float64_param_json(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Float64 param function in JSON mode shows tested/verified category."""
        source = """\
public fn double(@Float64 -> @Float64)
  requires(true)
  ensures(true)
  decreases(0)
  effects(pure)
{
  @Float64.0 + @Float64.0
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        tested = [f for f in funcs if f["category"] in ("tested", "verified")]
        assert len(tested) > 0


# =====================================================================
# TestTesterUnitFunctions — direct unit tests for helper functions
# =====================================================================


class TestTesterUnitFunctions:
    """Direct unit tests for tester.py helper functions."""

    def test_type_expr_to_slot_name_named_with_type_args(self) -> None:
        """Cover lines 717-723: NamedType with type_args."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        # NamedType with type args
        te = vera_ast.NamedType(
            name="Array",
            type_args=[vera_ast.NamedType(name="Int", type_args=[])],
        )
        result = _type_expr_to_slot_name(te, EMPTY_ALIAS_ENV)
        assert result == "Array<Int>"

    def test_type_expr_to_slot_name_refinement_type_arg(self) -> None:
        """A refinement type ARGUMENT resolves to its base name.

        #1208: the tester names through `vera.naming.slot_name`, which
        resolves a `RefinementType` ARGUMENT to the checker's own
        predicate-elided form — here `{@Int | ...}`, since the predicate is
        a literal `true` with no alias to see through.  (The pre-dedup
        tester copy bailed to `"?"` on any non-`NamedType` arg.)"""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        # NamedType with a RefinementType type arg
        pred = vera_ast.BoolLit(value=True)
        ref_type = vera_ast.RefinementType(
            base_type=vera_ast.NamedType(name="Int", type_args=[]),
            predicate=pred,
        )
        te = vera_ast.NamedType(name="Array", type_args=[ref_type])
        result = _type_expr_to_slot_name(te, EMPTY_ALIAS_ENV)
        assert result == "Array<{@Int | ...}>"

    def test_type_expr_to_slot_name_refinement(self) -> None:
        """Cover lines 725-727: RefinementType delegates to base_type."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        pred = vera_ast.BoolLit(value=True)
        te = vera_ast.RefinementType(
            base_type=vera_ast.NamedType(name="Int", type_args=[]),
            predicate=pred,
        )
        result = _type_expr_to_slot_name(te, EMPTY_ALIAS_ENV)
        assert result == "Int"

    def test_type_expr_to_slot_name_fntype(self) -> None:
        """A top-level `FnType` slot name is the synthetic ``"Fn"``.

        #1208: the tester names through `vera.naming.slot_name`, which
        returns ``"Fn"`` for a top-level function type — the checker's own
        convention (the pre-dedup tester copy returned `"?"`)."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        # FnType is neither NamedType nor RefinementType
        te = vera_ast.FnType(
            params=(vera_ast.NamedType(name="Int", type_args=()),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            effect=vera_ast.PureEffect(),
        )
        result = _type_expr_to_slot_name(te, EMPTY_ALIAS_ENV)
        assert result == "Fn"

    def test_slot_name_canonicalizes_an_alias_type_argument(self) -> None:
        """The threaded env is LOAD-BEARING, not decoration (#1208).

        A Z3 variable is declared under `@{slot name}.{index}` and the
        function's own `requires` clauses look themselves up under the key
        the CHECKER bound — so an alias in type-argument position has to
        resolve on the tester's side too, or the generated constraint binds
        nothing.  Contrasted against the alias-free environment, which is
        the answer a syntactic rebuild gives.
        """
        from tests.naming_helpers import alias_env_from_declarations
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.parser import parse_to_ast
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        env = alias_env_from_declarations(
            parse_to_ast("type Cnt = Int;\n").declarations)
        te = vera_ast.NamedType(
            name="Array",
            type_args=(vera_ast.NamedType(name="Cnt", type_args=()),),
        )
        assert _type_expr_to_slot_name(te, env) == "Array<Int>"
        assert _type_expr_to_slot_name(te, EMPTY_ALIAS_ENV) == "Array<Cnt>"

    def test_alias_typed_param_is_exercised(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """An alias-typed parameter is TRIALED, not skipped (#1216).

        ``_get_param_types`` resolves each parameter through the threaded
        naming environment before asking whether Z3 can encode it, so
        ``type Cnt = Int`` reaches the Z3-supported ``Int`` instead of the
        opaque syntactic head that used to classify it unsupported and skip
        the function (E701) before any variable was named.  The companion of
        the test above: the tester's rendered names are consistent BECAUSE
        both the resolution and the naming come from :mod:`vera.naming`, not
        because the parameters it reaches happen to have primitive heads.
        """
        source = (
            "type Cnt = Int;\n"
            "\n"
            "public fn keep(@Cnt -> @Int)\n"
            "  requires(@Cnt.0 > 100)\n"
            "  ensures(@Int.result > 100)\n"
            "  decreases(0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Cnt.0\n"
            "}\n"
        )
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=3)
        assert rc == 0
        out = capsys.readouterr().out
        assert "TESTED" in out.upper(), out
        assert "SKIPPED" not in out.upper(), out

    def test_alias_typed_fn_trials_run_and_its_ensures_holds(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The run-through: trials actually execute and the contract holds.

        Reported through ``--json`` so the trial COUNTS are asserted rather
        than inferred from a status word — "TESTED" with zero trials would
        satisfy a text check while proving nothing ran.  The `requires` is
        written against the alias slot ``@Cnt.0``, so a generator that named
        its Z3 variable anything else would drop the constraint (translation
        is best-effort) and feed the function values at or below 100, which
        the runtime-checked `ensures` reports as failures.
        """
        source = (
            "type Cnt = Int;\n"
            "\n"
            "public fn keep(@Cnt -> @Int)\n"
            "  requires(@Cnt.0 > 100)\n"
            "  ensures(@Int.result > 100)\n"
            "  decreases(0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Cnt.0\n"
            "}\n"
        )
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        payload = json.loads(capsys.readouterr().out)
        fns = {f["name"]: f for f in payload["functions"]}
        assert fns["keep"]["category"] == "tested", payload
        assert fns["keep"]["trials_run"] > 0, payload
        assert fns["keep"]["trials_failed"] == 0, payload

    def test_alias_typed_requires_binds_under_the_alias_slot_name(
        self, tmp_path: Path,
    ) -> None:
        """The generated inputs SATISFY the alias-spelled `requires` (#1216).

        The direct proof behind the run-through above: every generated value
        is > 100, which can only happen if `requires(@Cnt.0 > 100)` found the
        Z3 variable the generator declared.  ``translate_expr`` returns None
        for an unresolvable reference and the constraint is then silently
        dropped, so a mis-keyed variable produces unconstrained inputs rather
        than an error.
        """
        from tests.naming_helpers import alias_env_from_declarations
        from vera.parser import parse_to_ast
        from vera.tester import _generate_inputs, _get_param_types

        program = parse_to_ast(
            "type Cnt = Int;\n"
            "\n"
            "public fn keep(@Cnt -> @Int)\n"
            "  requires(@Cnt.0 > 100)\n"
            "  ensures(@Int.result > 100)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Cnt.0\n"
            "}\n"
        )
        env = alias_env_from_declarations(program.declarations)
        decl = program.declarations[1].decl
        param_types = _get_param_types(decl, env)
        inputs = _generate_inputs(decl, param_types, 5, env)
        assert inputs, "an alias-typed parameter must generate inputs"
        assert all(row[0] > 100 for row in inputs), inputs

    def test_refined_alias_param_is_generated_inside_its_refinement(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A refined alias reaches Z3 with its PREDICATE (#1216).

        A refinement is unwritable in parameter position, so an alias is the
        only way to have one — which means #1216 is what first brings refined
        parameters to the generator.  Codegen guards them on entry, so an
        unconstrained generator manufactures arguments the guard rejects and
        every out-of-range trial is reported as a refinement violation
        (measured: 96 of 100 trials, before the membership constraint).
        """
        source = (
            "type Pos = { @Int | @Int.0 > 0 };\n"
            "\n"
            "public fn f(@Pos -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result > 0)\n"
            "  decreases(0)\n"
            "  effects(pure)\n"
            "{\n"
            "  @Pos.0\n"
            "}\n"
        )
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=20)
        assert rc == 0
        payload = json.loads(capsys.readouterr().out)
        fn = {f["name"]: f for f in payload["functions"]}["f"]
        assert fn["category"] == "tested", payload
        assert fn["trials_run"] > 0, payload
        assert fn["trials_failed"] == 0, payload

    def test_unresolvable_alias_param_still_skips_cleanly(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The negative: a param that RESOLVES to something Z3 cannot encode.

        Resolution is not a promise of encodability — an ADT resolves fine
        and is still unsupported — so the E701-class skip has to survive the
        #1216 flip with its reason intact, naming the resolved type.
        """
        source = (
            "type Maybe = Option<Int>;\n"
            "\n"
            "public fn unwrap_or(@Maybe -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result >= 0)\n"
            "  decreases(0)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @Maybe.0 {\n"
            "    Some(@Int) -> 0,\n"
            "    None -> 0\n"
            "  }\n"
            "}\n"
        )
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=3)
        assert rc == 0
        out = capsys.readouterr().out
        assert "SKIPPED" in out.upper(), out
        assert "cannot generate Option<Int> inputs" in out, out

    def test_forall_var_shadowing_an_alias_stays_unsupported(self) -> None:
        """A type PARAMETER resolves to a type variable, alias or no alias.

        The shadowing scope is load-bearing for the resolution as well as for
        the naming: with a module alias ``type T = Int`` in the environment, a
        ``forall<T>`` parameter written ``@T`` would resolve to the encodable
        ``Int`` if the function's own type parameters were not in scope — and
        the tester would then generate Int inputs for a generic function.
        """
        import dataclasses

        from tests.naming_helpers import alias_env_from_declarations
        from vera.parser import parse_to_ast
        from vera.tester import _get_param_types
        from vera.types import INT, TypeVar

        program = parse_to_ast(
            "type T = Int;\n"
            "\n"
            "public forall<T> fn pick(@T -> @T)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  @T.0\n"
            "}\n"
        )
        env = alias_env_from_declarations(program.declarations)
        decl = program.declarations[1].decl
        assert _get_param_types(decl, env) == [TypeVar("T")]
        # The alias is genuinely in the environment — without the function's
        # own `forall` narrowing this same expression resolves to `Int`.
        assert _get_param_types(
            dataclasses.replace(decl, forall_vars=None), env,
        ) == [INT]

    def test_get_source_line_no_span(self) -> None:
        """Cover line 751: _get_source_line returns '' when no span."""
        from vera.tester import _get_source_line
        from vera import ast as vera_ast

        decl = vera_ast.FnDecl(
            name="test",
            params=(),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        result = _get_source_line("some source", decl)
        assert result == ""

    def test_get_param_types_adt(self) -> None:
        """An ADT parameter resolves to its `AdtType` — and stays unsupported.

        Since #1216 the answer is the CHECKER's semantic type rather than a
        placeholder `Type()`, so the skip reason can name what the parameter
        actually is; the encodability verdict is unchanged.
        """
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _get_param_types, _unsupported_type_names
        from vera.types import AdtType
        from vera import ast as vera_ast

        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.NamedType(name="MyADT", type_args=()),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        types = _get_param_types(decl, EMPTY_ALIAS_ENV)
        assert types == [AdtType("MyADT", ())]
        assert _unsupported_type_names(types) == ["MyADT"]

    def test_get_param_types_refinement_primitive(self) -> None:
        """A refinement over a primitive keeps its `RefinedType` wrapper."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _get_param_types
        from vera.types import INT, RefinedType, base_type
        from vera import ast as vera_ast

        pred = vera_ast.BoolLit(value=True)
        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.RefinementType(
                base_type=vera_ast.NamedType(name="Int", type_args=()),
                predicate=pred,
            ),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        types = _get_param_types(decl, EMPTY_ALIAS_ENV)
        assert len(types) == 1
        assert isinstance(types[0], RefinedType)
        assert base_type(types[0]) == INT

    def test_get_param_types_refinement_non_primitive(self) -> None:
        """A refinement over an ADT resolves through to the ADT base."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _get_param_types, _unsupported_type_names
        from vera.types import AdtType, base_type
        from vera import ast as vera_ast

        pred = vera_ast.BoolLit(value=True)
        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.RefinementType(
                base_type=vera_ast.NamedType(name="MyADT", type_args=()),
                predicate=pred,
            ),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        types = _get_param_types(decl, EMPTY_ALIAS_ENV)
        assert base_type(types[0]) == AdtType("MyADT", ())
        assert _unsupported_type_names(types) == ["MyADT"]

    def test_get_param_types_refinement_non_named_base(self) -> None:
        """A refinement over a function type resolves to a `FunctionType`."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _get_param_types, _unsupported_type_names
        from vera.types import FunctionType, base_type
        from vera import ast as vera_ast

        pred = vera_ast.BoolLit(value=True)
        fn_type = vera_ast.FnType(
            params=(vera_ast.NamedType(name="Int", type_args=()),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            effect=vera_ast.PureEffect(),
        )
        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.RefinementType(
                base_type=fn_type,
                predicate=pred,
            ),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        types = _get_param_types(decl, EMPTY_ALIAS_ENV)
        assert isinstance(base_type(types[0]), FunctionType)
        assert _unsupported_type_names(types) == [
            "fn(Int -> Int) effects(pure)"]

    def test_get_param_types_fn_type(self) -> None:
        """A function-typed parameter resolves to a `FunctionType`."""
        from vera.naming import EMPTY_ALIAS_ENV
        from vera.tester import _get_param_types
        from vera.types import INT, FunctionType
        from vera import ast as vera_ast

        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.FnType(
                params=(vera_ast.NamedType(name="Int", type_args=()),),
                return_type=vera_ast.NamedType(name="Int", type_args=()),
                effect=vera_ast.PureEffect(),
            ),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        types = _get_param_types(decl, EMPTY_ALIAS_ENV)
        assert len(types) == 1
        assert isinstance(types[0], FunctionType)
        assert types[0].params == (INT,)

    def test_has_nontrivial_contracts_decreases(self) -> None:
        """Cover line 462: Decreases is non-trivial."""
        from vera.tester import _has_nontrivial_contracts
        from vera import ast as vera_ast

        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.NamedType(name="Nat", type_args=()),),
            return_type=vera_ast.NamedType(name="Nat", type_args=()),
            contracts=(
                vera_ast.Requires(expr=vera_ast.BoolLit(value=True)),
                vera_ast.Ensures(expr=vera_ast.BoolLit(value=True)),
                vera_ast.Decreases(exprs=(vera_ast.SlotRef(type_name="Nat", type_args=None, index=0),)),
            ),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        assert _has_nontrivial_contracts(decl) is True

    def test_generate_inputs_unsupported_type(self) -> None:
        """Cover the unsupported-type returns-None path (ADT, not Float64)."""
        from vera.tester import _generate_inputs
        from vera.types import AdtType
        from vera import ast as vera_ast

        # ADT types are unsupported; _generate_inputs should return None
        adt_type = AdtType(name="Color", type_args=())
        decl = vera_ast.FnDecl(
            name="test",
            params=(vera_ast.NamedType(name="Color", type_args=()),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(
                vera_ast.Requires(expr=vera_ast.BoolLit(value=True)),
                vera_ast.Ensures(expr=vera_ast.BoolLit(value=True)),
            ),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=None,
        )
        result = _generate_inputs(decl, [adt_type], 10)
        assert result is None

    def test_get_source_line_out_of_range(self) -> None:
        """Cover line 751: span line out of range returns ''."""
        from vera.tester import _get_source_line
        from vera import ast as vera_ast

        decl = vera_ast.FnDecl(
            name="test",
            params=(),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            contracts=(),
            effect=vera_ast.PureEffect(),
            body=(),
            forall_vars=None,
            forall_constraints=None,
            where_fns=None,
            span=vera_ast.Span(line=999, column=1, end_line=999, end_column=1),
        )
        result = _get_source_line("line1\nline2", decl)
        assert result == ""


# =====================================================================
# #1229 — an untranslatable `requires` conjunct SKIPS the function
# =====================================================================


class TestUntranslatableRequiresSkips:
    """A precondition the input generator cannot model must not be reported as
    a falsified contract (#1229).

    ``vera/smt.py`` returns None for constructs outside the decidable fragment
    — ``string_length`` over a non-literal is the reported one (#802: Vera
    counts UTF-8 bytes, Z3's ``Length`` counts code points, and no byte-length
    operator exists in Z3's string theory).  The generator's solver then
    carries no constraint from that conjunct at all, so ``_seed_boundaries``
    happily emits ``""`` for a function whose ``requires`` forbids it, the
    compiled WASM traps on its own entry guard, and the trap was scored as a
    contract FAILURE: ``19/20 passed, 1 failed`` on a correct program, with an
    E700 naming the function's own ``requires``.

    Spec §0.3 forbids a diagnostic that misleads, and this one inverted the
    truth — a generator limitation reported as a falsified contract.  The
    function is SKIPPED instead, with a reason NAMING the conjunct, mirroring
    the existing ``cannot generate <T> inputs`` taxonomy.

    The detection is MECHANISM-based rather than a list of built-ins: it asks
    the SMT layer to translate each conjunct and believes the answer.  That
    matters because the tester's ``SmtContext`` is built bare — no
    ``_fn_lookup``, no ADT registry — so far more than ``string_length``
    defers there, and any hand-written list would have been incomplete from
    the day it was written.
    """

    _SHOUT = """\
public fn shout(@String -> @String)
  requires(string_length(@String.0) > 0)
  ensures(string_length(@String.result) >= string_length(@String.0))
  effects(pure)
{
  string_concat(@String.0, "!")
}
"""

    def _json(
        self,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
        source: str,
    ) -> dict:
        path = _write_vera(tmp_path, source)
        cmd_test(path, as_json=True, trials=20)
        return json.loads(capsys.readouterr().out)

    def test_the_reported_repro_no_longer_fails(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The issue's program, verbatim: skipped, not failed."""
        data = self._json(tmp_path, capsys, self._SHOUT)
        fns = {f["name"]: f for f in data["functions"]}
        assert fns["shout"]["category"] == "skipped", fns["shout"]
        assert fns["shout"]["trials_run"] == 0, fns["shout"]
        assert data["summary"]["failed"] == 0, data["summary"]
        assert data["summary"]["total_trials"] == 0, data["summary"]
        assert data["ok"] is True, data

    def test_the_skip_reason_names_the_conjunct(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Naming the blocker is the point of the taxonomy: "skipped" on its
        own is no more actionable than the wrong FAILED was."""
        data = self._json(tmp_path, capsys, self._SHOUT)
        reason = {f["name"]: f for f in data["functions"]}["shout"]["reason"]
        assert "string_length(@String.0) > 0" in reason, reason

    def test_the_skip_is_also_disclosed_as_an_e701_diagnostic(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The unsupported-parameter-type skip discloses itself as an E701
        warning; an unsatisfiable-by-construction precondition is the same
        class of blocker and discloses itself the same way, so a consumer
        reading only ``diagnostics`` still learns why nothing ran."""
        data = self._json(tmp_path, capsys, self._SHOUT)
        e701 = [d for d in data["diagnostics"] if d["error_code"] == "E701"]
        assert len(e701) == 1, data["diagnostics"]
        assert e701[0]["severity"] == "warning", e701
        assert "string_length(@String.0) > 0" in e701[0]["description"], e701
        assert not [d for d in data["diagnostics"] if d["severity"] == "error"]

    def test_a_mixed_clause_skips_the_function_naming_only_the_blocker(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """One translatable conjunct beside one untranslatable one.

        The ratified direction skips the FUNCTION — generating from the
        satisfiable half alone still manufactures inputs the other half
        forbids, which is the bug — and names the conjunct that blocked it,
        not the whole clause.
        """
        source = """\
public fn shout2(@String, @Int -> @String)
  requires(@Int.0 > 0 && string_length(@String.0) > 0)
  ensures(string_length(@String.result) >= 0)
  effects(pure)
{
  string_concat(@String.0, "!")
}
"""
        data = self._json(tmp_path, capsys, source)
        fn = {f["name"]: f for f in data["functions"]}["shout2"]
        assert fn["category"] == "skipped", fn
        assert "string_length(@String.0) > 0" in fn["reason"], fn["reason"]
        assert "@Int.0 > 0" not in fn["reason"], (
            "the translatable conjunct is not a blocker and must not be named "
            f"as one: {fn['reason']}"
        )
        assert data["summary"]["failed"] == 0, data["summary"]

    def test_a_fully_translatable_precondition_is_still_tested(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The control.  A skip taxonomy that fired on everything would
        satisfy every assertion above and silently switch `vera test` off.

        The closure keeps the function at Tier 3 — which is the only
        classification the new check is asked about — while its `requires`
        stays ordinary translatable arithmetic, so this measures the check and
        not the tier.
        """
        source = """\
type IntFn = fn(Int -> Int) effects(pure);

public fn half(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(@Int.result >= 0)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 / 2 };
  apply_fn(@IntFn.0, @Int.0)
}
"""
        data = self._json(tmp_path, capsys, source)
        fn = {f["name"]: f for f in data["functions"]}["half"]
        assert fn["category"] == "tested", fn
        assert fn["trials_run"] > 0, fn
        assert data["summary"]["total_trials"] > 0, data["summary"]

    def test_a_quantified_precondition_skips_too(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The mechanism generalises past ``string_length``.

        Quantifier translation is deferred (#427), so a ``forall``
        precondition constrains the generator no more than ``string_length``
        did — the same defect through a different construct, and no list of
        built-ins would have caught it.
        """
        source = """\
public fn under(@Nat -> @Nat)
  requires(forall(@Int, @Nat.0, fn(@Int -> @Bool) effects(pure) { @Int.0 >= 0 }))
  ensures(@Nat.result >= 0)
  effects(pure)
{
  @Nat.0
}
"""
        data = self._json(tmp_path, capsys, source)
        fn = {f["name"]: f for f in data["functions"]}["under"]
        assert fn["category"] == "skipped", fn
        assert "forall" in fn["reason"], fn["reason"]

    def test_an_untranslatable_refinement_predicate_skips_too(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A refined PARAMETER's predicate is the same defect one door over.

        The predicate is part of the parameter's type, not of its contract, so
        no ``requires`` states it — and codegen emits it as an entry guard
        that traps on a violating argument (the #1216 membership constraint
        exists for exactly this).  Untranslatable, it constrains the generator
        no more than an untranslatable ``requires`` conjunct does, and the
        trap it produces is scored identically.
        """
        source = """\
type NonEmpty = { @String | string_length(@String.0) > 0 };

public fn shout3(@NonEmpty -> @String)
  requires(true)
  ensures(string_length(@String.result) >= 0)
  effects(pure)
{
  string_concat(@NonEmpty.0, "!")
}
"""
        data = self._json(tmp_path, capsys, source)
        fn = {f["name"]: f for f in data["functions"]}["shout3"]
        assert fn["category"] == "skipped", fn
        assert "string_length(@String.0) > 0" in fn["reason"], fn["reason"]
        assert data["summary"]["failed"] == 0, data["summary"]
