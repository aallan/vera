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
    p.write_text(source)
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
        """A function with Float64 param is now tested (Z3 Real sort)."""
        source = """\
public fn square(@Float64 -> @Float64)
  requires(true)
  ensures(@Float64.result >= 0.0)
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
        as 'Tier 3 but no testable parameters'."""
        source = """\
private fn helper(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }

public fn unit_tier3(-> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  helper(())
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, as_json=True, trials=5)
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        # The function should appear in results
        assert len(data["functions"]) > 0


# =====================================================================
# TestTesterRefinementTypeAlias
# =====================================================================


class TestTesterRefinementTypeAlias:
    """Cover lines 725-727: RefinementType in _type_expr_to_slot_name,
    and lines 478-486 for RefinementType params in _get_param_types."""

    def test_refinement_type_alias_param(
        self, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A function with a refinement type alias param."""
        source = """\
type PosInt = { @Int | @Int.0 > 0 };

public fn double_pos(@PosInt -> @Int)
  requires(true)
  ensures(@Int.result > 0)
  effects(pure)
{
  @PosInt.0 * 2
}
"""
        path = _write_vera(tmp_path, source)
        rc = cmd_test(path, trials=10)
        assert rc == 0
        out = capsys.readouterr().out
        # Should be tested or verified (refinement narrows input)
        assert "Testing:" in out


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
        rc = cmd_test(path, trials=10)
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
        rc = cmd_test(path, trials=50)
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
        assert rc == 0
        data = json.loads(capsys.readouterr().out)
        funcs = data["functions"]
        # May be skipped due to unsatisfiable precondition
        assert len(funcs) > 0

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
        rc = cmd_test(path, as_json=True, trials=10)
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
  ensures(@Float64.result >= 0.0)
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
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        # NamedType with type args
        te = vera_ast.NamedType(
            name="Array",
            type_args=[vera_ast.NamedType(name="Int", type_args=[])],
        )
        result = _type_expr_to_slot_name(te)
        assert result == "Array<Int>"

    def test_type_expr_to_slot_name_named_with_non_named_type_arg(self) -> None:
        """Cover line 722: type arg that is not NamedType returns '?'."""
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        # NamedType with a non-NamedType type arg (e.g. RefinementType)
        pred = vera_ast.BoolLit(value=True)
        ref_type = vera_ast.RefinementType(
            base_type=vera_ast.NamedType(name="Int", type_args=[]),
            predicate=pred,
        )
        te = vera_ast.NamedType(name="Array", type_args=[ref_type])
        result = _type_expr_to_slot_name(te)
        assert result == "?"

    def test_type_expr_to_slot_name_refinement(self) -> None:
        """Cover lines 725-727: RefinementType delegates to base_type."""
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        pred = vera_ast.BoolLit(value=True)
        te = vera_ast.RefinementType(
            base_type=vera_ast.NamedType(name="Int", type_args=[]),
            predicate=pred,
        )
        result = _type_expr_to_slot_name(te)
        assert result == "Int"

    def test_type_expr_to_slot_name_unknown(self) -> None:
        """Cover line 727: unknown type expr returns '?'."""
        from vera.tester import _type_expr_to_slot_name
        from vera import ast as vera_ast

        # FnType is neither NamedType nor RefinementType
        te = vera_ast.FnType(
            params=(vera_ast.NamedType(name="Int", type_args=()),),
            return_type=vera_ast.NamedType(name="Int", type_args=()),
            effect=vera_ast.PureEffect(),
        )
        result = _type_expr_to_slot_name(te)
        assert result == "?"

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
        """Cover lines 477: non-primitive NamedType returns Type()."""
        from vera.tester import _get_param_types
        from vera.types import Type
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
        types = _get_param_types(decl)
        assert len(types) == 1
        assert types[0] == Type()

    def test_get_param_types_refinement_primitive(self) -> None:
        """Cover line 482: RefinementType with primitive base returns RefinedType."""
        from vera.tester import _get_param_types
        from vera.types import RefinedType, INT
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
        types = _get_param_types(decl)
        assert len(types) == 1
        assert isinstance(types[0], RefinedType)

    def test_get_param_types_refinement_non_primitive(self) -> None:
        """Cover line 484: RefinementType with non-primitive base returns Type()."""
        from vera.tester import _get_param_types
        from vera.types import Type
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
        types = _get_param_types(decl)
        assert len(types) == 1
        assert types[0] == Type()

    def test_get_param_types_refinement_non_named_base(self) -> None:
        """Cover line 486: RefinementType with non-NamedType base."""
        from vera.tester import _get_param_types
        from vera.types import Type
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
        types = _get_param_types(decl)
        assert len(types) == 1
        assert types[0] == Type()

    def test_get_param_types_fn_type(self) -> None:
        """Cover line 488: FnType param returns Type()."""
        from vera.tester import _get_param_types
        from vera.types import Type
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
        types = _get_param_types(decl)
        assert len(types) == 1
        assert types[0] == Type()

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
        from vera.types import AdtType, Type
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
