"""Unit tests for vera.types — type operations."""

from __future__ import annotations

import pytest

from vera.types import (
    INT, NAT, BOOL, FLOAT64, STRING, UNIT, NEVER, BYTE,
    PrimitiveType, AdtType, FunctionType, RefinedType, TypeVar, UnknownType,
    PureEffectRow, ConcreteEffectRow, EffectInstance,
    is_subtype, types_equal, substitute, substitute_effect,
    pretty_type, pretty_effect, canonical_type_name, base_type,
)
from vera import ast


# -- Dummy AST node for RefinedType predicates --
_DUMMY_PRED = ast.BoolLit(value=True, span=ast.Span(0, 0, 0, 0))


# =====================================================================
# is_subtype
# =====================================================================

class TestIsSubtype:
    def test_reflexivity_primitive(self) -> None:
        assert is_subtype(INT, INT)

    def test_reflexivity_adt(self) -> None:
        opt_int = AdtType("Option", (INT,))
        assert is_subtype(opt_int, opt_int)

    def test_unknown_left(self) -> None:
        assert is_subtype(UnknownType(), INT)

    def test_unknown_right(self) -> None:
        assert is_subtype(INT, UnknownType())

    def test_unknown_both(self) -> None:
        assert is_subtype(UnknownType(), UnknownType())

    def test_never_bottom(self) -> None:
        assert is_subtype(NEVER, INT)
        assert is_subtype(NEVER, BOOL)
        assert is_subtype(NEVER, AdtType("Option", (INT,)))

    def test_nat_widens_to_int(self) -> None:
        assert is_subtype(NAT, INT)

    def test_int_permitted_as_nat(self) -> None:
        assert is_subtype(INT, NAT)

    def test_typevar_not_subtype_of_concrete(self) -> None:
        assert not is_subtype(TypeVar("T"), INT)

    def test_concrete_not_subtype_of_typevar(self) -> None:
        assert not is_subtype(INT, TypeVar("T"))

    def test_typevar_reflexive(self) -> None:
        assert is_subtype(TypeVar("T"), TypeVar("T"))

    def test_typevar_different_names(self) -> None:
        assert not is_subtype(TypeVar("T"), TypeVar("U"))

    def test_adt_with_same_typevar(self) -> None:
        a = AdtType("Option", (TypeVar("T"),))
        assert is_subtype(a, a)

    def test_adt_typevar_not_subtype_concrete(self) -> None:
        assert not is_subtype(
            AdtType("Option", (TypeVar("T"),)),
            AdtType("Option", (INT,)),
        )

    def test_adt_concrete_not_subtype_typevar(self) -> None:
        assert not is_subtype(
            AdtType("Option", (INT,)),
            AdtType("Option", (TypeVar("T"),)),
        )

    def test_adt_matching_args(self) -> None:
        assert is_subtype(AdtType("Option", (INT,)), AdtType("Option", (INT,)))

    def test_adt_mismatched_args(self) -> None:
        assert not is_subtype(AdtType("Option", (INT,)), AdtType("Option", (BOOL,)))

    def test_adt_different_names(self) -> None:
        assert not is_subtype(AdtType("List", (INT,)), AdtType("Option", (INT,)))

    def test_refined_strips_to_base(self) -> None:
        refined = RefinedType(INT, _DUMMY_PRED)
        assert is_subtype(refined, INT)

    def test_base_to_refined(self) -> None:
        refined = RefinedType(INT, _DUMMY_PRED)
        assert is_subtype(INT, refined)

    def test_incompatible_types(self) -> None:
        assert not is_subtype(INT, BOOL)
        assert not is_subtype(STRING, INT)


# =====================================================================
# types_equal
# =====================================================================

class TestTypesEqual:
    def test_same_primitive(self) -> None:
        assert types_equal(INT, INT)

    def test_different_primitive(self) -> None:
        assert not types_equal(INT, BOOL)

    def test_unknown_wildcard_left(self) -> None:
        assert types_equal(UnknownType(), INT)

    def test_unknown_wildcard_right(self) -> None:
        assert types_equal(BOOL, UnknownType())

    def test_adt_deep_equality(self) -> None:
        a = AdtType("Result", (INT, STRING))
        b = AdtType("Result", (INT, STRING))
        assert types_equal(a, b)

    def test_adt_deep_inequality(self) -> None:
        a = AdtType("Result", (INT, STRING))
        b = AdtType("Result", (INT, BOOL))
        assert not types_equal(a, b)

    def test_different_type_classes(self) -> None:
        assert not types_equal(INT, AdtType("Int", ()))

    def test_function_type_equal(self) -> None:
        a = FunctionType((INT,), BOOL, PureEffectRow())
        b = FunctionType((INT,), BOOL, PureEffectRow())
        assert types_equal(a, b)

    def test_function_type_diff_return(self) -> None:
        a = FunctionType((INT,), BOOL, PureEffectRow())
        b = FunctionType((INT,), INT, PureEffectRow())
        assert not types_equal(a, b)

    def test_refined_equal_by_base(self) -> None:
        a = RefinedType(INT, _DUMMY_PRED)
        b = RefinedType(INT, _DUMMY_PRED)
        assert types_equal(a, b)

    def test_typevar_equal(self) -> None:
        assert types_equal(TypeVar("T"), TypeVar("T"))

    def test_typevar_unequal(self) -> None:
        assert not types_equal(TypeVar("T"), TypeVar("U"))


# =====================================================================
# substitute
# =====================================================================

class TestSubstitute:
    def test_typevar_replaced(self) -> None:
        result = substitute(TypeVar("T"), {"T": INT})
        assert result == INT

    def test_typevar_not_in_mapping(self) -> None:
        result = substitute(TypeVar("T"), {"U": INT})
        assert result == TypeVar("T")

    def test_empty_mapping(self) -> None:
        assert substitute(INT, {}) == INT

    def test_primitive_unchanged(self) -> None:
        assert substitute(BOOL, {"T": INT}) == BOOL

    def test_nested_adt(self) -> None:
        ty = AdtType("List", (TypeVar("T"),))
        result = substitute(ty, {"T": INT})
        assert result == AdtType("List", (INT,))

    def test_function_type(self) -> None:
        ty = FunctionType((TypeVar("A"),), TypeVar("B"), PureEffectRow())
        result = substitute(ty, {"A": INT, "B": BOOL})
        assert result == FunctionType((INT,), BOOL, PureEffectRow())

    def test_refined_type(self) -> None:
        ty = RefinedType(TypeVar("T"), _DUMMY_PRED)
        result = substitute(ty, {"T": INT})
        assert isinstance(result, RefinedType)
        assert result.base == INT
        assert result.predicate is _DUMMY_PRED

    def test_deeply_nested(self) -> None:
        # Option<List<T>> with T=Int -> Option<List<Int>>
        ty = AdtType("Option", (AdtType("List", (TypeVar("T"),)),))
        result = substitute(ty, {"T": INT})
        assert result == AdtType("Option", (AdtType("List", (INT,)),))


# =====================================================================
# substitute_effect
# =====================================================================

class TestSubstituteEffect:
    def test_pure_unchanged(self) -> None:
        result = substitute_effect(PureEffectRow(), {"T": INT})
        assert isinstance(result, PureEffectRow)

    def test_concrete_substituted(self) -> None:
        eff = ConcreteEffectRow(
            frozenset({EffectInstance("State", (TypeVar("T"),))}),
        )
        result = substitute_effect(eff, {"T": INT})
        assert isinstance(result, ConcreteEffectRow)
        (inst,) = result.effects
        assert inst.name == "State"
        assert inst.type_args == (INT,)

    def test_row_var_preserved(self) -> None:
        eff = ConcreteEffectRow(
            frozenset({EffectInstance("IO", ())}),
            row_var="E",
        )
        result = substitute_effect(eff, {})
        assert result.row_var == "E"


# =====================================================================
# pretty_type / pretty_effect
# =====================================================================

class TestPrettyType:
    def test_primitive(self) -> None:
        assert pretty_type(INT) == "Int"

    def test_adt_no_args(self) -> None:
        assert pretty_type(AdtType("Color", ())) == "Color"

    def test_adt_with_args(self) -> None:
        assert pretty_type(AdtType("Option", (INT,))) == "Option<Int>"

    def test_function_type(self) -> None:
        ft = FunctionType((INT,), BOOL, PureEffectRow())
        result = pretty_type(ft)
        assert "fn(" in result
        assert "Int" in result
        assert "Bool" in result

    def test_refined_type(self) -> None:
        result = pretty_type(RefinedType(INT, _DUMMY_PRED))
        assert "{@Int | ...}" == result

    def test_typevar(self) -> None:
        assert pretty_type(TypeVar("T")) == "T"

    def test_unknown(self) -> None:
        assert pretty_type(UnknownType()) == "?"


class TestPrettyEffect:
    def test_pure(self) -> None:
        assert pretty_effect(PureEffectRow()) == "effects(pure)"

    def test_concrete_single(self) -> None:
        eff = ConcreteEffectRow(frozenset({EffectInstance("IO", ())}))
        assert pretty_effect(eff) == "effects(<IO>)"

    def test_concrete_with_row_var(self) -> None:
        eff = ConcreteEffectRow(
            frozenset({EffectInstance("IO", ())}),
            row_var="E",
        )
        result = pretty_effect(eff)
        assert "IO" in result
        assert "E" in result


# =====================================================================
# canonical_type_name / base_type
# =====================================================================

class TestCanonicalTypeName:
    def test_bare_name(self) -> None:
        assert canonical_type_name("Int") == "Int"

    def test_with_args(self) -> None:
        assert canonical_type_name("Option", (INT,)) == "Option<Int>"

    def test_empty_args(self) -> None:
        assert canonical_type_name("Color", ()) == "Color"


class TestBaseType:
    def test_primitive_passthrough(self) -> None:
        assert base_type(INT) is INT

    def test_strips_refinement(self) -> None:
        assert base_type(RefinedType(INT, _DUMMY_PRED)) is INT

    def test_strips_nested_refinement(self) -> None:
        inner = RefinedType(INT, _DUMMY_PRED)
        outer = RefinedType(inner, _DUMMY_PRED)
        assert base_type(outer) is INT
