"""A judgement made on a value an earlier diagnostic already refused reports
nothing further (#1563, the checker's lines).

The class: the check refuses a declaration, a type name or a value, and a
later judgement reads what was left behind as if it stood, so the program
draws a second error at code that is not wrong, pointing away from the one
fix it needs.  One rule per source, each decided where the thing is refused,
not at the judgement:

* a function refused for taking a built-in's name (E151) leaves the name to
  no function of this file, so a bare call to it is `Unknown`, as the
  module-qualified call to it already was, and is never held to the
  built-in's signature;
* a `data` declaration refused for taking a built-in type's name (E158) is
  not registered, whatever the name, as a primitive's never was (#1497), so
  its constructors build no value of the built-in and the built-in keeps its
  own type arguments;
* a type name nothing declares (E136) is a placeholder every judgement
  admits, as `Unknown` is (`is_subtype`), so a `let`, a return, an argument
  and a destructured component draw no mismatch against it;
* a typed hole (W001) is the diagnostic behind its `Unknown`, so a `match`
  over one is not judged for coverage, as a scrutinee in error is not
  (#1671).

and in the verifier, a refused binder holds its predicate for the rest of
its scope in every spelling (the post-fact rule, #1695): a `@Nat` binder's
sign as a refined binder's predicate, and a destructure's component as a
`let`'s binder, so the call that reads it is never a second error.

The matrix spans source x judgement site; each cell asserts the program's
errors are exactly the refusal's own.  The negative space: the nearest
accepted neighbour of each source (the declaration renamed, the type name
spelled right, the hole filled) checks clean, and an `Unknown` no diagnostic
stands behind (`apply_fn` over a type variable) is still judged (E313).
"""

from __future__ import annotations

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/calls.py",
    "vera/checker/control.py",
    "vera/checker/core.py",
    "vera/checker/modules.py",
    "vera/checker/registration.py",
    "vera/checker/resolution.py",
    "vera/types.py",
    "vera/verifier.py",
    "vera/smt.py",
])


def _codes(source: str) -> list[str]:
    checked = pipeline.check(source)
    return [d.error_code for d in checked.diagnostics
            if d.severity == "error"]


def _all_codes(source: str) -> list[str]:
    checked = pipeline.check(source)
    return [d.error_code for d in checked.diagnostics]


_FN = """\
public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""

# ---------------------------------------------------------------------------
# E151: a call to a name a refused function took
# ---------------------------------------------------------------------------

#: A refused redefinition of a built-in, with a body the program means.
_SHADOWS = {
    "array_length": ("@Int -> @Option<Int>", "Some(@Int.0)"),
    "string_length": ("@Int -> @Option<Int>", "Some(@Int.0)"),
    "abs": ("@Int -> @Option<Int>", "Some(@Int.0)"),
}

#: Where the call's value is judged.
_CALL_SITES = {
    "match": "match {call} {{\n    Some(@Int) -> @Int.0,\n    None -> 0\n  }}",
    "let": "let @Option<Int> = {call};\n  0",
    "argument": "option_unwrap_or({call}, 0)",
}


def _shadow_program(name: str, site: str) -> str:
    sig, body = _SHADOWS[name]
    decl = (f"private fn {name}({sig})\n  requires(true)\n  ensures(true)\n"
            f"  effects(pure)\n{{\n  {body}\n}}\n\n")
    call = f"{name}(@Int.0)"
    return decl + _FN.format(body=_CALL_SITES[site].format(call=call))


@pytest.mark.parametrize("site", sorted(_CALL_SITES))
@pytest.mark.parametrize("name", sorted(_SHADOWS))
def test_a_call_to_a_refused_name_is_not_held_to_the_built_in(
        name: str, site: str) -> None:
    assert _codes(_shadow_program(name, site)) == ["E151"]


@pytest.mark.parametrize("site", sorted(_CALL_SITES))
def test_the_renamed_function_checks_clean(site: str) -> None:
    source = _shadow_program("abs", site).replace("abs", "abs_custom")
    assert _codes(source) == []


def test_repro_1563_a_call_to_a_refused_built_in_name_draws_one_error() -> None:
    """The issue's line: E151, then E202, E314 twice and E313 at base."""
    assert _codes(_shadow_program("array_length", "match")) == ["E151"]


# ---------------------------------------------------------------------------
# E158: a data declaration taking a built-in type's name
# ---------------------------------------------------------------------------

_RESERVED = ("Array", "Decimal", "Future", "Map", "Set", "Tuple", "Int",
             "String")

#: Where the refused declaration's constructor or name is used.
_DATA_USES = {
    "let_other_type": "let @Bool = Wrap(@Int.0);\n  0",
    "match": "match Wrap(@Int.0) {{\n    Wrap(@Int) -> @Int.0\n  }}",
    "argument": "nat_to_int(string_length(Wrap(@Int.0)))",
}


def _data_program(name: str, use: str) -> str:
    return (f"private data {name} {{\n  Wrap(Int)\n}}\n\n"
            + _FN.format(body=_DATA_USES[use]).replace("{{", "{")
            .replace("}}", "}"))


@pytest.mark.parametrize("use", sorted(_DATA_USES))
@pytest.mark.parametrize("name", _RESERVED)
def test_a_refused_data_declaration_draws_no_second_error(
        name: str, use: str) -> None:
    assert _codes(_data_program(name, use)) == ["E158"]


@pytest.mark.parametrize("name", ("Map", "Set", "Array", "Decimal"))
def test_the_built_in_keeps_its_own_type_after_a_refused_declaration(
        name: str) -> None:
    """The built-in's own type arguments still stand: a refused `data Map`
    left `@Map<String, Int>` meaning the declaration (E135)."""
    uses = {
        "Map": ("let @Map<String, Int> = map_new();\n"
                "  nat_to_int(map_size(@Map<String, Int>.0))"),
        "Set": ("let @Set<Int> = set_new();\n"
                "  nat_to_int(set_size(@Set<Int>.0))"),
        "Array": ("let @Array<Int> = [1, 2];\n"
                  "  nat_to_int(array_length(@Array<Int>.0))"),
        "Decimal": ("let @Decimal = decimal_from_int(1);\n  0"),
    }
    source = (f"private data {name} {{\n  Wrap(Int)\n}}\n\n"
              + _FN.format(body=uses[name]))
    assert _codes(source) == ["E158"]


@pytest.mark.parametrize("use", ("let_other_type", "argument"))
def test_the_renamed_data_declaration_is_judged(use: str) -> None:
    """The neighbour: a declaration under a free name stands, and the same
    uses are refused for what they are."""
    assert _codes(_data_program("Boxed", use)) == ["E170" if use.startswith(
        "let") else "E202"]


def test_repro_1563_a_refused_data_map_types_no_value_as_map() -> None:
    """The issue's line, at base: `Wrap(@Int.0)` typed `Map`, so the `let`
    drew E170 ("value has type Map")."""
    assert _codes(_data_program("Map", "let_other_type")) == ["E158"]


# ---------------------------------------------------------------------------
# E136: a type name nothing declares
# ---------------------------------------------------------------------------

_OPT = """\
private fn opt(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

"""

_UNKNOWN_SITES = {
    "let": _OPT + _FN.format(body="let @Optio<Int> = opt(@Int.0);\n  0"),
    "return": (
        "private fn give(@Int -> @Optio<Int>)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  Some(@Int.0)\n}\n"),
    "argument": (
        "private fn take(@Optio<Int> -> @Int)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  0\n}\n\n"
        + _FN.format(body="take(Some(@Int.0))")),
    "destructure": _FN.format(
        body="let Tuple<@Optio<Int>, @Int> = Tuple(Some(1), 2);\n  @Int.0"),
    "array_element": _FN.format(
        body="let @Array<Optio<Int>> = [Some(1)];\n  0"),
    "comparison": (
        "private fn eqs(@Optio<Int>, @Optio<Int> -> @Bool)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  @Optio<Int>.0 == @Optio<Int>.1\n}\n"),
    "nested_argument": (
        "private fn take(@Array<Optio<Int>> -> @Int)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n  0\n}\n\n"
        + _FN.format(body="take([Some(@Int.0)])")),
}


@pytest.mark.parametrize("site", sorted(_UNKNOWN_SITES))
def test_a_value_is_not_judged_against_an_unknown_type_name(site: str) -> None:
    codes = _codes(_UNKNOWN_SITES[site])
    assert codes and set(codes) == {"E136"}, codes


@pytest.mark.parametrize("site", sorted(_UNKNOWN_SITES))
def test_the_type_name_spelled_right_is_judged_clean(site: str) -> None:
    assert _codes(_UNKNOWN_SITES[site].replace("Optio<", "Option<")) == []


def test_a_value_of_another_type_is_still_refused_against_a_known_name() -> None:
    """The neighbour the rule must not widen into: against a type that
    resolves, a mismatched value is E170 as before."""
    source = _OPT + _FN.format(body="let @Result<Int, Int> = opt(@Int.0);\n  0")
    assert _codes(source) == ["E170"]


def test_repro_1563_an_unresolved_let_type_draws_one_error() -> None:
    """The issue's line: E136, then E170 at the initialiser, at base."""
    assert _codes(_UNKNOWN_SITES["let"]) == ["E136"]


# ---------------------------------------------------------------------------
# W001: a typed hole as a scrutinee
# ---------------------------------------------------------------------------

_HOLE_ARMS = {
    "option": "Some(@Int) -> @Int.0,\n    None -> 0",
    "bool": "true -> 1,\n    false -> 0",
    "literal": "1 -> 1,\n    2 -> 0",
    "constructor_only": "Some(@Int) -> @Int.0",
}


@pytest.mark.parametrize("arms", sorted(_HOLE_ARMS))
def test_a_match_over_a_hole_is_not_judged_for_coverage(arms: str) -> None:
    source = _FN.format(body="match ? {{\n    " + _HOLE_ARMS[arms] + "\n  }}")
    source = source.replace("{{", "{").replace("}}", "}")
    assert _all_codes(source) == ["W001"]


def test_the_hole_filled_is_judged() -> None:
    """The neighbour: a scrutinee with a type is judged as before."""
    source = _FN.format(body="match @Int.0 {\n    1 -> 1,\n    2 -> 0\n  }")
    assert _codes(source) == ["E313"]


def test_an_unknown_no_diagnostic_stands_behind_is_still_judged() -> None:
    """`apply_fn` over a type variable is `Unknown` with nothing reported, and
    its E313 is the error that refuses the program (#1671's boundary)."""
    source = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match apply_fn(@T.0, 1) {
    1 -> 1
  }
}
"""
    assert "E313" in _codes(source)


def test_repro_1563_a_match_over_a_hole_draws_only_the_hole() -> None:
    """The issue's line: W001, then E313 at the `match`, at base."""
    source = _FN.format(
        body="match ? {{\n    Some(@Int) -> @Int.0,\n    None -> 0\n  }}")
    source = source.replace("{{", "{").replace("}}", "}")
    assert _all_codes(source) == ["W001"]


# ---------------------------------------------------------------------------
# The verifier: a refused binder holds its predicate for the rest of its scope
# ---------------------------------------------------------------------------

_BINDER = """\
type Pos = { @Int | @Int.0 > 0 };

private fn need(@Int -> @Int)
  requires(@Int.0 REQ)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn mk(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

private fn pair(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, 1)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  BODY
}
"""

#: Each binder spelling, over a value the bind cannot prove (so the bind is
#: refused), and the call that reads the binder.
_BINDERS = {
    "let": "let @T = @Int.0 - 5;\n  need(@T.0)",
    "arm": ("match mk(@Int.0 - 5) {\n    Some(@T) -> need(@T.0),\n"
            "    None -> 0\n  }"),
    "binding_pattern": "match @Int.0 - 5 {\n    @T -> need(@T.0)\n  }",
    "destructure_literal": (
        "let Tuple<@T, @Int> = Tuple(@Int.0 - 5, 1);\n  need(@T.0)"),
    "destructure_call": (
        "let Tuple<@T, @Int> = pair(@Int.0 - 5);\n  need(@T.0)"),
}

#: The binder's type, its predicate as the callee's precondition, and the
#: bind's own refusal.
_TARGETS = {
    "Pos": ("> 0", {"E505"}),
    "Nat": (">= 0", {"E503"}),
}


def _binder_program(binder: str, target: str, req: str | None = None) -> str:
    pred, _ = _TARGETS[target]
    return (_BINDER.replace("REQ", req or pred)
            .replace("BODY", _BINDERS[binder].replace("@T", "@" + target)))


def _verified_codes(source: str) -> list[str]:
    verified = pipeline.verify(source)
    return [d.error_code for d in verified.errors]


@pytest.mark.parametrize("target", sorted(_TARGETS))
@pytest.mark.parametrize("binder", sorted(_BINDERS))
def test_a_refused_binder_draws_no_second_error(binder: str, target: str) -> None:
    """The bind is refused at the binder, and the call whose precondition is
    the binder's predicate is discharged by it: no E501 beside it."""
    codes = _verified_codes(_binder_program(binder, target))
    assert codes and set(codes) <= _TARGETS[target][1], codes


@pytest.mark.parametrize("target", sorted(_TARGETS))
@pytest.mark.parametrize("binder", sorted(_BINDERS))
def test_a_precondition_the_predicate_does_not_imply_is_still_refused(
        binder: str, target: str) -> None:
    """The negative space: the post-fact is the binder's predicate and no
    more, so a precondition beyond it (`> 10`) is still E501."""
    codes = _verified_codes(_binder_program(binder, target, req="> 10"))
    assert "E501" in codes, codes


def test_repro_1563_an_at_nat_arm_binder_draws_no_second_error() -> None:
    """The issue's second repro: E503 at the `Some(@Nat)` binder and E501 at
    `need_nn(@Nat.0)` at base; the `@Nat` binder's sign is guarded, so it
    holds where the arm runs."""
    assert _verified_codes(_binder_program("arm", "Nat")) == ["E503"]


def test_repro_1563_a_refused_destructured_binder_draws_no_second_error() -> None:
    """`let Tuple<@Pos, @Int> = Tuple(@Int.0 - 5, 1); need(@Pos.0)`: E505 and
    E501 at base, the destructure's literal component read unguarded by the
    walk that decides the call."""
    assert _verified_codes(
        _binder_program("destructure_literal", "Pos")) == ["E505"]


_CHAINED_NAT = """\
public fn f(@Nat, @Bool -> @Int)
  requires(@Nat.0 >= 20 && @Nat.0 <= 39)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2, 3, 4];
  let @Nat = array_length(@Array<Int>.0);
  let @Nat = if @Bool.0 then { @Nat.1 - 7 } else { @Nat.0 };
  @Nat.0 - -2
}
"""


def test_repro_a_guarded_binder_read_through_another_keeps_its_fact() -> None:
    """A guarded binder's value whose fact reads an earlier guarded binder's
    value: the query reads the second, and through its fact the first, so
    the first's fact holds there too (`SmtContext._facts_of_values_read`,
    closed over the facts).  Generator seed 177's `f2` lost its overflow
    proof to Tier 3 without the closure once a `@Nat` binder read its guard."""
    verified = pipeline.verify(_CHAINED_NAT)
    assert not verified.errors, [d.error_code for d in verified.errors]
    overflow = [o.status for o in verified.obligations
                if o.kind == "int_overflow"]
    assert overflow and set(overflow) == {"verified"}, [
        (o.kind, o.status) for o in verified.obligations]


# ---------------------------------------------------------------------------
# The class's further members (PR #1842 review): the hole at a destructure,
# a refused name read above its declaration, the placeholder through a
# generic's substitution, and every operator over the placeholder
# ---------------------------------------------------------------------------

_SIG = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def test_a_destructure_of_a_hole_draws_only_the_hole() -> None:
    """The destructuring `let` reads the reported-`Unknown` rule the `match`
    reads (`_unknown_is_reported`): `let Tuple<@Int, @Int> = ?;` drew E313
    beside the hole's W001."""
    source = f"public fn f(@Int -> @Int)\n{_SIG}{{\n  let Tuple<@Int, @Int> = ?;\n  @Int.0\n}}\n"
    assert _all_codes(source) == ["W001"]


_ABOVE = {
    "alias_first": ("type M = Decimal<Int>;\nprivate data Decimal {\n  MkDecimal(Int)\n}\n\n"
                    f"public fn f(@Int -> @Int)\n{_SIG}{{\n  0\n}}\n"),
    "signature_first": (f"private fn g(@Decimal<Int> -> @Int)\n{_SIG}{{\n  0\n}}\n\n"
                        "private data Decimal {\n  MkDecimal(Int)\n}\n"),
}


@pytest.mark.parametrize("order", sorted(_ABOVE))
def test_a_refused_name_above_its_declaration_reports_nothing_further(
        order: str) -> None:
    """The refused built-in names are known before the namespace resolves
    anything, so an alias or a signature above `data Decimal` reads the name
    as one below it does: E158 alone (the base drew E158 alone above, and
    E135 beside it for the signature; filled at the declaration, E134)."""
    assert _codes(_ABOVE[order]) == ["E158"]


_GENERIC = {
    "return": (f"private forall<T> fn mk(@T -> @Optio<T>)\n{_SIG}{{\n  ?\n}}\n\n"
               + _FN.format(body="let @Option<Int> = mk(1);\n  0")),
    "parameter": (f"private forall<T> fn tk(@Optio<T> -> @Int)\n{_SIG}{{\n  0\n}}\n\n"
                  + _FN.format(body="tk(Some(1))")),
}


@pytest.mark.parametrize("site", sorted(_GENERIC))
def test_the_placeholder_survives_a_generics_substitution(site: str) -> None:
    """A rebuild of a data type over new arguments keeps its class
    (`AdtType.with_args`), so `Optio<T>` instantiated is still the
    placeholder: no E170 at the `let`, no E202 at the argument."""
    codes = _codes(_GENERIC[site])
    assert codes and set(codes) == {"E136"}, codes


_OPERATORS = {
    "add": "@Qzt.0 + 1",
    "negate": "-@Qzt.0",
    "not": "!@Qzt.0",
    "compare": "@Qzt.0 < 1",
    "and": "@Qzt.0 && true",
    "index": "@Qzt.0[0]",
    "interpolate": '"\\(@Qzt.0)"',
    "condition": "if @Qzt.0 then { 1 } else { 0 }",
}


@pytest.mark.parametrize("op", sorted(_OPERATORS))
def test_an_operator_over_the_placeholder_draws_nothing_further(op: str) -> None:
    """Every operator's early guard admits the placeholder as it admits
    `Unknown` (`types.is_unknown_like`): `@Qzt.0 + 1` drew E140, `-` E147,
    `<` E143 and an index E161 beside the E136 (the base drew those, and
    E146, E144, E148 and E300 for the other four, which the compatible
    placeholder already removes)."""
    source = (f"private fn f(@Qzt -> @Int)\n{_SIG}{{\n  let @Int = 0;\n"
              f"  {_OPERATORS[op]};\n  0\n}}\n")
    assert _codes(source) == ["E136"]
