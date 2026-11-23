"""A sibling's type fixes no variable, whichever wrapper hands it down and
whatever object it is (#1866).

An `if` branch or a `match` arm whose type a call left open is synthesized
again against its sibling's type (`_synth_against`), so a constructor takes
the type arguments it cannot fix itself.  That type is no type the value is
expected at (spec §5.9), so it fixes no variable a call leaves open, and
fills no literal's hole.  Before #1866 the check told the sibling's type
from another expected type by the object's identity (`_part_of`): an index
wraps the type in a new `Array`, so the sibling fixed the indexed call in
three arm orders of four, and a callee's parameter that is the shared
`Int` object was taken for the sibling's, so a call accepted outside a
branch was refused inside one, except where the `match` put it first.

Now every site that hands an expected type down states where it came from
(`_synth_expr`'s *from_sibling*).  `SITES` lists each such site with the
origin it states and the forms that reach it; `test_every_handoff_is_
classified` holds the code to the table, so a new site fails until it is
classified and given a form, and the matrix runs every form in every join
and both orders against its control, the same expression with no sibling:
the order of the arms never decides a verdict, and a branch is judged as
the same expression outside one.
"""

from __future__ import annotations

import ast as pyast
import re
from collections import Counter
from pathlib import Path
from typing import NamedTuple

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/calls.py",
    "vera/checker/control.py",
    "vera/checker/core.py",
    "vera/checker/expressions.py",
    "vera/checker/resolution.py",
])

ROOT = Path(__file__).resolve().parent.parent

_PRELUDE = """\
type PosInt = { @Int | @Int.0 > 0 };

type UF = fn(Unit -> Int) effects(pure);

private data Q<A, B> { MkQ(Option<A>, B, B) }

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private forall<U> fn pick(@U, @U -> @U)
  requires(true)
  ensures(true)
  effects(pure)
{
  @U.0
}

private forall<T where Ord<T>> fn empty_ord(@Unit -> @Array<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  []
}

private forall<T where Ord<T>> fn head_ord(@Array<T> -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}

private fn take(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

"""

#: The sibling's type and the slot that has it.
_FAMILIES = {
    "int": "Int",
    "posint": "PosInt",
    "tuple": "Tuple<Option<Int>, Int>",
    "tuple_nat": "Tuple<Option<Int>, Nat>",
    "option": "Option<Int>",
    "array": "Array<Int>",
    "q": "Q<Int, Int>",
    "q_bool": "Q<Int, Bool>",
    "q_unit": "Q<Int, Unit>",
    "q_fn": "Q<Int, UF>",
}


class Form(NamedTuple):
    family: str
    #: The arm whose type a call leaves open.
    open_: str
    #: The same expression with no sibling: the construction's open part
    #: given by a literal where the sibling would give it.
    control: str
    #: The control's codes, pinned so a control that stops meaning
    #: anything shows.
    codes: tuple[str, ...]
    stage: str = "check"


_IDX = "empty_ord(())[0]"
_NESTED_IF = f"if @Bool.0 then {{ {_IDX} }} else {{ {_IDX} }}"
_NESTED_MATCH = f"match @Bool.0 {{ true -> {_IDX}, false -> {_IDX} }}"
_STATE = ("handle[State<Int>](@Int = {init}) {{ get(@Unit) -> "
          "{{ resume(@Int.0) }}, put(@Int) -> {{ resume(()) }}{upd} }} "
          "in {{ {body} }}")

FORMS: dict[str, Form] = {
    # The sibling's type itself, and each part of it handed down.
    "direct": Form("int", "head_ord([])", "head_ord([])", ("E613",)),
    "index": Form("int", _IDX, _IDX, ("E613",)),
    "index_refined": Form("posint", _IDX, _IDX, ("E613",)),
    "index_component": Form("tuple", f"Tuple(None, {_IDX})",
                            f"Tuple(Some(1), {_IDX})", ("E613",)),
    "index_field": Form("option", f"Some({_IDX})", f"Some({_IDX})",
                        ("E613",)),
    "index_element": Form("array", f"[{_IDX}]", f"[{_IDX}]", ("E613",)),
    "nested_if": Form("int", _NESTED_IF, _NESTED_IF, ("E613", "E613")),
    "nested_match": Form("int", _NESTED_MATCH, _NESTED_MATCH,
                         ("E613", "E613")),
    "block_tail": Form("int", f"{{ let @Int = 1; {_IDX} }}",
                       f"{{ let @Int = 1; {_IDX} }}", ("E613",)),
    "field_sibling_only": Form(
        "q", "MkQ(None, head_ord([]), head_ord([]))",
        "MkQ(Some(1), head_ord([]), head_ord([]))", ("E613", "E613")),
    # A type the context gives, whatever object it is.
    "callee_param": Form("tuple", "Tuple(None, take(head_ord([])))",
                         "Tuple(Some(1), take(head_ord([])))", ()),
    "generic_callee_param": Form(
        "tuple", "Tuple(None, pick(head_ord([]), 5))",
        "Tuple(Some(1), pick(head_ord([]), 5))", ()),
    "apply_fn_param": Form(
        "tuple", "Tuple(None, apply_fn(fn(@Int -> @Int) effects(pure) "
        "{ @Int.0 }, head_ord([])))",
        "Tuple(Some(1), apply_fn(fn(@Int -> @Int) effects(pure) "
        "{ @Int.0 }, head_ord([])))", ()),
    "op_param": Form(
        "tuple", "Tuple(None, { IO.print(head_ord([])); 1 })",
        "Tuple(Some(1), { IO.print(head_ord([])); 1 })", ()),
    # An ability operation's parameter fixes no open call's variable
    # outside a branch either (E241); the branch is judged the same.
    "ability_op_param": Form(
        "tuple", "Tuple(None, match compare(head_ord([]), 5) "
        "{ Less -> 1, _ -> 2 })",
        "Tuple(Some(1), match compare(head_ord([]), 5) "
        "{ Less -> 1, _ -> 2 })", ("E241",)),
    "field_other_arg": Form("q", "MkQ(None, head_ord([]), 5)",
                            "MkQ(Some(1), head_ord([]), 5)", ()),
    "field_literal": Form("q", "MkQ(None, idg(5), 7)",
                          "MkQ(Some(1), idg(5), 7)", ()),
    "state_init": Form(
        "tuple",
        "Tuple(None, " + _STATE.format(init="head_ord([])", upd="",
                                       body="get(())") + ")",
        "Tuple(Some(1), " + _STATE.format(init="head_ord([])", upd="",
                                          body="get(())") + ")", ()),
    "state_update": Form(
        "tuple",
        "Tuple(None, " + _STATE.format(
            init="0", upd=" with @Int = head_ord([])",
            body="put(1); get(())") + ")",
        "Tuple(Some(1), " + _STATE.format(
            init="0", upd=" with @Int = head_ord([])",
            body="put(1); get(())") + ")", ()),
    "eq_right_operand": Form(
        "tuple", "Tuple(None, if Some(1) == Some(head_ord([])) then "
        "{ 1 } else { 2 })",
        "Tuple(Some(1), if Some(1) == Some(head_ord([])) then "
        "{ 1 } else { 2 })", ()),
    "eq_left_operand": Form(
        "tuple", "Tuple(None, if Some(head_ord([])) == Some(1) then "
        "{ 1 } else { 2 })",
        "Tuple(Some(1), if Some(head_ord([])) == Some(1) then "
        "{ 1 } else { 2 })", ()),
    "let": Form("tuple", "Tuple(None, { let @Int = head_ord([]); @Int.0 })",
                "Tuple(Some(1), { let @Int = head_ord([]); @Int.0 })", ()),
    "let_destructure": Form(
        "tuple", "Tuple(None, { let Tuple<@Int, @Int> = "
        "Tuple(head_ord([]), 1); @Int.0 })",
        "Tuple(Some(1), { let Tuple<@Int, @Int> = "
        "Tuple(head_ord([]), 1); @Int.0 })", ("E613",)),
    "lambda_return": Form(
        "tuple", "Tuple(None, apply_fn(fn(@Unit -> @Int) effects(pure) "
        "{ head_ord([]) }, ()))",
        "Tuple(Some(1), apply_fn(fn(@Unit -> @Int) effects(pure) "
        "{ head_ord([]) }, ()))", ()),
    # A literal's hole: a sibling's `Nat` placed `0 - 3` at `Nat`.
    "literal_hole": Form("tuple_nat", "Tuple(None, idg(0 - 3))",
                         "Tuple(Some(1), idg(0 - 3))", (), "verify"),
}

#: Each site that hands down a type of its own, in a constructor's field
#: whose type is a part of the sibling's: the site's own synthesis then
#: carries the sibling's origin (a `Tuple`'s component is synthesized with
#: no expected type, so it carries none), and the type the site hands
#: down must not.  (The value, the second field's argument, the family.)
_IN_FIELD = {
    "callee_param": ("take(head_ord([]))", "5", "q"),
    "generic_callee_param": ("pick(head_ord([]), 5)", "5", "q"),
    "apply_fn_param": ("apply_fn(fn(@Int -> @Int) effects(pure) "
                       "{ @Int.0 }, head_ord([]))", "5", "q"),
    "op_param": ("IO.print(head_ord([]))", "()", "q_unit"),
    "state_init": (_STATE.format(init="head_ord([])", upd="",
                                 body="get(())"), "5", "q"),
    "state_update": (_STATE.format(init="0", upd=" with @Int = head_ord([])",
                                   body="put(1); get(())"), "5", "q"),
    "eq_right_operand": ("Some(1) == Some(head_ord([]))", "true", "q_bool"),
    "eq_left_operand": ("Some(head_ord([])) == Some(1)", "true", "q_bool"),
    "let": ("{ let @Int = head_ord([]); @Int.0 }", "5", "q"),
    "lambda_return": ("fn(@Unit -> @Int) effects(pure) { head_ord([]) }",
                      "fn(@Unit -> @Int) effects(pure) { 1 }", "q_fn"),
}
for _name, (_value, _other, _family) in _IN_FIELD.items():
    FORMS[f"{_name}_in_field"] = Form(
        _family, f"MkQ(None, {_value}, {_other})",
        f"MkQ(Some(1), {_value}, {_other})", ())


class Site(NamedTuple):
    module: str
    function: str
    callee: str
    expected: str
    origin: str


def _site(module: str, function: str, callee: str, expected: str,
          origin: str) -> Site:
    return Site(module, function, callee, expected, origin)


_S = "_synth_expr"
_L = "_check_in_literal_context"
_FWD = "self._expected_from_sibling"

#: Every site that hands an expected type to a sub-expression, the origin
#: it states, how many calls of that shape it has, and the forms that reach
#: it (or why none can: a site no branch's call meets).
SITES: dict[Site, tuple[int, tuple[str, ...] | str]] = {
    _site("control.py", "_synth_against", _S, "sibling", "True"): (
        1, ("direct",)),
    _site("control.py", "_check_if", _S, "expected", _FWD): (
        2, ("nested_if",)),
    _site("control.py", "_check_match", _S, "expected", _FWD): (
        1, ("nested_match",)),
    _site("expressions.py", "_check_block", _S, "expected", _FWD): (
        1, ("block_tail",)),
    _site("expressions.py", "_check_index", _S,
          "AdtType('Array', (expected,))", _FWD): (1, ("index",)),
    _site("expressions.py", "_check_index", _L,
          "AdtType('Array', (expected,))", _FWD): (1, ("index_refined",)),
    _site("calls.py", "_check_tuple_constructor", _L, "components[i]",
          _FWD): (1, ("index_component", "literal_hole")),
    _site("expressions.py", "_check_array_lit", _L, "element_ctx", _FWD): (
        1, ("index_element",)),
    _site("calls.py", "_check_constructor_call", _S, "field_expected",
          _FWD): (1, ("index_field",)),
    _site("calls.py", "_check_constructor_call", _S, "field_ty",
          "sibling_fields[i]"): (
        2, ("field_sibling_only", "field_other_arg", "field_literal")),
    _site("expressions.py", "_check_in_literal_context", _S, "context",
          "from_sibling"): (
        1, ("index_refined", "index_component", "index_element")),
    _site("calls.py", "_check_fn_call_with_info", _S, "exp", "False"): (
        1, ("callee_param", "callee_param_in_field")),
    _site("calls.py", "_check_fn_call_with_info", _S, "param_ty",
          "False"): (4, ("generic_callee_param",
                         "generic_callee_param_in_field")),
    _site("calls.py", "_check_apply_fn", _S, "exp", "False"): (
        1, ("apply_fn_param", "apply_fn_param_in_field")),
    _site("calls.py", "_check_apply_fn", _S, "param_ty", "False"): (
        2, ("apply_fn_param", "lambda_return")),
    _site("calls.py", "_check_op_call", _S, "exp", "False"): (
        1, ("op_param", "op_param_in_field")),
    _site("calls.py", "_check_ability_op_call", _S, "param_ty", "False"): (
        1, ("ability_op_param",)),
    _site("control.py", "_check_handle", _S, "state_type", "False"): (
        2, ("state_init", "state_update", "state_init_in_field",
            "state_update_in_field")),
    _site("expressions.py", "_resynth_eq_ctor_operand", _S, "left_ty",
          "False"): (1, ("eq_right_operand", "eq_right_operand_in_field")),
    _site("expressions.py", "_resynth_eq_ctor_operand", _S, "right_ty",
          "False"): (1, ("eq_left_operand", "eq_left_operand_in_field")),
    _site("expressions.py", "_check_let", _S, "declared_type", "False"): (
        1, ("let", "let_in_field")),
    _site("expressions.py", "_check_let_destruct", _L,
          "AdtType('Tuple', tuple(resolved_types))", "False"): (
        1, ("let_destructure",)),
    _site("expressions.py", "_check_anon_fn", _S, "ret_type", "False"): (
        1, ("lambda_return", "lambda_return_in_field")),
    _site("core.py", "_check_fn", _S, "return_type", "False"): (
        1, "a function's body is a declaration's, never a branch's"),
    _site("expressions.py", "_check_binary", _S, "BYTE", "False"): (
        2, "an integer literal operand, which no call leaves open"),
}

#: Calls that pass `expected=` something other than their own `expected`
#: and are no handoff to a sub-expression's synthesis: each is read in the
#: frame of the synthesis in progress.
SAME_FRAME = {
    ("calls.py", "_infer_ctor_type_args", "_infer_type_args_in_context"):
        "the construction's own expected type, narrowed to its data type",
    ("expressions.py", "_check_hole", "HoleSite"):
        "a hole's record of the type's text",
}

_HANDOFFS = {_S: "expected", _L: 2}


class _Scan(pyast.NodeVisitor):
    def __init__(self, module: str) -> None:
        self.module = module
        self.stack: list[str] = []
        self.sites: Counter[Site] = Counter()
        self.other: set[tuple[str, str, str]] = set()

    def visit_FunctionDef(self, node: pyast.FunctionDef) -> None:
        self.stack.append(node.name)
        self.generic_visit(node)
        self.stack.pop()

    def visit_Call(self, node: pyast.Call) -> None:
        func = node.func
        name = (func.attr if isinstance(func, pyast.Attribute)
                else getattr(func, "id", ""))
        kws = {k.arg: k.value for k in node.keywords}
        where = self.stack[-1] if self.stack else "<module>"
        if name in _HANDOFFS:
            at = _HANDOFFS[name]
            exp = (kws.get("expected") if isinstance(at, str)
                   else node.args[at] if len(node.args) > at else None)
            if exp is not None:
                origin = kws.get("from_sibling")
                self.sites[Site(
                    self.module, where, name, pyast.unparse(exp),
                    "<unstated>" if origin is None
                    else pyast.unparse(origin))] += 1
        elif ("expected" in kws
                and pyast.unparse(kws["expected"]) != "expected"):
            self.other.add((self.module, where, name))
        self.generic_visit(node)


def _scan() -> tuple[Counter[Site], set[tuple[str, str, str]]]:
    sites: Counter[Site] = Counter()
    other: set[tuple[str, str, str]] = set()
    for path in sorted((ROOT / "vera" / "checker").glob("*.py")):
        scan = _Scan(path.name)
        scan.visit(pyast.parse(path.read_text(encoding="utf-8")))
        sites += scan.sites
        other |= scan.other
    return sites, other


def test_every_handoff_is_classified() -> None:
    """Every call that hands a sub-expression an expected type states its
    origin, and is the site the table names with that origin, as many
    times: a new site, or one whose origin changes, fails here until it is
    classified and given a form."""
    sites, other = _scan()
    assert dict(sites) == {s: n for s, (n, _) in SITES.items()}
    assert other == set(SAME_FRAME)


def test_every_form_is_reached_by_a_site() -> None:
    named = {f for _, forms in SITES.values() if not isinstance(forms, str)
             for f in forms}
    assert named == set(FORMS)


#: Each join of a sibling and an open arm, in both orders.
JOINS = {
    "if_sibling_first": "if @Bool.0 then {{ {sib} }} else {{ {open_} }}",
    "if_open_first": "if @Bool.0 then {{ {open_} }} else {{ {sib} }}",
    "match_sibling_first": (
        "match @Bool.0 {{ false -> {sib}, true -> {open_} }}"),
    "match_open_first": (
        "match @Bool.0 {{ true -> {open_}, false -> {sib} }}"),
    "handler_sibling_clause": (
        "handle[Exn<Bool>] {{ throw(@Bool) -> {sib} }} in {{ {open_} }}"),
    "handler_open_clause": (
        "handle[Exn<Bool>] {{ throw(@Bool) -> {open_} }} in {{ {sib} }}"),
}


def _program(family: str, body: str) -> str:
    stype = _FAMILIES[family]
    return (_PRELUDE + f"public fn g(@Bool, @{stype} -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(<IO>)\n{\n"
            f"  {body};\n  0\n}}\n")


def _codes(source: str, stage: str) -> tuple[str, ...]:
    result = (pipeline.verify(source) if stage == "verify"
              else pipeline.check(source))
    return tuple(sorted(str(e.error_code) for e in result.errors))


@pytest.mark.parametrize("form", list(FORMS))
def test_the_control_means_what_it_pins(form: str) -> None:
    f = FORMS[form]
    assert _codes(_program(f.family, f.control), f.stage) == f.codes


@pytest.mark.parametrize("join", list(JOINS))
@pytest.mark.parametrize("form", list(FORMS))
def test_a_branch_is_judged_as_the_same_value_outside_one(
        form: str, join: str) -> None:
    """The open arm beside its sibling, in each join and order, has the
    codes the same expression has with no sibling."""
    f = FORMS[form]
    sib = f"@{_FAMILIES[f.family]}.0"
    body = JOINS[join].format(sib=sib, open_=f.open_)
    assert _codes(_program(f.family, body), f.stage) == f.codes


# ---------------------------------------------------------------------
# The issue's two programs, in every order
# ---------------------------------------------------------------------

_ISSUE_PRE = _PRELUDE + """\
private fn g(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  idg(JOIN)
}
"""

_ORDERS_1 = {
    "match_sibling_first": (
        "match @Bool.0 { false -> @Int.0, true -> empty_ord(())[0] }"),
    "match_open_first": (
        "match @Bool.0 { true -> empty_ord(())[0], false -> @Int.0 }"),
    "if_sibling_first": "if @Bool.0 then { @Int.0 } else { empty_ord(())[0] }",
    "if_open_first": "if @Bool.0 then { empty_ord(())[0] } else { @Int.0 }",
}


def test_repro_an_index_hides_no_sibling() -> None:
    """`idg(match @Bool.0 { false -> @Int.0, true -> empty_ord(())[0] })`:
    the index hands `empty_ord` its sibling's `Int` wrapped in a new
    `Array`, which fixed `T` at `Int` in three orders of four; nothing
    else gives the call a type, so it is refused in all four, as the same
    call with no index is."""
    got = {order: _codes(_ISSUE_PRE.replace("JOIN", join), "check")
           for order, join in _ORDERS_1.items()}
    assert got == dict.fromkeys(_ORDERS_1, ("E613",))


_ISSUE_2 = _PRELUDE + """\
private fn g(@Bool, @Tuple<Option<Int>, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match JOIN {
    Tuple(@Option<Int>, @Int) -> @Int.0
  }
}
"""

_O2 = "Tuple(None, take(head_ord([])))"
_S2 = "@Tuple<Option<Int>, Int>.0"
_ORDERS_2 = {
    "if_open_first": f"if @Bool.0 then {{ {_O2} }} else {{ {_S2} }}",
    "if_sibling_first": f"if @Bool.0 then {{ {_S2} }} else {{ {_O2} }}",
    "match_open_first": f"match @Bool.0 {{ true -> {_O2}, false -> {_S2} }}",
    "match_sibling_first": (
        f"match @Bool.0 {{ false -> {_S2}, true -> {_O2} }}"),
}


def test_repro_a_callee_s_parameter_is_no_sibling_s_type() -> None:
    """`take(head_ord([]))` in a branch beside a `Tuple<Option<Int>, Int>`:
    `take`'s parameter is the shared `Int` object, the same as the
    sibling's component, and was read as the sibling's, so the call was
    refused in three orders of four (E613); it is `take`'s, and fixes
    `head_ord` at `Int` in all four, as outside a branch."""
    got = {order: _codes(_ISSUE_2.replace("JOIN", join), "check")
           for order, join in _ORDERS_2.items()}
    assert got == dict.fromkeys(_ORDERS_2, ())


def test_repro_a_sibling_fills_no_literal_s_hole() -> None:
    """`Tuple(None, idg(0 - 3))` beside a `Tuple<Option<Int>, Nat>`: the
    sibling's `Nat` filled the literal's hole, `idg` at `Nat`, and the -3
    was refuted (E503) in three orders of four; a sibling's type is no
    context, so `idg` is at `Int` in all four."""
    f = FORMS["literal_hole"]
    sib = f"@{_FAMILIES[f.family]}.0"
    got = {join: _codes(_program(f.family, JOINS[join].format(
        sib=sib, open_=f.open_)), "verify")
        for join in ("if_sibling_first", "if_open_first",
                     "match_sibling_first", "match_open_first")}
    assert set(got.values()) == {()}, got


def test_repro_the_fix_binds_the_open_call_in_the_arm() -> None:
    """E613 at an index a sibling no longer types names the `let` that
    does, written where the call is; made in the arm, the program checks
    clean in every order."""
    source = _ISSUE_PRE.replace("JOIN", _ORDERS_1["match_open_first"])
    (found,) = [e for e in pipeline.check(source).errors
                if e.error_code == "E613"]
    assert found.fix == (
        "No argument of 'empty_ord(())' fixes T, so the call instantiates "
        "'empty_ord' at Bool, nothing giving its result a type: bind its "
        "result at a type that supports 'Ord', where the call is: "
        "`let @Array<Int> = empty_ord(());`, then `@Array<Int>.0` in its "
        "place; or give 'empty_ord' a parameter that carries T ('@T' for "
        "example) and pass it a value at a type that supports 'Ord', Int "
        "for example."), found.fix
    let, slot = re.findall(r"`([^`]+)`", found.fix)[:2]
    arm = f"{{ {let} {slot}[0] }}"
    for order, join in _ORDERS_1.items():
        fixed = _ISSUE_PRE.replace(
            "JOIN", join.replace("empty_ord(())[0]", arm))
        assert _codes(fixed, "check") == (), order
