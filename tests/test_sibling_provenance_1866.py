"""A sibling's type is no expected type: a branch is judged as the same
value outside one (#1866).

Before #1866 an `if` branch or a `match` arm whose type a call left open
was synthesized again against its sibling's type, and the check told that
type from one the context gives by the object's identity (`_part_of`):
an index wrapped it in a new `Array`, a callee's parameter that is the
shared `Int` object was taken for it, and a constructor's field
expectation carried it into the constructor's inference
(`MkW(None, head_ord([]), None)`).  Each moved a verdict with the order of
the arms.

Now no join hands an arm a type derived from another arm's: each arm is
synthesized once, against the type the join's context expects, and the
join completes in an arm's recorded types only the variables its
constructors left open (`_complete_arms`), never one a call's
instantiation holds.  `test_no_join_hands_an_arm_s_type_down` holds every
join to that rule, and the matrix runs every form in every join and both
orders against its control, the same expression with no sibling.
"""

from __future__ import annotations

import ast as pyast
import functools
import re
from collections import Counter
from pathlib import Path
from typing import NamedTuple

import pytest

from tests import pipeline
from vera import ast as vast
from vera import fold
from vera.types import contains_typevar

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

private data W<A, B> { MkW(Option<A>, B, Option<B>) }

private data V<B> { MkV(Array<B>, B) }

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

private forall<T where Ord<T>> fn ido(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private forall<T> fn none_any(@Unit -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  None
}

private forall<T> fn first(@Array<T> -> @T)
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
    "q_nat": "Q<Int, Nat>",
    "array_option_nat": "Array<Option<Nat>>",
    "q_tuple_open": "Q<Int, Tuple<Nat, Option<Bool>>>",
    "w": "W<Int, Int>",
    "v": "V<Int>",
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
    # A field whose variable no argument's type binds: the sibling gives
    # the construction's type its argument, and the argument is held to
    # the field's type the arguments give, as outside a branch (with the
    # sibling's `Int` in it, `Option<Int>`, the arm was refused, E213).
    "field_only_sibling_binds": Form("q", "MkQ(first([]), 1, 2)",
                                     "MkQ(first([]), 1, 2)", ()),
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
    # An ability operation's constructor argument, synthesized again
    # against the parameter its other argument fixes: the `Some` takes the
    # parameter's `Int` into its field, which fixes `head_ord`.
    "ability_op_ctor_arg": Form(
        "tuple", "Tuple(None, if eq(Some(1), Some(head_ord([]))) then "
        "{ 1 } else { 2 })",
        "Tuple(Some(1), if eq(Some(1), Some(head_ord([]))) then "
        "{ 1 } else { 2 })", ()),
    # A destructure's bindings are the type its generic call is expected
    # at: `idg` at `Tuple<Nat, Nat>`, and the -3 is refuted, in a branch as
    # outside one.
    "let_destructure_nat": Form(
        "tuple", "Tuple(None, { let Tuple<@Nat, @Nat> = "
        "idg(Tuple(1, 0 - 3)); 5 })",
        "Tuple(Some(1), { let Tuple<@Nat, @Nat> = "
        "idg(Tuple(1, 0 - 3)); 5 })", ("E503",), "verify"),
    "let_destructure_nat_in_field": Form(
        "q", "MkQ(None, { let Tuple<@Nat, @Nat> = idg(Tuple(1, 0 - 3)); 5 }, "
        "5)",
        "MkQ(Some(1), { let Tuple<@Nat, @Nat> = idg(Tuple(1, 0 - 3)); 5 }, "
        "5)", ("E503",), "verify"),
    # A generic call's argument whose literal the instantiation types
    # (`pick` at `Nat` from its other argument): checked against that
    # instantiation, a type of the context's, the -3 is refuted, in a
    # constructor's field beside a sibling as outside one.
    # A constructor's field expectation from the sibling completed a
    # nested `None`, and the constructor's inference read it back as an
    # argument's type, fixing `B` and so `head_ord` (PR 1907, fourth
    # review); a call's result and an array literal carried it the same way.
    "nested_ctor_feeds_inference": Form(
        "w", "MkW(None, head_ord([]), None)",
        "MkW(None, head_ord([]), None)", ("E613",)),
    "nested_call_feeds_inference": Form(
        "w", "MkW(None, head_ord([]), none_any(()))",
        "MkW(None, head_ord([]), none_any(()))", ("E613",)),
    "nested_array_feeds_inference": Form(
        "v", "MkV([], head_ord([]))", "MkV([], head_ord([]))", ("E613",)),
    "generic_callee_hole_in_field": Form(
        "q", "MkQ(None, { let @Nat = 1; pick(@Nat.0, idg(0 - 3)) }, 5)",
        "MkQ(Some(1), { let @Nat = 1; pick(@Nat.0, idg(0 - 3)) }, 5)",
        ("E503",), "verify"),
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
    "ability_op_ctor_arg": ("eq(Some(1), Some(head_ord([])))", "true",
                            "q_bool"),
}
for _name, (_value, _other, _family) in _IN_FIELD.items():
    FORMS[f"{_name}_in_field"] = Form(
        _family, f"MkQ(None, {_value}, {_other})",
        f"MkQ(Some(1), {_value}, {_other})", ())


#: The functions that join values (`_join`, `_join_parts`, `_join_either`,
#: `_value_join`): an `if`'s branches, a `match`'s arms, an `Exn`
#: handler's clauses, an array literal's elements, and the checks that
#: fit one type to another.
_JOINS = frozenset({"_join", "_join_parts", "_join_either", "_value_join"})
#: The sub-expressions whose type a join may hand down: they are no arm.
_NOT_ARMS = frozenset({"condition", "scrutinee"})


def _refused_expectations(fn: pyast.FunctionDef) -> list[str]:
    """Each `expected=` in *fn* a join may not write: one that names a
    value derived from an arm's synthesized type.  A name is derived when
    it is assigned the result of `_synth_expr` on anything but a condition
    or a scrutinee, or any expression naming a derived name; the closure
    is taken to a fixed point.  Allowed: the function's own `expected`
    parameter, a type no arm gave (a condition's `Bool`), and a
    scrutinee's own type."""
    tainted: set[str] = set()

    def names(node: pyast.AST) -> set[str]:
        return {n.id for n in pyast.walk(node) if isinstance(n, pyast.Name)}

    def from_arm(value: pyast.AST) -> bool:
        for call in pyast.walk(value):
            if (isinstance(call, pyast.Call)
                    and isinstance(call.func, pyast.Attribute)
                    and call.func.attr == "_synth_expr" and call.args):
                arg = call.args[0]
                if not (isinstance(arg, pyast.Attribute)
                        and arg.attr in _NOT_ARMS):
                    return True
        return bool(names(value) & tainted)

    changed = True
    while changed:
        changed = False
        for node in pyast.walk(fn):
            targets: list[pyast.AST] = []
            value: pyast.AST | None = None
            if isinstance(node, pyast.Assign):
                targets, value = node.targets, node.value
            elif isinstance(node, (pyast.AnnAssign, pyast.AugAssign)):
                targets, value = [node.target], node.value
            elif isinstance(node, pyast.For):
                targets, value = [node.target], node.iter
            if value is None or not from_arm(value):
                continue
            for target in targets:
                new = names(target) - tainted
                if new:
                    tainted |= new
                    changed = True
    return [pyast.unparse(kw.value) for node in pyast.walk(fn)
            if isinstance(node, pyast.Call) for kw in node.keywords
            if kw.arg == "expected" and names(kw.value) & tainted]


def _join_functions() -> dict[str, pyast.FunctionDef]:
    found: dict[str, pyast.FunctionDef] = {}
    for path in sorted((ROOT / "vera" / "checker").glob("*.py")):
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        for fn in pyast.walk(tree):
            if (isinstance(fn, pyast.FunctionDef) and fn.name not in _JOINS
                    and any(isinstance(c, pyast.Call)
                            and isinstance(c.func, pyast.Attribute)
                            and c.func.attr in _JOINS
                            for c in pyast.walk(fn))):
                found[f"{path.name}:{fn.name}"] = fn
    return found


#: The rule, by shape: each row a join's body and whether its `expected=`
#: is allowed.  The rule is read off these rows.
_SHAPES: dict[str, tuple[str, bool]] = {
    "the join's own expected": (
        "t = self._synth_expr(expr.then_branch, expected=expected)", True),
    "a condition's Bool": (
        "c = self._synth_expr(expr.condition, expected=BOOL)", True),
    "a scrutinee's own type": (
        "s = self._synth_expr(expr.scrutinee)\n"
        "b = self._check_pattern(arm.pattern, expected=s)", True),
    "a sibling's type": (
        "t = self._synth_expr(expr.then_branch)\n"
        "e = self._synth_expr(expr.else_branch, expected=t)", False),
    "the joined type": (
        "t = self._synth_expr(expr.then_branch)\n"
        "j = self._join(t, BOOL)\n"
        "e = self._synth_expr(expr.else_branch, expected=j)", False),
    "a part of an arm's type": (
        "for arm in expr.arms:\n"
        "    a = self._synth_expr(arm.body)\n"
        "    self._synth_expr(x, expected=AdtType('Array', (a,)))", False),
}


@pytest.mark.parametrize("shape", list(_SHAPES))
def test_the_rule_reads_each_shape(shape: str) -> None:
    body, allowed = _SHAPES[shape]
    fn = pyast.parse("def j(self, expr, expected):\n"
                     + "\n".join("    " + ln for ln in body.splitlines())
                     ).body[0]
    assert isinstance(fn, pyast.FunctionDef)
    assert (_refused_expectations(fn) == []) is allowed


def test_no_join_hands_an_arm_s_type_down() -> None:
    """No function that joins values hands a sub-expression an expected
    type derived from an arm's type: a sibling's type, the joined type or
    a part of either (spec §5.9, #1866).  An arm is synthesized once,
    against the type the join's context expects; a new join, or a new
    hand-down from an arm's type, fails here."""
    joins = _join_functions()
    assert {"control.py:_check_if", "control.py:_check_match"} <= set(joins)
    refused = {name: bad for name, fn in joins.items()
               if (bad := _refused_expectations(fn))}
    assert refused == {}


def test_the_completion_has_one_writer_and_one_reader() -> None:
    """The mark of a constructor's variable is written where a constructor
    mints one and read by the join's completion alone, and the completion
    is called by the two joins whose arms it completes."""
    uses: Counter[tuple[str, str]] = Counter()
    calls: Counter[str] = Counter()
    source = ""
    for path in sorted((ROOT / "vera").rglob("*.py")):
        text = path.read_text(encoding="utf-8")
        source += text
        tree = pyast.parse(text)
        for fn in pyast.walk(tree):
            if not isinstance(fn, pyast.FunctionDef):
                continue
            for node in pyast.walk(fn):
                if (isinstance(node, pyast.Attribute)
                        and node.attr == "_constructor_minted"):
                    uses[(fn.name, type(node.ctx).__name__)] += 1
                if (isinstance(node, pyast.Call)
                        and isinstance(node.func, pyast.Attribute)
                        and node.func.attr == "_complete_arms"):
                    calls[fn.name] += 1
    assert set(uses) == {("__init__", "Store"),
                         ("_constructor_typevar", "Load"),
                         ("_complete_arms", "Load")}, uses
    assert calls == Counter({"_check_if": 1, "_check_match": 1}), calls
    assert "from_sibling" not in source and "_synth_against" not in source


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
    source = _program(f.family, JOINS[join].format(sib=sib, open_=f.open_))
    assert _codes(source, f.stage) == f.codes
    if not f.codes:
        # Accepted: each open generic is built where the control builds it,
        # so a sibling fixed no variable on the way to the same verdict.
        assert _instances(source) == _instances(
            _program(f.family, f.control))


#: The prelude's generics whose variables a call can leave open.
_OPEN_GENERICS = frozenset({"head_ord", "empty_ord", "first", "idg", "pick"})


@functools.cache
def _instances(source: str) -> frozenset[tuple[str, tuple[str, ...]]]:
    checked = pipeline.check(source)
    assert checked.ok, [e.format() for e in checked.errors]
    return frozenset((inst.key, inst.args) for inst in checked.typed.instances
                     if inst.key in _OPEN_GENERICS)


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
    """E613 at an index a sibling no longer types names the binding that
    does, as a block in the call's place; made in the arm, the program
    checks clean in every order."""
    source = _ISSUE_PRE.replace("JOIN", _ORDERS_1["match_open_first"])
    (found,) = [e for e in pipeline.check(source).errors
                if e.error_code == "E613"]
    assert found.fix == (
        "No argument of 'empty_ord(())' fixes T, so the call instantiates "
        "'empty_ord' at Bool, nothing giving its result a type: bind its "
        "result at a type that supports 'Ord', with the block "
        "`{ let @Array<Int> = empty_ord(()); @Array<Int>.0 }` in the "
        "call's place; or give 'empty_ord' a parameter that carries T "
        "('@T' for example) and pass it a value at a type that supports "
        "'Ord', Int for example."), found.fix
    (block,) = re.findall(r"`(\{ let [^`]+ \})`", found.fix)
    for order, join in _ORDERS_1.items():
        fixed = _ISSUE_PRE.replace(
            "JOIN", join.replace("empty_ord(())", block))
        assert _codes(fixed, "check") == (), order


# ---------------------------------------------------------------------
# A sibling's type is no narrowing target either (PR 1907 review)
# ---------------------------------------------------------------------

_MKQ = "MkQ(None, idg(0 - 3), 7)"
_MKQ_CTL = "MkQ(Some(1), idg(0 - 3), 7)"

#: Each site that hands a part of a sibling's type down, reaching an `Int`
#: argument (`idg(0 - 3)`) at a position the sibling holds at `Nat`: the
#: site's synthesis is against the sibling's part, and the type it records
#: as the value's target, which the verifier narrows to, must be the
#: context's (here none), as outside a branch.  (Family, open arm, control.)
TARGET_FORMS: dict[str, tuple[str, str, str]] = {
    "field": ("q_nat", _MKQ, _MKQ_CTL),
    "component": ("tuple_nat", "Tuple(None, idg(0 - 3))",
                  "Tuple(Some(1), idg(0 - 3))"),
    "element": ("array_option_nat", "[None, Some(idg(0 - 3))]",
                "[Some(1), Some(idg(0 - 3))]"),
    "index": ("q_nat", f"[{_MKQ}][0]", f"[{_MKQ_CTL}][0]"),
    "block": ("q_nat", f"{{ let @Int = 1; {_MKQ} }}",
              f"{{ let @Int = 1; {_MKQ_CTL} }}"),
    "nested_if": ("q_nat", f"if @Bool.0 then {{ {_MKQ} }} else {{ {_MKQ} }}",
                  f"if @Bool.0 then {{ {_MKQ_CTL} }} else {{ {_MKQ_CTL} }}"),
    "nested_match": (
        "q_nat", f"match @Bool.0 {{ true -> {_MKQ}, false -> {_MKQ} }}",
        f"match @Bool.0 {{ true -> {_MKQ_CTL}, false -> {_MKQ_CTL} }}"),
    # An index's collection checked again in the literal context the
    # sibling's part gives (`_check_index`'s second hand-off).
    "index_literal_context": ("q_nat", "MkQ(None, idg([0 - 3])[0], 7)",
                              "MkQ(Some(1), idg([0 - 3])[0], 7)"),
}


@functools.cache
def _verified(source: str) -> tuple[tuple[str, ...], tuple[tuple[str, str], ...]]:
    """The verdict and every obligation (kind, status) `vera verify` reports."""
    result = pipeline.verify(source)
    return (tuple(sorted(str(e.error_code) for e in result.errors)),
            tuple(sorted((str(o.kind), str(o.status))
                         for o in result.obligations)))


@pytest.mark.parametrize("join", list(JOINS))
@pytest.mark.parametrize("form", list(TARGET_FORMS))
def test_a_sibling_s_type_is_no_narrowing_target(form: str, join: str) -> None:
    """`MkQ(None, idg(0 - 3), 7)` beside a `Q<Int, Nat>`: re-synthesized
    against the sibling, the argument was recorded with the sibling's
    `Nat` as its target, so `vera verify` obligated a narrowing outside a
    branch has none (`nat_bind`, refuted E503 at main, a run-time check
    that trapped once the sibling stopped filling the literal's hole), in
    three orders of four.  Every obligation, in every join and order, is
    the control's."""
    family, open_, control = TARGET_FORMS[form]
    sib = f"@{_FAMILIES[family]}.0"
    cell = _program(family, JOINS[join].format(sib=sib, open_=open_))
    assert _verified(cell) == _verified(_program(family, control))


def test_repro_a_sibling_s_nat_is_no_target_for_an_int_argument() -> None:
    """The reported program, `MkQ(None, idg(0 - 3), 7)` beside a
    `Q<Int, Nat>`, as an `if` with the sibling first: no `nat_bind` stands
    at the argument, and the verdict is the construction's outside a
    branch."""
    cell = _program("q_nat", JOINS["if_sibling_first"].format(
        sib="@Q<Int, Nat>.0", open_=_MKQ))
    codes, rows = _verified(cell)
    assert codes == () and not any(k == "nat_bind" for k, _ in rows), rows


# ---------------------------------------------------------------------
# Killers: the sites the Mutation (diff) lane found no cell deciding
# ---------------------------------------------------------------------


def test_repro_an_ability_operation_s_constructor_argument_meets_its_parameter() -> None:
    """`eq(Some(1), Some(head_ord([])))`: the `Some` is synthesized again
    against the `Option<Int>` its sibling argument gives `eq`'s parameter,
    a type of the context's, so its field fixes `head_ord` at `Int`, plain
    and in a constructor's field beside a sibling.  Taken as a sibling's
    type the parameter fixes nothing (E613)."""
    for family, body in (
            ("tuple", FORMS["ability_op_ctor_arg"].control),
            ("q_bool", JOINS["if_sibling_first"].format(
                sib="@Q<Int, Bool>.0",
                open_=FORMS["ability_op_ctor_arg_in_field"].open_))):
        source = _program(family, body)
        assert _codes(source, "check") == (), body
        assert _instances(source) == frozenset({("head_ord", ("Int",))}), body


def test_repro_a_destructure_s_bindings_are_its_call_s_expected_type() -> None:
    """`let Tuple<@Nat, @Nat> = idg(Tuple(1, 0 - 3))`: the bindings are the
    type the call is expected at, so `idg` is built at `Tuple<Nat, Nat>`
    and the -3 is refuted (E503, a violated `nat_bind`), as
    `let @Nat = idg(0 - 3)` is; and so in a constructor's field beside a
    sibling, where the destructure's type is still its own."""
    plain = _program("int", "let Tuple<@Nat, @Nat> = idg(Tuple(1, 0 - 3)); "
                            "@Nat.0")
    assert _instances(plain) == frozenset({("idg", ("Tuple<Nat, Nat>",))})
    codes, rows = _verified(plain)
    assert codes == ("E503",) and ("nat_bind", "violated") in rows, rows
    in_field = _program("q", JOINS["if_sibling_first"].format(
        sib="@Q<Int, Int>.0",
        open_=FORMS["let_destructure_nat_in_field"].open_))
    assert _instances(in_field) == frozenset({("idg", ("Tuple<Nat, Nat>",))})
    assert _verified(in_field)[0] == ("E503",)


def test_repro_a_generic_call_s_literal_meets_its_instantiation() -> None:
    """`pick(@Nat.0, idg(0 - 3))`: `pick` is at `Nat`, and its argument is
    checked again against that instantiation (#1541), so `idg` is at `Nat`
    and the -3 refuted (E503): outside a branch, in a constructor's field
    beside a sibling, and through a parameter a `None` leaves partly open
    (`Tuple<Nat, Option<T>>`, #1010)."""
    outside = _program("int", "{ let @Nat = 1; pick(@Nat.0, idg(0 - 3)); 0 }")
    partial = _program("int", "{ let @Nat = 1; pick(Tuple(idg(0 - 3), None), "
                              "Tuple(@Nat.0, None)); 0 }")
    in_field = _program("q", JOINS["if_sibling_first"].format(
        sib="@Q<Int, Int>.0",
        open_=FORMS["generic_callee_hole_in_field"].open_))
    for source in (outside, partial, in_field):
        assert ("idg", ("Nat",)) in _instances(source), source
        assert _verified(source)[0] == ("E503",), source


def test_repro_an_index_s_literal_context_keeps_the_sibling_s_origin() -> None:
    """`MkQ(None, idg([0 - 3])[0], 7)` beside a `Q<Int, Nat>`: the index
    checks its collection again in the context `Array<Nat>`, a part of the
    sibling's type, which fills no literal's hole, so `idg` is at
    `Array<Int>` and nothing is refuted, as outside a branch."""
    family, open_, control = TARGET_FORMS["index_literal_context"]
    cell = _program(family, JOINS["if_sibling_first"].format(
        sib="@Q<Int, Nat>.0", open_=open_))
    assert _instances(cell) == frozenset({("idg", ("Array<Int>",))})
    assert _verified(cell) == _verified(_program(family, control))
    assert _verified(cell)[0] == ()


def test_repro_a_value_with_no_target_records_none() -> None:
    """Checked against a sibling's type the value records no target, and
    neither table holds an entry that says so with `None`: the
    constructor-field gap fill (#1503) fills only a missing entry, which a
    recorded `None` would block."""
    cell = _program("q_nat", JOINS["if_sibling_first"].format(
        sib="@Q<Int, Nat>.0", open_=_MKQ))
    arts = pipeline.check(cell).artifacts
    assert arts.node_target_types and arts.expr_target_types
    assert None not in arts.node_target_types.values()
    assert None not in arts.expr_target_types.values()


class _RefusedWithNoSibling(Exception):
    """The control is refused (E213) with no sibling at all."""


_PARTLY_OPEN = ("{ let @Nat = 1; pick(Tuple(@Nat.0, None), "
                "Tuple(idg(0 - 3), None)) }")


@pytest.mark.xfail(
    raises=_RefusedWithNoSibling, strict=True,
    reason="`MkQ(Some(1), { ... pick(Tuple(@Nat.0, None), "
           "Tuple(idg(0 - 3), None)) }, Tuple(1, None))` is refused E213 "
           "with no sibling, a refusal outside #1866; until it is lifted no "
           "accepted program observes the origin `_check_fn_call_with_info` "
           "hands a constructor argument against a partly open parameter")
def test_repro_a_partly_open_parameter_in_a_field_is_judged_as_outside() -> None:
    """A generic call whose parameter a `None` leaves partly open
    (`Tuple<Nat, Option<T>>`, #1010), as a field's value beside a sibling:
    its constructor argument is synthesized again against the parameter, a
    type of the context's, so the cell is judged as its control, the same
    construction with no sibling."""
    control = _program("q_tuple_open",
                       f"MkQ(Some(1), {_PARTLY_OPEN}, Tuple(1, None))")
    codes = _codes(control, "check")
    if codes == ("E213",):
        raise _RefusedWithNoSibling(codes)
    assert codes == ()
    cell = _program("q_tuple_open", JOINS["if_sibling_first"].format(
        sib="@Q<Int, Tuple<Nat, Option<Bool>>>.0",
        open_=f"MkQ(None, {_PARTLY_OPEN}, Tuple(1, None))"))
    assert _instances(cell) == _instances(control)
    assert _verified(cell) == _verified(control)


def test_repro_a_join_completes_no_call_s_type_arguments() -> None:
    """`idg(None)` and `ido(None)` in a branch beside an `Option<Int>`: the
    `None`'s variable is the call's (its instantiation holds it), so the
    join completes it nowhere.  `ido(None)` is refused (E613) in both
    orders as outside a branch, and `idg(None)`'s recorded type keeps the
    open variable it has outside one."""
    for order in ("if_sibling_first", "if_open_first",
                  "match_sibling_first", "match_open_first"):
        join = JOINS[order].format(sib="@Option<Int>.0", open_="ido(None)")
        assert _codes(_program("option", join), "check") == ("E613",), order
        cell = _program("option", JOINS[order].format(
            sib="@Option<Int>.0", open_="idg(None)"))
        checked = pipeline.check(cell)
        assert checked.ok, order
        recorded = checked.artifacts.node_semantic_types
        calls = [n for tld in checked.program.declarations
                 if isinstance(tld.decl, vast.FnDecl)
                 for n in fold.walk(tld.decl.body)
                 if isinstance(n, vast.FnCall) and n.name == "idg"]
        assert calls and all(
            contains_typevar(recorded[n.node_id]) for n in calls), order
    assert _codes(_program("option", "ido(None)"), "check") == ("E613",)


def test_repro_an_arm_left_open_runs_as_outside_a_branch() -> None:
    """An arm whose recorded type keeps a constructor's variable after the
    join (`idg(None)`, the call's own) is built and run as outside a
    branch: the typed program instantiates `idg` at the phantom
    `Option<Bool>`, and the value is the `None` either way."""
    source = _PRELUDE + (
        "public fn h(@Bool -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  match (if @Bool.0 then { idg(None) } "
        "else { Some(4) }) {\n    Some(@Int) -> @Int.0,\n"
        "    None -> 7\n  }\n}\n")
    for arg, value in (("true", 7), ("false", 4)):
        ran = pipeline.run(source, fn="h", raw_args=[arg])
        assert ran.value == value, (arg, ran.value)
