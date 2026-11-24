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
from collections.abc import Callable
from pathlib import Path
from typing import NamedTuple

import pytest

from tests import pipeline
from vera import ast as vast
from vera import fold
from vera import types as types_mod
from vera.checker import control as control_mod
from vera.checker.control import _variable_names
from vera.types import (
    AdtType,
    Type,
    TypeVar,
    contains_typevar,
    fresh_typevar_origin,
    pretty_type,
    read_open_as_unknown,
)

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


def _names(node: pyast.AST) -> set[str]:
    return {n.id for n in pyast.walk(node) if isinstance(n, pyast.Name)}


def _derived(fn: pyast.FunctionDef, seed: set[str],
             source: Callable[[pyast.AST], bool] = lambda _: False,
             ) -> set[str]:
    """The names in *fn* derived from *seed*, or from a value *source*
    accepts: a name assigned (or bound by a `for` or `:=`) a value that
    names a derived name, taken to a fixed point."""
    derived = set(seed)
    changed = True
    while changed:
        changed = False
        for node in pyast.walk(fn):
            targets: list[pyast.AST] = []
            value: pyast.AST | None = None
            if isinstance(node, pyast.Assign):
                targets, value = node.targets, node.value
            elif isinstance(node, (pyast.AnnAssign, pyast.AugAssign,
                                   pyast.NamedExpr)):
                targets, value = [node.target], node.value
            elif isinstance(node, pyast.For):
                targets, value = [node.target], node.iter
            if value is None or not (_names(value) & derived
                                     or source(value)):
                continue
            for target in targets:
                new = _names(target) - derived
                if new:
                    derived |= new
                    changed = True
    return derived


def _params(fn: pyast.FunctionDef) -> list[str]:
    return [a.arg for a in (*fn.args.posonlyargs, *fn.args.args,
                            *fn.args.kwonlyargs)]


#: A function's name, and the parameters it hands down as an expected type.
_Handing = dict[str, set[str]]


def _hands_down(call: pyast.Call, handing: _Handing,
                defs: dict[str, pyast.FunctionDef],
                derived: set[str]) -> bool:
    """Whether *call* hands a *derived* name down as an expected type: at
    `expected=`, or as an argument for a parameter its callee hands down
    (`self._f(a)` binds `a` to `_f`'s parameter after `self`)."""
    if any(kw.arg == "expected" and _names(kw.value) & derived
           for kw in call.keywords):
        return True
    func = call.func
    name = (func.attr if isinstance(func, pyast.Attribute)
            else func.id if isinstance(func, pyast.Name) else None)
    if name not in handing:
        return False
    params = _params(defs[name])
    skip = 1 if isinstance(func, pyast.Attribute) else 0
    passed = [(params[i + skip], arg) for i, arg in enumerate(call.args)
              if i + skip < len(params)]
    passed += [(kw.arg, kw.value) for kw in call.keywords if kw.arg]
    return any(p in handing[name] and _names(arg) & derived
               for p, arg in passed)


def _handing(defs: dict[str, pyast.FunctionDef]) -> _Handing:
    """Each function of *defs* that hands one of its parameters down as an
    expected type, directly at `expected=` or through another such
    function, with those parameters; to a fixed point.  A parameter named
    `expected` is one like any other: a join may pass it its own
    `expected`, which no arm gave, and never an arm's type."""
    handing: _Handing = {}
    changed = True
    while changed:
        changed = False
        for name, fn in defs.items():
            for p in _params(fn):
                if p == "self" or p in handing.get(name, ()):
                    continue
                derived = _derived(fn, {p})
                if any(isinstance(c, pyast.Call)
                       and _hands_down(c, handing, defs, derived)
                       for c in pyast.walk(fn)):
                    handing.setdefault(name, set()).add(p)
                    changed = True
    return handing


def _refused_expectations(fn: pyast.FunctionDef,
                          defs: dict[str, pyast.FunctionDef]) -> list[str]:
    """Each hand-down in *fn* a join may not write: a value derived from an
    arm's synthesized type, at `expected=` or as an argument for a
    parameter its callee hands down as an expected type (*defs*'
    functions, read by `_handing`).  A name is derived when it is assigned
    the result of `_synth_expr` on anything but a condition or a
    scrutinee, or any expression naming a derived name.  Allowed: the
    function's own `expected` parameter, a type no arm gave (a condition's
    `Bool`), and a scrutinee's own type."""

    def from_arm(value: pyast.AST) -> bool:
        return any(
            isinstance(call, pyast.Call)
            and isinstance(call.func, pyast.Attribute)
            and call.func.attr == "_synth_expr" and call.args
            and not (isinstance(call.args[0], pyast.Attribute)
                     and call.args[0].attr in _NOT_ARMS)
            for call in pyast.walk(value))

    derived = _derived(fn, set(), from_arm)
    handing = _handing(defs)
    return [pyast.unparse(call) for call in pyast.walk(fn)
            if isinstance(call, pyast.Call)
            and _hands_down(call, handing, defs, derived)]


def _checker_functions() -> tuple[dict[str, pyast.FunctionDef],
                                  dict[str, pyast.FunctionDef]]:
    """Every function of `vera/checker/` by name, and the joins among them
    (a function that calls `_join*` or `_value_join`) by file and name."""
    defs: dict[str, pyast.FunctionDef] = {}
    joins: dict[str, pyast.FunctionDef] = {}
    for path in sorted((ROOT / "vera" / "checker").glob("*.py")):
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        for fn in pyast.walk(tree):
            if not isinstance(fn, pyast.FunctionDef):
                continue
            defs.setdefault(fn.name, fn)
            if (fn.name not in _JOINS
                    and any(isinstance(c, pyast.Call)
                            and isinstance(c.func, pyast.Attribute)
                            and c.func.attr in _JOINS
                            for c in pyast.walk(fn))):
                joins[f"{path.name}:{fn.name}"] = fn
    return defs, joins


#: The helpers the shapes below call.  `_synth_against` and
#: `_check_in_literal_context` are as `origin/main` wrote them before #1866:
#: a branch synthesized again against its sibling's type, and a value
#: checked in a literal context.  `_against_again` hands its parameter on
#: through `_synth_against`, which it precedes, so the rule must take its
#: helpers to a fixed point to find it; `_synth_as` hands a parameter named
#: `expected` down; `_complete_arms` hands nothing down.
_HELPERS = '''
def _against_again(self, expr, other):
    return self._synth_against(expr, other)

def _synth_against(self, expr, sibling):
    self._sibling_types.append(sibling)
    try:
        return self._synth_expr(expr, expected=sibling)
    finally:
        self._sibling_types.pop()

def _check_in_literal_context(self, expr, ty, context, *, component=False):
    if ty is None or component:
        return ty
    return self._synth_expr(expr, expected=context)

def _complete_arms(self, arms, joined):
    for arm, ty in arms:
        bound = {}
        self._unify_for_inference(ty, joined, bound)

def _synth_as(self, expr, expected):
    return self._synth_expr(expr, expected=expected)
'''

#: The rule, by shape: each row a join's body and whether what it hands
#: down is allowed.  The rule is read off these rows.  The first three
#: refused rows are `origin/main`'s re-synthesis at its three sites
#: (`_check_if`'s two branches, `_check_match`'s arms), which an earlier
#: form of this rule, reading `expected=` in the join's own body alone,
#: passed.
_SHAPES: dict[str, tuple[str, bool]] = {
    "the join's own expected": (
        "t = self._synth_expr(expr.then_branch, expected=expected)", True),
    "a condition's Bool": (
        "c = self._synth_expr(expr.condition, expected=BOOL)", True),
    "a scrutinee's own type": (
        "s = self._synth_expr(expr.scrutinee)\n"
        "b = self._check_pattern(arm.pattern, expected=s)", True),
    "the join's own expected, as a literal context": (
        "t = self._synth_expr(expr.then_branch)\n"
        "self._check_in_literal_context(expr.then_branch, t, expected)", True),
    "an arm's type to a helper that hands it to nothing": (
        "t = self._synth_expr(expr.then_branch)\n"
        "e = self._synth_expr(expr.else_branch)\n"
        "self._complete_arms([(expr.then_branch, t)], e)", True),
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
    "main's then-branch against its sibling": (
        "then_ty = self._synth_expr(expr.then_branch, expected=expected)\n"
        "else_ty = self._synth_expr(expr.else_branch, expected=expected)\n"
        "if contains_typevar(then_ty) and not contains_typevar(else_ty):\n"
        "    then_ty = self._synth_against(\n"
        "        expr.then_branch, else_ty) or then_ty", False),
    "main's else-branch against its sibling": (
        "then_ty = self._synth_expr(expr.then_branch, expected=expected)\n"
        "else_ty = self._synth_expr(expr.else_branch, expected=expected)\n"
        "if contains_typevar(else_ty) and not contains_typevar(then_ty):\n"
        "    else_ty = self._synth_against(\n"
        "        expr.else_branch, then_ty) or else_ty", False),
    "main's match arm against the arms before it": (
        "result_type = None\n"
        "for arm in expr.arms:\n"
        "    arm_ty = self._synth_expr(arm.body, expected=expected)\n"
        "    if result_type is None:\n"
        "        result_type = arm_ty\n"
        "    elif contains_typevar(arm_ty):\n"
        "        arm_ty = self._synth_against(arm.body, result_type)", False),
    "a sibling's type as a literal context": (
        "t = self._synth_expr(expr.then_branch)\n"
        "e = self._synth_expr(expr.else_branch)\n"
        "self._check_in_literal_context(expr.else_branch, e, t)", False),
    "a sibling's type as a literal context, by keyword": (
        "t = self._synth_expr(expr.then_branch)\n"
        "e = self._synth_expr(expr.else_branch)\n"
        "self._check_in_literal_context(expr.else_branch, e, context=t)",
        False),
    "a sibling's type through two helpers": (
        "t = self._synth_expr(expr.then_branch)\n"
        "self._against_again(expr.else_branch, t)", False),
    "a sibling's type to a helper's parameter named expected": (
        "t = self._synth_expr(expr.then_branch)\n"
        "self._synth_as(expr.else_branch, t)", False),
    "the join's own expected to a helper's parameter named expected": (
        "self._synth_as(expr.else_branch, expected)", True),
    "an arm's type through a loop's target": (
        "arm_types = [self._synth_expr(arm.body) for arm in expr.arms]\n"
        "for ty in arm_types:\n"
        "    self._synth_expr(expr.arms[0].body, expected=ty)", False),
    "an arm's type named before it is assigned": (
        "for arm in expr.arms:\n"
        "    if prev is not None:\n"
        "        self._synth_expr(arm.body, expected=prev)\n"
        "    prev = last\n"
        "    last = self._synth_expr(arm.body)", False),
}


@pytest.mark.parametrize("shape", list(_SHAPES))
def test_the_rule_reads_each_shape(shape: str) -> None:
    body, allowed = _SHAPES[shape]
    module = pyast.parse(
        _HELPERS + "\ndef j(self, expr, expected):\n"
        + "\n".join("    " + ln for ln in body.splitlines()) + "\n")
    defs = {fn.name: fn for fn in module.body
            if isinstance(fn, pyast.FunctionDef)}
    assert (_refused_expectations(defs["j"], defs) == []) is allowed


def test_no_join_hands_an_arm_s_type_down() -> None:
    """No function that joins values hands a sub-expression an expected
    type derived from an arm's type: a sibling's type, the joined type or
    a part of either (spec §5.9, #1866), at `expected=` or through a
    function that hands the argument down as one.  An arm is synthesized
    once, against the type the join's context expects; a new join, or a
    new hand-down from an arm's type, fails here."""
    defs, joins = _checker_functions()
    assert {"control.py:_check_if", "control.py:_check_match"} <= set(joins)
    refused = {name: bad for name, fn in joins.items()
               if (bad := _refused_expectations(fn, defs))}
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


# ---------------------------------------------------------------------
# What the completion writes, and where
# ---------------------------------------------------------------------

_ORDERS = ("if_sibling_first", "if_open_first", "match_sibling_first",
           "match_open_first")


def _source(params: str, body: str) -> str:
    return (_PRELUDE + f"public fn g(@Bool, {params} -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            f"  {body};\n  0\n}}\n")


def _nodes(checked: pipeline.Checked, kind: type, name: str) -> list[vast.Expr]:
    return [n for tld in checked.program.declarations
            if isinstance(tld.decl, vast.FnDecl) and tld.decl.name == "g"
            for n in fold.walk(tld.decl.body)
            if isinstance(n, kind) and getattr(n, "name", None) == name]


def _variables(ty: Type) -> set[str]:
    return _variable_names(ty)


def test_repro_a_join_completes_no_nested_call_s_type_arguments() -> None:
    """`Some(idg(None))` beside an `Option<Option<Int>>`: the `None`'s
    variable is held by `idg`'s instantiation, though the call is not the
    arm's root, so the join completes it nowhere: `idg`'s node and its
    argument keep the open variable they have outside a branch."""
    outside = pipeline.check(_source("@Option<Option<Int>>",
                                     "Some(idg(None))"))
    assert outside.ok
    for order in _ORDERS:
        checked = pipeline.check(_source("@Option<Option<Int>>", JOINS[
            order].format(sib="@Option<Option<Int>>.0",
                          open_="Some(idg(None))")))
        assert checked.ok, order
        recorded = checked.artifacts.node_semantic_types
        nodes = (_nodes(checked, vast.FnCall, "idg")
                 + _nodes(checked, vast.NullaryConstructor, "None"))
        assert len(nodes) == 2 and all(
            contains_typevar(recorded[n.node_id]) for n in nodes), order


def test_repro_a_builtin_s_variable_is_recorded_as_outside_a_branch() -> None:
    """`map_new()` beside a `Map<String, Int>`: the built-in's variables
    are no constructor's (`_constructor_minted`), and no recorded
    instantiation holds them, so the join completes neither: the call is
    recorded `Map<K, V>` in a branch as outside one."""
    def recorded(body: str) -> str:
        checked = pipeline.check(_source("@Map<String, Int>", body))
        assert checked.ok, body
        (call,) = _nodes(checked, vast.FnCall, "map_new")
        return pretty_type(checked.artifacts.node_semantic_types[
            call.node_id])

    assert recorded("map_size(map_new())") == "Map<K, V>"
    for order in _ORDERS:
        assert recorded("map_size(" + JOINS[order].format(
            sib="@Map<String, Int>.0", open_="map_new()") + ")") == (
                "Map<K, V>"), order


def test_repro_a_completed_arm_is_recorded_alike_in_every_table() -> None:
    """`None` beside an `Option<Int>`: the completed type is written in
    each table that records one, the node table code generation reads,
    the span table the language server and the artifacts read, and its
    text.  Behind a statement too, which the walk passes over (a `let` is
    no expression)."""
    for order, open_ in [(o, a) for o in _ORDERS
                         for a in ("None", "{ let @Int = 1; None }")]:
        checked = pipeline.check(_source("@Option<Int>", "match " + JOINS[
            order].format(sib="@Option<Int>.0", open_=open_)
            + " { Some(@Int) -> @Int.0, None -> 7 }"))
        assert checked.ok, (order, open_)
        a = checked.artifacts
        (none,) = _nodes(checked, vast.NullaryConstructor, "None")
        key = vast.span_key(none)
        assert (pretty_type(a.node_semantic_types[none.node_id]),
                pretty_type(a.expr_semantic_types[key]),
                a.expr_types[key]) == ("Option<Int>",) * 3, (order, open_)


def test_repro_a_join_writes_no_variable_into_an_arm() -> None:
    """`None` beside `Some(idg(None))`: the joined type's payload is the
    call's open variable, which the join does not write into the bare
    `None`'s record (a binding that holds a variable completes nothing),
    so the two records share no variable."""
    for order in _ORDERS:
        checked = pipeline.check(_source("@Bool", JOINS[order].format(
            sib="Some(idg(None))", open_="None")))
        assert checked.ok, order
        recorded = checked.artifacts.node_semantic_types
        (call,) = _nodes(checked, vast.FnCall, "idg")
        bare = [n for n in _nodes(checked, vast.NullaryConstructor, "None")
                if not any(n is m for m in fold.walk(call))]
        assert len(bare) == 1, order
        assert not (_variables(recorded[bare[0].node_id])
                    & _variables(recorded[call.node_id])), order


def test_fresh_typevar_origin_names_a_minted_variable_alone() -> None:
    """The one reader of a minted variable's name: `T$2`, which
    `_fresh_typevar` mints for `T`, has the origin `T`; a declared variable
    (`T`, a generic's own, rigid in its body) and any other type have none.
    The #1684 cells read their open variables through it, so a reader that
    took a declared variable for a minted one would make them lax."""
    assert fresh_typevar_origin(TypeVar("T$2")) == "T"
    assert fresh_typevar_origin(TypeVar("Key$13")) == "Key"
    assert fresh_typevar_origin(TypeVar("T")) is None
    assert fresh_typevar_origin(AdtType("Option", (TypeVar("T$2"),))) is None


#: Each reader of a minted variable's name outside `vera/types.py`'s own,
#: with an input on which its answer turns on that reading: a declared
#: `T` the function holds rigid, which is no minted variable.
_MINTED_READERS = {
    "control._holds_variable": (
        lambda: control_mod._holds_variable(TypeVar("T"), {"T"}), True),
    "control._holds_open": (
        lambda: control_mod._holds_open(TypeVar("T"), {"T"}), False),
    "control._rigid_named": (
        lambda: control_mod._rigid_named(
            AdtType("Option", (TypeVar("T"),)), {"T"}), ["T"]),
    "types.read_open_as_unknown": (
        lambda: read_open_as_unknown(TypeVar("T"), {"T"}, lambda _: ()),
        TypeVar("T")),
}


@pytest.mark.parametrize("site", list(_MINTED_READERS))
def test_a_minted_variable_is_read_by_its_one_reader(
        site: str, monkeypatch: pytest.MonkeyPatch) -> None:
    """Each site that tells a variable a call minted from the enclosing
    function's own reads it through `fresh_typevar_origin`, the one reader
    of the form `_fresh_typevar` writes: given the reader's answer, a
    declared `T` is the function's own; with a reader that calls every
    name minted, the site's answer turns."""
    call, held = _MINTED_READERS[site]
    assert call() == held, site
    module = control_mod if site.startswith("control.") else types_mod
    monkeypatch.setattr(module, "fresh_typevar_origin", lambda _ty: "T")
    assert call() != held, site
    assert control_mod._holds_variable(TypeVar("T$3"), {"T"}) is False
    assert control_mod._holds_open(TypeVar("T$3"), {"T"}) is True
