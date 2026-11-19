"""A row the obligation table holds guardable for which the compiled module
holds no check (#1861): `vera verify` refuses a correct program with E541.

The class: every row whose guard is a check of its own while code
generation emits none for it.  Two mechanisms produce its members.

* The table (`vera/obligations/table.py`).  An argument applied to a
  function value is held at the entry of the closure that runs, whatever
  the function operand is; the table answered it there only for a slot
  operand, so an `if`, a `match`, a call's result or an index left the
  argument's row, and its refinement predicate's operations, with checks
  nothing emits.  And a refined head is checked once, at the position the
  value reaches (a `let`, a return, an argument, a store): the table listed
  the head of a value built in place (an array literal, `set_add`,
  `map_insert`, `set_new()`) at the construction itself when it is a leaf
  of a join or a return, and at a closure argument, and it held the join of
  a non-scalar store guardable where the store guards only scalars.
* Code generation (`vera/wasm/calls_containers.py`).  `set_add`'s element
  and `map_insert`'s key took the sign guard and no refinement guard,
  where an array literal's element and `map_insert`'s value take both.

The instrument is the census: `apply_fn`'s function operand (a slot, a
call's result, an `if`, a `match`, an index, a built-in's result, a closure
literal, a let-bound join) by the parameter's type (a refinement whose
predicate has an obligated operation, a plain refinement, `Nat`, a refined
array, a refined tuple component, a refined element, an argument that is
itself a join) by the argument (proved, or opaque to the solver); and a
value built in place (by the component type: a refined head, a refined
element or key, a `Nat` element, nested, plain, a call's result beside it)
by its position.  Every cell joins clean, and a cell whose value can
violate its row traps at a violating input and runs at a satisfying one.
"""

from __future__ import annotations

import itertools

import pytest

from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs
# a sample of its parametrised cells, and all of them when it changes this
# file or a module that decides its class: the table's rows, and the
# container lowerings' store guards.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/obligations/table.py",
        "vera/wasm/calls_containers.py",
    ],
)

HEADER = (
    "type Small = { @Int | @Int.0 * @Int.0 * @Int.0 < 1000 };\n"
    "type Pos = { @Int | @Int.0 > 0 };\n"
    "type NE = { @Array<Int> | array_length(@Array<Int>.0) > 0 };\n"
    "type RS = { @Set<Int> | set_size(@Set<Int>.0) > 0 };\n"
    "type RM = { @Map<Int, Int> | map_size(@Map<Int, Int>.0) > 0 };\n"
    "type NEP = { @Array<Pos> | array_length(@Array<Pos>.0) > 0 };\n"
    "type NEPI = { @Array<{ @Int | @Int.0 > 0 }> | "
    "array_length(@Array<{ @Int | @Int.0 > 0 }>.0) > 0 };\n"
    # A predicate the solver neither proves nor refutes of an opaque value,
    # so a component held to it is checked at run time.
    "type Short = { @Int | string_length(to_string(@Int.0)) < 3 };\n"
    # Refinements whose resolved base names no type (a function type,
    # behind an alias or as a type argument), and one a generic alias
    # writes over its parameter.
    "type IntFn = fn(Int -> Int) effects(pure);\n"
    "type LiveFn = { @IntFn | true };\n"
    "type NEF = { @Array<IntFn> | array_length(@Array<IntFn>.0) > 0 };\n"
    "type NonEmptyOf<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };\n"
    # Bases written through an alias: of a primitive, of a data type, and a
    # generic alias whose refinement does not read its parameter.
    "type Count = Int;\n"
    "type PosCount = { @Count | @Count.0 > 0 };\n"
    "type IntList = Array<Int>;\n"
    "type NEL = { @IntList | array_length(@IntList.0) > 0 };\n"
    "type Bounded<T> = { @Int | @Int.0 > 0 };\n"
)
CONTRACT = ("  requires(@Int.0 >= 0 && @Int.0 < 5)\n  ensures(true)\n"
            "  effects(pure)\n")
PLAIN = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

#: Producers of an opaque value of each shape: an argument that is no
#: construction, so its components' rows stand at the argument itself.
PRODUCERS = (
    "private fn pair(@Int -> @Tuple<Int, Int>)\n" + PLAIN
    + "{\n  Tuple(@Int.0, 0)\n}\n\n"
    + "private fn optof(@Int -> @Option<Int>)\n" + PLAIN
    + "{\n  Some(@Int.0)\n}\n\n"
    + "private fn arrof(@Int -> @Array<Int>)\n" + PLAIN
    + "{\n  [@Int.0]\n}\n\n"
    + "private fn fns(@Int -> @Array<IntFn>)\n" + PLAIN
    + "{\n  array_slice([fn(@Int -> @Int) effects(pure) { 1 }], 0, @Int.0)\n}\n\n"
)

#: The `@Float64` argument each cell runs with: a value no row refuses.
SATISFYING = 3.0


def _mismatches(source: str) -> list[str]:
    """The join's mismatches for *source*, as `kind:obligation@line:col`."""
    verified = pipeline.verify(source, reconcile=True)
    assert verified.ran, verified.checked.errors
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None, (
        reconciled.diagnostics if reconciled is not None else None)
    return [f"{m.kind}:{m.obligation}@{m.line}:{m.column}"
            for m in reconciled.reconciliation.mismatches]


def _verified_clean(source: str) -> pipeline.Verified:
    verified = pipeline.verify(source, reconcile=True)
    assert verified.ran, verified.checked.errors
    codes = sorted({d.error_code for d in verified.errors})
    assert verified.ok, codes
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None
    assert reconciled.reconciliation.mismatches == []
    return verified


def _statuses(verified: pipeline.Verified, kind: str, line: int) -> list[str]:
    return sorted(o.status for o in verified.obligations
                  if o.kind == kind and o.line == line)


# =====================================================================
# The census: apply_fn's operand x the parameter's type x the argument
# =====================================================================

#: name -> (parameter type, closure body, proved argument, opaque argument,
#: the `@Float64` the opaque argument violates its row at, or None)
PARAMS: dict[str, tuple[str, str, str, str, float | None]] = {
    "small": ("Small", "@Small.0", "@Int.0", "float_to_int(@Float64.0)",
              3000000.0),
    "pos": ("Pos", "@Pos.0", "@Int.0 + 1", "float_to_int(@Float64.0)", -5.0),
    "nat": ("Nat", "0", "@Int.0", "float_to_int(@Float64.0)", -5.0),
    "ne": ("NE", "array_length(@NE.0)", "[@Int.0, 1]", "[@Int.0]", None),
    "tuple_pos": ("Tuple<Pos, Int>", "0", "Tuple(@Int.0 + 1, 0)",
                  "Tuple(float_to_int(@Float64.0), 0)", -5.0),
    "tuple_nat": ("Tuple<Nat, Int>", "0", "Tuple(@Int.0, 0)",
                  "Tuple(float_to_int(@Float64.0), 0)", -5.0),
    "arr_pos": ("Array<Pos>", "array_length(@Array<Pos>.0)", "[@Int.0 + 1]",
                "[float_to_int(@Float64.0)]", -5.0),
    "arr_small": ("Array<Small>", "array_length(@Array<Small>.0)", "[@Int.0]",
                  "[float_to_int(@Float64.0)]", 3000000.0),
    "ne_join": ("NE", "array_length(@NE.0)",
                "if @Bool.0 then { [@Int.0] } else { [1] }",
                "if @Bool.0 then { array_append([], @Int.0) } else { [1] }",
                None),
    "pos_join": ("Pos", "@Pos.0", "if @Bool.0 then { @Int.0 + 1 } else { 1 }",
                 "if @Bool.0 then { float_to_int(@Float64.0) } else { 1 }",
                 -5.0),
    # A refined head over a base whose type argument is itself refined,
    # by an alias and written inline: the guard at the call names its
    # binder with the argument rendered as the checker renders it.
    "nep": ("NEP", "array_length(@NEP.0)", "[@Int.0 + 1, 1]",
            "[float_to_int(@Float64.0)]", -5.0),
    "nep_inline": ("NEPI", "array_length(@NEPI.0)", "[@Int.0 + 1, 1]",
                   "[float_to_int(@Float64.0)]", -5.0),
    # The row paths an argument's value carries below its head: a tuple
    # component, one nested a level down, an `Option` payload and an
    # array element, each of a value that is no construction, so the row
    # stands at the argument (#1861 review).
    "tuple_short": ("Tuple<Short, Int>", "0", "Tuple(@Int.0, 0)",
                    "pair(float_to_int(@Float64.0))", 5000.0),
    "tuple_nested": ("Tuple<Tuple<Short, Int>, Int>", "0",
                     "Tuple(Tuple(@Int.0, 0), 0)",
                     "Tuple(pair(float_to_int(@Float64.0)), 0)", 5000.0),
    "opt_short": ("Option<Short>", "0", "Some(@Int.0)",
                  "optof(float_to_int(@Float64.0))", 5000.0),
    "arr_short": ("Array<Short>", "array_length(@Array<Short>.0)", "[@Int.0]",
                  "arrof(float_to_int(@Float64.0))", 5000.0),
    # A refinement whose resolved base names no type: a function type
    # behind an alias, an array of function values, and one a generic
    # alias writes over its parameter (#1861 review).
    "fn_alias": ("LiveFn", "0", "fn(@Int -> @Int) effects(pure) { 1 }",
                 "fn(@Int -> @Int) effects(pure) { 2 }", None),
    "arr_fn": ("NEF", "array_length(@NEF.0)",
               "[fn(@Int -> @Int) effects(pure) { 1 }]",
               "fns(float_to_int(@Float64.0))", 0.0),
    "arr_fn_generic": ("NonEmptyOf<IntFn>", "array_length(@NonEmptyOf<IntFn>.0)",
                       "[fn(@Int -> @Int) effects(pure) { 1 }]",
                       "fns(float_to_int(@Float64.0))", 0.0),
    # How the refinement's base is written: the check binds the refinement
    # as the program writes it, whose base names the binder its predicate
    # reads (#1861 review).  A primitive written directly is `pos`.
    "alias_prim": ("PosCount", "0", "@Int.0 + 1", "float_to_int(@Float64.0)",
                   -5.0),
    "alias_data": ("NEL", "0", "[@Int.0]",
                   "array_slice([1], 0, float_to_int(@Float64.0))", 0.0),
    "generic_reads": ("NonEmptyOf<Int>", "0", "[@Int.0]",
                      "array_slice([1], 0, float_to_int(@Float64.0))", 0.0),
    "generic_unread": ("Bounded<Bool>", "0", "@Int.0 + 1",
                       "float_to_int(@Float64.0)", -5.0),
}

#: The parameters whose opaque argument's row no check at the call can
#: evaluate, so `vera verify` discloses it (`tier3_unguarded`) and a
#: violating value runs, bar a closure literal's own entry: the reason
#: each is not guarded.
DISCLOSED: dict[str, str] = {
    "tuple_nested": "a construction store checks a component's head, not "
                    "the tuple component below it",
    "opt_short": "a constructor payload is decomposed by no check",
    "arr_short": "an element below an argument is decomposed by no check",
    "arr_fn_generic": "the check at the call has no written type to bind: "
                      "the base names a generic alias's parameter",
    "generic_reads": "the check at the call has no written type to bind: "
                     "the base names a generic alias's parameter",
}

#: The disclosed parameters whose row a closure literal applied in place
#: answers at its own entry, which checks its parameter.
ANSWERED_AT_ENTRY = frozenset({"arr_short", "arr_fn_generic", "generic_reads"})

OPERANDS: dict[str, str] = {
    "slot": "@F.0",
    "call": "choose(@Bool.0, @F.0, @F.1)",
    "if": "if @Bool.0 then { @F.0 } else { @F.1 }",
    "match": "match @Bool.0 { true -> @F.0, false -> @F.1 }",
    "index": "[@F.0, @F.1][0]",
    "builtin": "option_unwrap_or(Some(@F.0), @F.1)",
    "lambda": "",
    "let_if": "",
}


def apply_program(param: str, operand: str, arg: str) -> str:
    pty, body, proved, opaque, _ = PARAMS[param]
    value = proved if arg == "proved" else opaque
    lam = f"fn(@{pty} -> @Int) effects(pure) {{ {body} }}"
    pre = ""
    if operand == "lambda":
        fn_value = lam
    elif operand == "let_if":
        pre = "  let @F = if @Bool.0 then { @F.0 } else { @F.1 };\n"
        fn_value = "@F.0"
    else:
        fn_value = OPERANDS[operand]
    return (
        HEADER
        + f"type F = fn({pty} -> Int) effects(pure);\n\n"
        + PRODUCERS
        + "private fn choose(@Bool, @F, @F -> @F)\n" + PLAIN
        + "{\n  if @Bool.0 then { @F.1 } else { @F.0 }\n}\n\n"
        + "private fn pick(@Bool, @F, @F, @Int, @Float64 -> @Int)\n" + CONTRACT
        + "{\n" + pre + f"  apply_fn({fn_value}, {value})\n}}\n\n"
        + "public fn f(@Bool, @Int, @Float64 -> @Int)\n" + CONTRACT
        + "{\n"
        + f"  let @F = {lam};\n"
        + "  pick(@Bool.0, @F.0, @F.0, @Int.0, @Float64.0)\n}\n"
    )


APPLY_CELLS = list(itertools.product(PARAMS, OPERANDS, ("proved", "opaque")))


@pytest.mark.parametrize(
    ("param", "operand", "arg"), APPLY_CELLS,
    ids=["-".join(c) for c in APPLY_CELLS])
def test_apply_fn_argument_joins_clean(param: str, operand: str, arg: str) -> None:
    source = apply_program(param, operand, arg)
    verified = _verified_clean(source)
    assert pipeline.run(source, fn="f", args=[1, 2, SATISFYING]).ok
    bad = PARAMS[param][4]
    if arg != "opaque":
        return
    disclosed = [o for o in verified.obligations
                 if o.kind == "refine_bind" and o.status == "tier3_unguarded"
                 and o.fn_name == "pick"]
    if param in DISCLOSED and not (operand == "lambda"
                                   and param in ANSWERED_AT_ENTRY):
        assert disclosed, verified.obligations
    else:
        assert disclosed == [], disclosed
        if bad is not None:
            ran = pipeline.run(source, fn="f", args=[1, 2, bad])
            assert ran.trap is not None, ran.value


# =====================================================================
# The census: a value built in place x its position x the component type
# =====================================================================

#: name -> (type, built expression, the `@Float64` it violates its row at)
BUILT: dict[str, tuple[str, str, float | None]] = {
    "arr_head": ("NE", "[@Int.0]", None),
    "set_head": ("RS", "set_add(set_new(), @Int.0)", None),
    "map_head": ("RM", "map_insert(map_new(), @Int.0, 1)", None),
    "arr_elem": ("Array<Pos>", "[float_to_int(@Float64.0)]", -5.0),
    "set_elem": ("Set<Pos>", "set_add(set_new(), float_to_int(@Float64.0))",
                 -5.0),
    "map_elem": ("Map<Int, Pos>",
                 "map_insert(map_new(), 1, float_to_int(@Float64.0))", -5.0),
    "map_key": ("Map<Pos, Int>",
                "map_insert(map_new(), float_to_int(@Float64.0), 1)", -5.0),
    "arr_nat": ("Array<Nat>", "[float_to_int(@Float64.0)]", -5.0),
    "set_nat": ("Set<Nat>", "set_add(set_new(), float_to_int(@Float64.0))",
                -5.0),
    "map_nat": ("Map<Int, Nat>",
                "map_insert(map_new(), 1, float_to_int(@Float64.0))", -5.0),
    "arr_nested": ("Array<NE>", "[[@Int.0]]", None),
    "arr_plain": ("Array<Int>", "[@Int.0]", None),
    "arr_head_call": ("NE", "array_append([], @Int.0)", None),
    "pos_call": ("Pos", "float_to_int(@Float64.0)", -5.0),
    # A tuple component below a stored value, which no store checks.
    "tuple_nested": ("Tuple<Tuple<Short, Int>, Int>",
                     "Tuple(pair(float_to_int(@Float64.0)), 0)", 5000.0),
    "arr_tuple": ("Array<Tuple<Short, Int>>",
                  "[pair(float_to_int(@Float64.0))]", 5000.0),
}

POSITIONS: dict[str, str] = {
    "ret": "  E\n",
    "ret_block": "  let @Bool = true;\n  E\n",
    "ret_if": "  if @Bool.0 then { E } else { E }\n",
    "ret_match": "  match @Bool.0 { true -> E, false -> E }\n",
    "let": "  let @S = E;\n  @S.0\n",
    "let_if": "  let @S = if @Bool.0 then { E } else { E };\n  @S.0\n",
    "let_match": "  let @S = match @Bool.0 { true -> E, false -> E };\n  @S.0\n",
    "arg": "  take(E)\n",
    "arg_if": "  take(if @Bool.0 then { E } else { E })\n",
    "ctor_field": "  let @W = MkW(E);\n  match @W.0 { MkW(@S) -> @S.0 }\n",
    "ctor_field_if": ("  let @W = MkW(if @Bool.0 then { E } else { E });\n"
                      "  match @W.0 { MkW(@S) -> @S.0 }\n"),
    "tuple_comp": "  let Tuple<@S, @Int> = Tuple(E, 0);\n  @S.0\n",
    "ret_tuple": "  Tuple(E, 0)\n",
}


def built_program(built: str, position: str) -> str:
    ty, expr, _ = BUILT[built]
    body = POSITIONS[position].replace("E", expr).replace("@S", "@" + ty)
    ret = f"Tuple<{ty}, Int>" if position == "ret_tuple" else ty
    return (
        HEADER
        + f"private data W {{ MkW({ty}) }}\n\n"
        + PRODUCERS
        + f"private fn take(@{ty} -> @{ty})\n" + PLAIN
        + f"{{\n  @{ty}.0\n}}\n\n"
        + f"private fn mk(@Bool, @Int, @Float64 -> @{ret})\n" + PLAIN
        + "{\n" + body + "}\n\n"
        + "public fn f(@Bool, @Int, @Float64 -> @Int)\n" + PLAIN
        + "{\n  let @" + ret + " = mk(@Bool.0, @Int.0, @Float64.0);\n  0\n}\n"
    )


BUILT_CELLS = list(itertools.product(BUILT, POSITIONS))

#: The cells `vera verify` discloses (a `refine_bind` record at
#: `tier3_unguarded`), by the reason no check stands for the row.
DISCLOSED_BUILT: dict[tuple[str, str], str] = {
    # A refinement over a non-scalar base stored in a constructor field.
    **{(b, p): "a construction store guards only a scalar-based refinement"
       for b, ps in (
           ("arr_head", ("ctor_field", "ctor_field_if", "tuple_comp",
                         "ret_tuple")),
           ("set_head", ("ctor_field", "ctor_field_if", "ret_tuple")),
           ("map_head", ("ctor_field", "ctor_field_if", "ret_tuple")),
           ("arr_head_call", ("ctor_field", "ctor_field_if", "ret_tuple")))
       for p in ps},
    # An element below a returned tuple component.
    **{(b, "ret_tuple"): "an element below a tuple component is decomposed "
                         "by no boundary"
       for b in ("arr_elem", "set_elem", "map_elem", "map_key")},
    # A refined element of a composite element type.
    **{(b, p): "a composite element refinement is not checked by the "
               "element loop"
       for b in ("arr_nested", "arr_tuple") for p in POSITIONS},
    # A tuple component below a stored value (#1861 review).
    **{("tuple_nested", p): "a construction store checks a component's "
                            "head, not a tuple component below it"
       for p in POSITIONS if p != "ret_tuple"},
}


@pytest.mark.parametrize(
    ("built", "position"), BUILT_CELLS,
    ids=["-".join(c) for c in BUILT_CELLS])
def test_value_built_in_place_joins_clean(built: str, position: str) -> None:
    source = built_program(built, position)
    verified = _verified_clean(source)
    assert pipeline.run(source, fn="f", args=[1, 2, SATISFYING]).ok
    disclosed = [o for o in verified.obligations
                 if o.status == "tier3_unguarded"]
    if (built, position) in DISCLOSED_BUILT:
        assert disclosed, verified.obligations
        assert {o.kind for o in disclosed} == {"refine_bind"}, disclosed
        return
    assert disclosed == [], disclosed
    bad = BUILT[built][2]
    if bad is not None:
        ran = pipeline.run(source, fn="f", args=[1, 2, bad])
        assert ran.trap is not None, ran.value


# =====================================================================
# The reported instances (red first)
# =====================================================================

_ISSUE_BODY = """\
type Small = { @Int | @Int.0 * @Int.0 * @Int.0 < 1000 };
type SmallToInt = fn(Small -> Int) effects(pure);

private fn pick(@Bool, @SmallToInt, @SmallToInt, @Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < 5)
  ensures(true)
  effects(pure)
{
  apply_fn(OPERAND, @Int.0)
}

public fn f(@Bool, @Int -> @Int)
  requires(@Int.0 >= 0 && @Int.0 < 5)
  ensures(true)
  effects(pure)
{
  let @SmallToInt = fn(@Small -> @Int) effects(pure) { @Small.0 };
  pick(@Bool.0, @SmallToInt.0, @SmallToInt.0, @Int.0)
}
"""


@pytest.mark.parametrize("operand", [
    "if @Bool.0 then { @SmallToInt.0 } else { @SmallToInt.1 }",
    "match @Bool.0 { true -> @SmallToInt.0, false -> @SmallToInt.1 }",
])
def test_repro_apply_fn_of_a_computed_value_checks_its_predicate_at_the_call(
        operand: str) -> None:
    source = _ISSUE_BODY.replace("OPERAND", operand)
    assert _mismatches(source) == []
    verified = _verified_clean(source)
    # The predicate's two products are rows of each check that evaluates
    # it: the call's in `pick` (the argument checked at the call) and the
    # closure's entry in `f`, each with its check.  Their records are
    # named for the alias whose predicate they are, `Small`.
    table = verified.result.table
    argument = [r for r in table.rows
                if r.kind == "refine_bind" and r.fn == "pick"]
    assert len(argument) == 1 and argument[0].guard.check, argument
    products = [r for r in table.rows
                if r.kind == "int_overflow" and r.fn == "pick"]
    assert [r.evaluation for r in products] == [
        ("predicate", argument[0].id)] * 2, products
    records = [o for o in verified.obligations if o.kind == "int_overflow"]
    assert [(o.fn_name, o.status) for o in records] == [("Small", "tier3")] * 2
    assert pipeline.run(source, fn="f", args=[1, 3]).value == 3


_NON_EMPTY = """\
type NonEmpty = { @Array<Int> | array_length(@Array<Int>.0) > 0 };
type Head = fn(NonEmpty -> Int) effects(pure);

private fn pick(@Bool, @Head, @Head, @Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(if @Bool.0 then { @Head.0 } else { @Head.1 }, @Array<Int>.0)
}

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Head = fn(@NonEmpty -> @Int) effects(pure) { @NonEmpty.0[0] };
  pick(@Bool.0, @Head.0, @Head.0, array_slice([@Int.0], 0, @Int.0))
}
"""


def test_repro_apply_fn_of_a_computed_value_checks_its_argument_at_the_call(
) -> None:
    """The first comment's member: an argument the solver does not prove,
    checked at the call, before the entry of the closure that runs."""
    assert _mismatches(_NON_EMPTY) == []
    verified = _verified_clean(_NON_EMPTY)
    assert _statuses(verified, "refine_bind", 9) == ["tier3"]
    assert pipeline.run(_NON_EMPTY, fn="f", args=[1, 1]).value == 1
    ran = pipeline.run(_NON_EMPTY, fn="f", args=[1, 0])
    assert ran.trap is not None
    assert "Refinement violation in closure argument\n" in str(ran.trap)


_COMPOSITE_WALK = """\
private fn pair2(@Int -> @Tuple<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(@Int.0, @Int.0)
}

private fn wrap(@Int -> @Option<Tuple<Int, Int>>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(Tuple(@Int.0, @Int.0))
}

private fn take(@Tuple<Nat, Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn go(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Nat, Nat> = pair2(@Int.0);
  let @Nat = take(pair2(@Int.0));
  match wrap(@Int.0) {
    Some(@Tuple<Nat, Nat>) -> 1,
    None -> 0
  }
}
"""


def test_the_composite_walk_lists_one_check_and_answers_the_rest() -> None:
    """The `Nat` positions of a differing tuple (`_Builder._tree_rows`):
    at a `let` and at a pattern binder, the first position is the walk's
    own check and each further one is answered by it, the binder's rows
    carrying the value they take apart; at a call argument every position
    is answered by the callee's entry.  Each row is held to `Nat`."""
    from vera.types import NAT

    verified = _verified_clean(_COMPOSITE_WALK)
    rows = [r for r in verified.result.table.rows
            if r.kind == "nat_bind" and r.fn == "go"]
    assert [r.path for r in rows] == [("Tuple.0",), ("Tuple.1",)] * 3, rows
    assert all(r.target == NAT for r in rows), rows
    let, arg, binder = rows[0:2], rows[2:4], rows[4:6]
    for first, second in (let, binder):
        assert first.answered_by is None and first.guard.check, first
        assert second.answered_by == first.id, second
    assert [r.source is None for r in let + arg] == [True] * 4
    assert all(r.source is not None for r in binder), binder
    assert all(r.answered_by is not None for r in arg), arg
    assert pipeline.run(_COMPOSITE_WALK, fn="go", args=[3]).value == 1
    assert pipeline.run(_COMPOSITE_WALK, fn="go", args=[-3]).trap is not None


_TUPLE_COMPONENT = """\
type Short = { @Int | string_length(to_string(@Int.0)) < 3 };
type F = fn(Tuple<Short, Int> -> Int) effects(pure);

private fn take(@Tuple<Int, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Tuple<Int, Int> -> @Int) effects(pure) {
    match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 }
  };
  apply_fn(@F.0, @Tuple<Int, Int>.0)
}

public fn go(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take(Tuple(float_to_int(@Float64.0), 1))
}
"""


def test_repro_a_tuple_component_of_a_closure_argument_is_checked_at_the_call(
) -> None:
    """A refined tuple component of an argument applied to a function
    value is a row of the argument, checked at the call: the closure that
    runs is wider than its type and checks nothing (#1861 review).  The
    row was listed with a check and none was emitted: E541."""
    verified = _verified_clean(_TUPLE_COMPONENT)
    assert _statuses(verified, "refine_bind", 12) == ["tier3"]
    assert pipeline.run(_TUPLE_COMPONENT, fn="go", args=[3.0]).value == 3
    ran = pipeline.run(_TUPLE_COMPONENT, fn="go", args=[5000.0])
    assert ran.trap is not None, ran.value
    assert ("Refinement violation in closure argument (tuple component)\n"
            in str(ran.trap)), ran.trap


_FUNCTION_BASE = """\
type IntFn = fn(Int -> Int) effects(pure);
REFINEMENT
type G = fn(PARAM -> Int) effects(pure);

public fn go(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntFn = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  let @G = fn(@Array<IntFn> -> @Int) effects(pure) {
    array_length(@Array<IntFn>.0)
  };
  apply_fn(@G.0, array_slice([@IntFn.0], 0, float_to_int(@Float64.0)))
}
"""


@pytest.mark.parametrize(("refinement", "param", "status"), [
    ("type NEF = { @Array<IntFn> | array_length(@Array<IntFn>.0) > 0 };",
     "NEF", "tier3"),
    ("type NonEmptyOf<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };",
     "NonEmptyOf<IntFn>", "tier3_unguarded"),
], ids=["alias", "generic_alias"])
def test_repro_a_refinement_over_function_values_at_a_closure_argument(
        refinement: str, param: str, status: str) -> None:
    """A refinement whose resolved base names no type (an array of
    function values) is checked at the call against the refinement as the
    program writes it, whose base names the binder its predicate reads; a
    generic alias's, which writes its parameter there, is disclosed.  Code
    generation raised an internal error for both (#1861 review)."""
    source = (_FUNCTION_BASE.replace("REFINEMENT", refinement)
              .replace("PARAM", param))
    verified = _verified_clean(source)
    assert _statuses(verified, "refine_bind", 14) == [status]
    assert pipeline.run(source, fn="go", args=[1.0]).value == 1
    ran = pipeline.run(source, fn="go", args=[0.0])
    if status == "tier3":
        assert ran.trap is not None, ran.value
    else:
        assert ran.value == 0


_WRITTEN_BASE = {
    "alias_prim": ("""\
type Count = Int;
type PosCount = { @Count | @Count.0 > 0 };
type F = fn(PosCount -> Int) effects(pure);
""", "fn(@Int -> @Int) effects(pure) { @Int.0 }", "float_to_int(@Float64.0)",
                   [(3.0, 3), (-5.0, None)]),
    "alias_data": ("""\
type IntList = Array<Int>;
type NEL = { @IntList | array_length(@IntList.0) > 0 };
type F = fn(NEL -> Int) effects(pure);
""", "fn(@Array<Int> -> @Int) effects(pure) { array_length(@Array<Int>.0) }",
                   "array_slice([1], 0, float_to_int(@Float64.0))",
                   [(1.0, 1), (0.0, None)]),
    "generic_reads": ("""\
type NonEmptyOf<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };
type F = fn(NonEmptyOf<Int> -> Int) effects(pure);
""", "fn(@Array<Int> -> @Int) effects(pure) { array_length(@Array<Int>.0) }",
                      "array_slice([1], 0, float_to_int(@Float64.0))",
                      [(1.0, 1), (0.0, 0)]),
}


@pytest.mark.parametrize("base", sorted(_WRITTEN_BASE))
def test_repro_a_closure_argument_binds_its_refinement_as_written(
        base: str) -> None:
    """The check at the call binds the refinement as the program writes
    it: its predicate reads its binder by the written base (`@Count.0` for
    `type Count = Int`, `@IntList.0`), which a base minted from the resolved
    type (`Int`, `Array<Int>`) does not name, and code generation stopped
    with an internal error (E699).  A generic alias's refinement over its
    own parameter (`@Array<T>.0`) has no binder the call can name: it is
    disclosed, and the violating value runs (#1861 review)."""
    header, closure, arg, runs = _WRITTEN_BASE[base]
    source = (header + "\npublic fn go(@Float64 -> @Int)\n" + PLAIN
              + f"{{\n  let @F = {closure};\n  apply_fn(@F.0, {arg})\n}}\n")
    verified = _verified_clean(source)
    statuses = sorted(o.status for o in verified.obligations
                      if o.kind == "refine_bind")
    assert statuses == (["tier3_unguarded"] if base == "generic_reads"
                        else ["tier3"]), statuses
    for value, expected in runs:
        ran = pipeline.run(source, fn="go", args=[value])
        if expected is None:
            assert ("Refinement violation in closure argument\n"
                    in str(ran.trap)), ran.trap
        else:
            assert ran.value == expected


_FUNCTION_ALIAS = """\
type F = fn(Int -> Int) effects(pure);
type G = fn({ @F | true } -> Int) effects(pure);

public fn go(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Int -> @Int) effects(pure) { @Int.0 + 1 };
  let @G = fn(@F -> @Int) effects(pure) { apply_fn(@F.0, 1) };
  apply_fn(@G.0, @F.0)
}
"""


def test_repro_a_refined_function_alias_at_a_closure_argument() -> None:
    """A refinement over a function type behind an alias is checked at
    the call over the alias its predicate names: code generation raised an
    internal error (#1861 review)."""
    verified = _verified_clean(_FUNCTION_ALIAS)
    assert _statuses(verified, "refine_bind", 11) == ["tier3"]
    assert pipeline.run(_FUNCTION_ALIAS, fn="go", args=[0.0]).value == 2


_RETURNED = HEADER + """
private fn mk(@Bool, @Int -> @NE)
  requires(true)
  ensures(true)
  effects(pure)
{
  BODY
}

public fn f(@Bool, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(mk(@Bool.0, @Int.0))
}
"""


@pytest.mark.parametrize(("body", "positions"), [
    ("[@Int.0]", 1),
    ("if @Bool.0 then { [@Int.0] } else { [0] }", 1),
    ("match @Bool.0 { true -> [@Int.0], false -> [0] }", 1),
    ("let @NE = if @Bool.0 then { [@Int.0] } else { [0] };\n  @NE.0", 2),
])
def test_repro_a_literal_built_at_a_result_is_checked_once(
        body: str, positions: int) -> None:
    source = _RETURNED.replace("BODY", body)
    assert _mismatches(source) == []
    verified = _verified_clean(source)
    # One record of the refinement per position the value reaches (the
    # return, and the `let`), each `tier3` and each with its check.
    rows = [o for o in verified.obligations if o.kind == "refine_bind"]
    assert len(rows) == positions, rows
    assert all(o.status == "tier3" for o in rows), rows
    reconciled = verified.reconciled
    assert reconciled is not None and reconciled.reconciliation is not None
    assert len(reconciled.reconciliation.pairs) == positions
    assert pipeline.run(source, fn="f", args=[1, 4]).value == 1


_SET_RETURN = """\
type RS = { @Set<Int> | set_size(@Set<Int>.0) > 0 };

private fn mk(@Int -> @RS)
  requires(true)
  ensures(true)
  effects(pure)
{
  set_add(set_new(), @Int.0)
}

public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print(int_to_string(set_size(mk(1))))
}
"""


def test_repro_set_add_at_a_return_1865() -> None:
    assert _mismatches(_SET_RETURN) == []
    assert pipeline.run(_SET_RETURN).stdout == "1"


_STORE_JOIN = """\
type NE = { @Array<Int> | array_length(@Array<Int>.0) > 0 };

private data W { MkW(NE) }

public fn f(@Bool, @Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @W = MkW(if @Bool.0 then { @Array<Int>.0 } else { @Array<Int>.0 });
  match @W.0 { MkW(@NE) -> array_length(@NE.0) }
}
"""


def test_repro_a_join_in_a_non_scalar_store_is_disclosed_as_the_store_is() -> None:
    """The join of a non-scalar store is held as its leaf would be: the
    store guards only a scalar-based refinement, so the row is disclosed
    and the binder's check stands."""
    assert _mismatches(_STORE_JOIN) == []
    verified = _verified_clean(_STORE_JOIN)
    assert _statuses(verified, "refine_bind", 10) == ["tier3_unguarded"]


_SET_ELEMENT = """\
type Pos = { @Int | @Int.0 > 0 };
type Big = { @Int | @Int.0 > 100 };

public fn st(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Set<Pos> = set_add(set_new(), float_to_int(@Float64.0));
  set_size(@Set<Pos>.0)
}

public fn mk(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<Pos, Big> = map_insert(map_new(), float_to_int(@Float64.0), 500);
  map_size(@Map<Pos, Big>.0)
}
"""


@pytest.mark.parametrize(("fn", "where"), [
    ("st", "set element insert"), ("mk", "map key insert")])
def test_repro_set_add_element_and_map_insert_key_take_the_store_guard(
        fn: str, where: str) -> None:
    """#1542's line for a container with refined elements: `set_add`'s
    element and `map_insert`'s key are guarded as `map_insert`'s value is,
    each against its own refinement (a key of 5 is a `Pos` and no `Big`),
    and the trap names the store."""
    assert _mismatches(_SET_ELEMENT) == []
    assert pipeline.run(_SET_ELEMENT, fn=fn, args=[5.0]).value == 1
    ran = pipeline.run(_SET_ELEMENT, fn=fn, args=[-5.0])
    assert ran.trap is not None
    assert f"Refinement violation in {where}\n" in str(ran.trap), ran.trap


# =====================================================================
# #1885: a closure wider than its function type
# =====================================================================

#: The function type's parameter, and the closure's, by how they relate.
RELATIONS: dict[str, tuple[str, str]] = {
    "wider": ("Pos", "Int"), "equal": ("Pos", "Pos"), "narrower": ("Int", "Pos"),
}
#: The argument: refused by the solver, proved, or left to run time (the
#: `@Float64` is `t`'s argument).
VARIANCE_ARGS = {"refuted": "0", "proved": "5",
                 "undecided": "float_to_int(@Float64.0)"}
ROUTES = ("let", "param", "field", "join_arm", "generic")


def variance_program(route: str, relation: str, arg: str) -> str:
    fty, cty = RELATIONS[relation]
    closure = f"fn(@{cty} -> @Int) effects(pure) {{ 7 }}"
    other = f"fn(@{fty} -> @Int) effects(pure) {{ 8 }}"
    a = VARIANCE_ARGS[arg]
    body = {
        "let": f"  let @F = {closure};\n  apply_fn(@F.0, {a})\n",
        "param": f"  run_f({closure}, @Float64.0)\n",
        "field": (f"  let @Holder = H({closure});\n"
                  f"  match @Holder.0 {{ H(@F) -> apply_fn(@F.0, {a}) }}\n"),
        "join_arm": (f"  let @F = if @Bool.0 then {{ {closure} }} "
                     f"else {{ {other} }};\n  apply_fn(@F.0, {a})\n"),
        "generic": f"  let @F = {closure};\n  app(@F.0, {a})\n",
    }[route]
    helper = {
        "param": ("private fn run_f(@F, @Float64 -> @Int)\n" + PLAIN
                  + "{\n  apply_fn(@F.0, " + a + ")\n}\n\n"),
        "field": "private data Holder { H(F) }\n\n",
        "generic": ("private forall<T> fn app(@G<T>, @T -> @Int)\n" + PLAIN
                    + "{\n  apply_fn(@G<T>.0, @T.0)\n}\n\n"),
    }.get(route, "")
    return (
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "type G<T> = fn(T -> Int) effects(pure);\n"
        f"type F = fn({fty} -> Int) effects(pure);\n\n"
        + helper
        + "public fn t(@Bool, @Float64 -> @Int)\n" + PLAIN
        + "{\n" + body + "}\n")


_AT_THE_CALL = "Refinement violation in closure argument"

#: The cells whose argument meets the function type's refined parameter at
#: the `apply_fn`: every route bar the generic, whose instance is chosen
#: from the argument, at a closure as wide as its type or wider.
CALL_CELLS = list(itertools.product(
    ("let", "param", "field", "join_arm"), ("wider", "equal"),
    tuple(VARIANCE_ARGS)))


@pytest.mark.parametrize(
    ("route", "relation", "arg"), CALL_CELLS,
    ids=["-".join(c) for c in CALL_CELLS])
def test_a_closure_argument_is_held_at_the_call(
        route: str, relation: str, arg: str) -> None:
    """Spec §6.7: the function type's refined parameter is verified at the
    call site, whatever closure runs; a refuted argument is refused, a
    proved one runs, and an undecided one is checked at the call."""
    source = variance_program(route, relation, arg)
    if arg == "refuted":
        verified = pipeline.verify(source, reconcile=True)
        assert "E505" in {d.error_code for d in verified.errors}
        return
    verified = _verified_clean(source)
    where = "run_f" if route == "param" else "t"
    statuses = {o.status for o in verified.obligations
                if o.kind == "refine_bind" and o.fn_name == where}
    assert ("tier3" if arg == "undecided" else "verified") in statuses
    assert pipeline.run(source, fn="t", args=[1, 5.0]).value == 7
    ran = pipeline.run(source, fn="t", args=[1, -5.0])
    if arg == "proved":
        assert ran.value == 7
    else:
        assert ran.trap is not None
        assert _AT_THE_CALL in str(ran.trap)


def test_repro_a_closure_wider_than_its_type_is_checked_at_the_call_1885() -> None:
    """#1885's program: a `fn(@Int -> @Int)` bound at `fn(Pos -> Int)` and
    applied to an argument the solver cannot decide.  The record says the
    argument is checked at run time (`E506`), and the check runs at the
    call, against the function type's parameter."""
    source = """\
type Pos = { @Int | @Int.0 > 0 };
type F = fn(Pos -> Int) effects(pure);

public fn main(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @F = fn(@Int -> @Int) effects(pure) { @Int.0 };
  apply_fn(@F.0, float_to_int(@Float64.0))
}
"""
    verified = _verified_clean(source)
    assert _statuses(verified, "refine_bind", 10) == ["tier3"]
    assert "E506" in {d.error_code for d in verified.warnings}
    assert pipeline.run(source, fn="main", args=[5.0]).value == 5
    ran = pipeline.run(source, fn="main", args=[-5.0])
    assert ran.trap is not None
    assert _AT_THE_CALL in str(ran.trap)


OPEN_CELLS = [("narrower", route) for route in ROUTES]


@pytest.mark.parametrize(("relation", "route"), OPEN_CELLS,
                         ids=["-".join(c) for c in OPEN_CELLS])
@pytest.mark.xfail(strict=True, reason=(
    "#1885's open line: a closure narrower than the function type it flows "
    "into (a `fn(Pos -> Int)` at a `fn(Int -> Int)`, by every route, and at "
    "a generic instance chosen from the argument) is accepted with no row at "
    "the flow, and its entry check, recorded `verified`, traps on a value "
    "the function type admits"))
def test_a_closure_narrower_than_its_type_is_refused(
        relation: str, route: str) -> None:
    source = variance_program(route, relation, "refuted")
    verified = pipeline.verify(source, reconcile=True)
    if not verified.ok:
        return
    # Accepted: then the run must not refuse a value the type admits.
    ran = pipeline.run(source, fn="t", args=[1, 5.0])
    assert ran.trap is None, str(ran.trap)


# =====================================================================
# Regression cells
# =====================================================================

_GENERIC_JOIN = """\
type PosInt = { @Int | @Int.0 > 0 };

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn t(@Bool, @PosInt, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  idg(if @Bool.0 then { @Int.0 } else { @PosInt.0 })
}
"""


def test_a_generic_call_of_a_join_with_a_refined_arm_joins_clean() -> None:
    """#1542's generic-join line: since the checker joins disagreeing arms
    at their common type (#1684), `T` is `Int` and the argument owes no
    refinement, so nothing is claimed and the value passes."""
    assert _mismatches(_GENERIC_JOIN) == []
    verified = _verified_clean(_GENERIC_JOIN)
    assert _statuses(verified, "refine_bind", 16) == []
    assert pipeline.run(_GENERIC_JOIN, fn="t", args=[1, 1, -5]).value == -5
