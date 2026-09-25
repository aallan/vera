"""An integer literal takes its type from its context (#1541, #1565).

Spec §4.2: integer literals are checked against the type their context
expects.  When a generic call infers its type arguments, that context is the
call's other arguments (a closure's declared parameter types, a slot, a
call result) and the type the call's result is expected at.  The checker
used to type a literal, and a literal-only expression such as `0 - 3`,
bottom-up as `@Nat`, and let that `Nat` fix the type argument before any of
that context was read:

* **#1541** — `0 - 3` is two non-negative literals, so `Nat - Nat`, so
  `id(0 - 3)` was `id` at `Nat`, `[0 - 1, 5]` an `Array<Nat>`, and
  `map_insert(m, "k", 0 - 1)` a `Map<String, Nat>`.  The `@Nat` guards on
  those instantiations refused (E503) or trapped programs whose value is
  plainly -3.
* **#1565** — in SKILL.md's sum idiom `array_fold(xs, 0, fn(@Int, @Int ->
  @Int) ...)` the accumulator `0` bound `U = Nat` first, and the closure's
  declared `@Int` never displaced it, so the sum trapped once it went
  negative.  Typing a literal-only expression by its value does not reach
  this one: `0` IS a `Nat` by value.

The rule the checker now follows:

1. a literal-only integer expression whose value is negative is `@Int`;
2. a type argument a literal would fix is fixed first by the call's other
   arguments, then by the type its result is expected at, and only when
   neither constrains it by the literal's own value (`Nat` when every such
   literal is non-negative, `Int` otherwise).

A program that is genuinely wrong stays refused: a negative literal whose
context is `@Nat` is a narrowing, obligated and refused (E503) as before —
#1541's `get_nat(id(W(0 - 3)))` among them, and a tuple destructure's and a
refinement of `Nat`'s context too.

With `0 - 3` an `@Int`, `@Nat.0 + (0 - 3)` is a `Nat + Int` — an `@Int`
operation on the `@Nat`'s bits (PR #1583 review, #1588).  The last blocks
hold every `@Nat` such an operation reads to its widening: computed in
range, trapping above `i64.MAX`, obligated and guarded at one site.
"""

from __future__ import annotations

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.codegen.api import WasmTrapError
from vera.parser import parse_to_ast
from vera.verifier import verify

_ID = """private forall<T> fn id(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""


def _codes(source: str) -> list[str]:
    """Every error code `vera verify` reports: the checker's, then the
    verifier's (the verifier runs only on a check-clean program)."""
    ast = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(
        ast, source, collect_module_artifacts=True)
    errors = [d.error_code for d in diags if d.severity == "error"]
    if errors:
        return errors
    result = verify(ast, source,
                    expr_types=arts.expr_semantic_types,
                    expr_target_types=arts.expr_target_types,
                    module_artifacts=arts.module_artifacts)
    return [d.error_code for d in result.diagnostics
            if d.severity == "error"]


def _run(source: str, fn: str, args: list[int]) -> int | str:
    """The value the program returns, or the trap text.

    Built the way `vera run` builds it: the checker's semantic and target
    tables go to code generation, which reads them to decide the guards —
    compiled without them, the release branch's traps do not reproduce."""
    ast = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(
        ast, source, collect_module_artifacts=True)
    assert not [d for d in diags if d.severity == "error"], diags
    result = codegen_compile(
        ast, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts)
    assert result.ok, result.diagnostics
    try:
        return execute(result, fn_name=fn, args=args).value
    except WasmTrapError as exc:
        return f"trap: {exc}"


def _fn(body: str, ret: str = "Int", param: str = "Int") -> str:
    return f"""
public fn f(@{param} -> @{ret})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""


# ---------------------------------------------------------------------
# Rule 1: a literal-only expression whose value is negative is `Int`;
# otherwise its operators type it.  Read from the
# checker's `expr_types` table, so the type is the one synthesized and not
# a consequence observed downstream.
# ---------------------------------------------------------------------

_BY_VALUE = {
    "0 - 3": "Int",
    "2 - 5": "Int",
    "(0 - 3) + 1": "Int",
    "(1 - 4) * 2": "Int",
    "(0 - 7) / 2": "Int",
    "(0 - 7) % 2": "Int",
    "5 - 2": "Nat",
    "(0 - 3) - (0 - 5)": "Int",
    "3 * 4": "Nat",
    "7 / 0": "Nat",
}


class TestLiteralOnlyTypedByValue:
    @pytest.mark.parametrize("expr", sorted(_BY_VALUE))
    def test_synthesized_type(self, expr: str) -> None:
        # Written as a tuple component, a position with no type of its own
        # (`Tuple(...)` synthesizes each component with no expected type).
        source = _fn(f"let Tuple<@Int, @Int> = Tuple(0, {expr});\n  @Int.0")
        ast = parse_to_ast(source)
        _diags, arts = typecheck_with_artifacts(ast, source)
        line = source.splitlines().index(
            f"  let Tuple<@Int, @Int> = Tuple(0, {expr});") + 1
        col = len("  let Tuple<@Int, @Int> = Tuple(0, ") + 1
        key = (line, col, line, col + len(expr))
        assert arts.expr_types[key] == _BY_VALUE[expr]


# ---------------------------------------------------------------------
# The regression cells: programs `main` (6dc41d40) ran, which the release
# branch refused (E503) or trapped on ("Negative value bound into a @Nat
# slot").  Each must verify clean and return what `main` returns.
# ---------------------------------------------------------------------

REGRESSION_CELLS = {
    "h3b_generic_tuple_match": (
        _ID + _fn("match id(Tuple(1, 0 - 3)) {\n"
                  "    Tuple(@Int, @Int) -> @Int.0\n  }"), 0, -3),
    "h1_index_generic_call_let": (
        _fn("let @Int = array_append([0 - 3], 1)[0];\n  @Int.0"), 0, -3),
    "h2_index_generic_call_slot": (
        _fn("let @Array<Int> = array_append([0 - 3], 1);\n"
            "  let @Int = @Array<Int>.0[0];\n  @Int.0"), 0, -3),
    "h3_index_reverse_return": (
        _fn("array_reverse([0 - 3, 4])[1]"), 0, -3),
    "h4_tuple_index_generic": (
        _fn("let Tuple<@Int, @Int> = "
            "Tuple(1, array_append([0 - 3], 1)[0]);\n  @Int.0"), 0, -3),
    "i2_array_reverse_slot": (
        _fn("let @Array<Int> = array_reverse([0 - 1, 5]);\n"
            "  @Array<Int>.0[1]"), 0, -1),
    "i5_map_insert_lit": (
        _fn('map_size(map_insert(map_new(), "k", 0 - 1))', ret="Nat"),
        0, 1),
    "s09_slot_minus_index_generic": (
        _fn("@Nat.0 - array_reverse([0 - 1, 5])[0]", param="Nat"), 2, -3),
}


class TestRegressionCells:
    @pytest.mark.parametrize("name", sorted(REGRESSION_CELLS))
    def test_verifies_clean(self, name: str) -> None:
        source, _arg, _want = REGRESSION_CELLS[name]
        assert _codes(source) == []

    @pytest.mark.parametrize("name", sorted(REGRESSION_CELLS))
    def test_runs_as_on_main(self, name: str) -> None:
        source, arg, want = REGRESSION_CELLS[name]
        assert _run(source, "f", [arg]) == want


# ---------------------------------------------------------------------
# #1541: the issue's programs.
# ---------------------------------------------------------------------

_WRAP = """private data Wrap<A> { W(A) }

private fn get_nat(@Wrap<Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Wrap<Nat>.0 { W(@Nat) -> @Nat.0 }
}
""" + _ID


class TestIssue1541:
    def test_scalar_returns_the_negative_value(self) -> None:
        source = _ID + _fn("let @Int = id(0 - 3);\n  @Int.0")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -3

    def test_escape_stays_refused(self) -> None:
        # `W(0 - 3)` meets `@Wrap<Nat>` through `id`'s result: the literal's
        # context is `@Nat`, so -3 is a narrowing the verifier refutes.
        source = _WRAP + _fn("get_nat(id(W(0 - 3)))", ret="Nat")
        assert "E503" in _codes(source)

    def test_escape_built_at_the_site_stays_refused(self) -> None:
        source = _WRAP + _fn("get_nat(W(0 - 3))", ret="Nat")
        assert "E503" in _codes(source)

    def test_show_of_a_negative_field(self) -> None:
        source = _WRAP + _fn(
            "string_length(show(W(0 - 3)))", ret="Nat")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == len("W(-3)")

    def test_composite_let_reads_the_negative_field(self) -> None:
        source = _WRAP + _fn(
            "let @Wrap<Int> = W(0 - 3);\n"
            "  match @Wrap<Int>.0 { W(@Int) -> @Int.0 }")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -3

    def test_nat_context_still_refuses_a_negative_literal(self) -> None:
        # The context wins over the literal's value in both directions: an
        # expected `@Nat` makes `id` a `Nat` function, and -3 cannot be one.
        source = _ID + _fn("let @Nat = id(0 - 3);\n  @Nat.0", ret="Nat")
        assert "E503" in _codes(source)

    def test_a_nat_argument_fixes_the_instantiation(self) -> None:
        # A genuine `@Nat` argument is a constraint, not a default: `T` is
        # `Nat`, and the literal -3 in the other `@T` position is refused.
        source = """private forall<T> fn second(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
""" + _fn("second(@Nat.0, 0 - 3)", param="Nat")
        assert "E503" in _codes(source)


    def test_nested_generic_call_in_a_nat_field_is_refused(self) -> None:
        # The `@Nat` sibling fixes `MkTwo`'s `A`; `id(0 - 1)` is then checked
        # against that field, so its own instantiation is `Nat` and -1 is a
        # narrowing (without the field re-check it verified clean and
        # trapped).
        source = """private data Two<A> { MkTwo(A, A) }
""" + _ID + _fn(
            "match MkTwo(@Nat.0, id(0 - 1)) {\n"
            "    MkTwo(@Nat, @Nat) -> nat_to_int(@Nat.0)\n  }",
            param="Nat")
        assert "E503" in _codes(source)

    def test_refined_context_checks_the_literal(self) -> None:
        # A literal whose context is a refinement meets the predicate: the
        # `Option<Pos>` argument fixes `option_unwrap_or` at `Pos`, and the
        # default -1 is not one.
        source = """type Pos = { @Int | @Int.0 > 0 };

private fn pos_opt(@Unit -> @Option<Pos>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(9)
}
""" + _fn("option_unwrap_or(pos_opt(()), 0 - 1)")
        assert "E505" in _codes(source)


# ---------------------------------------------------------------------
# #1565: SKILL.md's array_fold sum idiom, on data that goes negative.
# ---------------------------------------------------------------------

_SUM = """public fn sum(@Array<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })
}
"""


class TestIssue1565:
    def test_skill_sum_idiom_goes_negative(self) -> None:
        source = _SUM + _fn("sum([3, 0 - 5])")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -2

    def test_skill_sum_idiom_over_a_let(self) -> None:
        source = _SUM + _fn(
            "let @Array<Int> = [3, 0 - 5, 0 - 7];\n  sum(@Array<Int>.0)")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -9

    def test_negative_accumulator_literal(self) -> None:
        source = _fn(
            "array_fold([0 - 5, 0 - 7], 0 - 1, "
            "fn(@Int, @Int -> @Int) effects(pure) { @Int.0 })")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -7

    def test_fold_over_a_mapped_array(self) -> None:
        source = _fn(
            "array_fold(array_map([1, 2], fn(@Int -> @Int) effects(pure) "
            "{ 0 - 5 }), 0, fn(@Int, @Int -> @Int) effects(pure) "
            "{ @Int.0 })")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -5

    def test_closure_fixes_the_accumulator_type(self) -> None:
        # The closure's declared `@Int` is the literal accumulator's context,
        # so the fold is `U = Int` and the result needs no widening at all.
        source = _fn(
            "array_fold([1, 2], 0, fn(@Int, @Int -> @Int) effects(pure) "
            "{ @Int.1 - @Int.0 - 10 })")
        assert _codes(source) == []
        assert _run(source, "f", [0]) == -23

    def test_nat_closure_keeps_a_nat_accumulator(self) -> None:
        # The dual: a closure that declares its accumulator `@Nat` makes the
        # literal a `Nat`, and a negative one is refused.
        source = _fn(
            "array_fold([1, 2], 0 - 1, fn(@Nat, @Int -> @Nat) effects(pure) "
            "{ @Nat.0 })", ret="Nat")
        assert "E503" in _codes(source)


# ---------------------------------------------------------------------
# The class, generated: every literal shape through every generic host,
# read back at `@Int` from a rotating position.  The answer is known for
# each cell (the literal's value), so no cell rests on another compiler.
# The full product (every position for every pair) is the PR's
# differential instrument; this is its pairwise cover, cheap enough for
# the suite.
# ---------------------------------------------------------------------

_SHAPES = {
    "zero": ("0", 0),
    "three": ("3", 3),
    "sub_0_3": ("0 - 3", -3),
    "neg_3": ("-3", -3),
    "sub_2_5": ("2 - 5", -3),
    "nest_add": ("(0 - 3) + 1", -2),
    "nest_mul": ("(1 - 4) * 2", -6),
    "nest_sub": ("(0 - 3) - (0 - 5)", 2),
}

_HOSTS_PRELUDE = _ID + """
private data Box<A> { MkBox(A) }

private data Two<A> { MkTwo(A, A) }

private forall<T> fn second(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private fn take(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}

private fn unbox(@Box<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box<Int>.0 { MkBox(@Int) -> @Int.0 }
}
"""

# name -> (an `@Int` expression over the literal L, or None; the slot form
# as (declared type, host call, read of the slot), or None)
_HOSTS: dict[str, tuple[str, tuple[str, str, str] | None]] = {
    "id": ("id({L})", None),
    "second_literal": ("second(7, {L})", None),
    "second_slot": ("second(@Int.0, {L})", None),
    "ctor": ("match MkBox({L}) { MkBox(@Int) -> @Int.0 }",
             ("Box<Int>", "MkBox({L})",
              "match @Box<Int>.0 { MkBox(@Int) -> @Int.0 }")),
    "ctor_two_fields": ("match MkTwo(1, {L}) { MkTwo(@Int, @Int) -> @Int.0 }",
                        ("Two<Int>", "MkTwo(1, {L})",
                         "match @Two<Int>.0 { MkTwo(@Int, @Int) -> @Int.0 }")),
    "ctor_through_id": ("unbox(id(MkBox({L})))",
                        ("Box<Int>", "id(MkBox({L}))", "unbox(@Box<Int>.0)")),
    "array_reverse": ("array_reverse([{L}, 5])[1]",
                      ("Array<Int>", "array_reverse([{L}, 5])",
                       "@Array<Int>.0[1]")),
    "array_reverse_second": ("array_reverse([5, {L}])[0]",
                             ("Array<Int>", "array_reverse([5, {L}])",
                              "@Array<Int>.0[0]")),
    "array_append": ("array_append([{L}], 1)[0]",
                     ("Array<Int>", "array_append([{L}], 1)",
                      "@Array<Int>.0[0]")),
    "array_append_element": ("array_append([1], {L})[1]",
                             ("Array<Int>", "array_append([1], {L})",
                              "@Array<Int>.0[1]")),
    "array_map": ("array_map([1, 2], fn(@Int -> @Int) effects(pure) { {L} })[0]",
                  None),
    "array_fold_accumulator": (
        "array_fold([1, 2], {L}, fn(@Int, @Int -> @Int) effects(pure) "
        "{ @Int.1 })", None),
    "array_fold_sum": (
        "array_fold([{L}], 0, fn(@Int, @Int -> @Int) effects(pure) "
        "{ @Int.1 + @Int.0 })", None),
    "array_fold_id_accumulator": (
        "array_fold([1], id({L}), fn(@Int, @Int -> @Int) effects(pure) "
        "{ @Int.1 })", None),
    "map_insert": ('option_unwrap_or(map_get(map_insert(map_new(), "k", {L}), '
                   '"k"), 0)', None),
    "tuple": ("match Tuple(1, {L}) { Tuple(@Int, @Int) -> @Int.0 }",
              ("Tuple<Int, Int>", "Tuple(1, {L})",
               "match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 }")),
    "tuple_through_id": (
        "match id(Tuple(1, {L})) { Tuple(@Int, @Int) -> @Int.0 }",
        ("Tuple<Int, Int>", "id(Tuple(1, {L}))",
         "match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.0 }")),
    "option_through_id": ("option_unwrap_or(id(Some({L})), 0)", None),
    "if_branch": ("id(if @Int.0 == 0 then { {L} } else { 5 })", None),
    "pipe": ("({L}) |> id()", None),
}

_POSITIONS = ("let", "argument", "return", "match", "slot")


def _cell_body(position: str, host: str, literal: str) -> str:
    expr, slot = _HOSTS[host]
    e = expr.replace("{L}", literal)
    if position == "slot" and slot is not None:
        ty, call, read = slot
        return f"let @{ty} = {call.replace('{L}', literal)};\n  {read}"
    if position == "let" or position == "slot":
        return f"let @Int = {e};\n  @Int.0"
    if position == "argument":
        return f"take({e})"
    if position == "match":
        return f"match {e} {{ @Int -> @Int.0 }}"
    return e


def _class_cells() -> list[tuple[str, str, int]]:
    cells = []
    for i, (shape, (literal, value)) in enumerate(sorted(_SHAPES.items())):
        for j, host in enumerate(sorted(_HOSTS)):
            position = _POSITIONS[(i + j) % len(_POSITIONS)]
            if position == "match" and (host.startswith("array_fold")
                                        or host == "pipe"):
                # A `match` directly on an `array_fold` or a pipe result is
                # dropped at compile on every revision, whatever the literal
                # (#1578).
                position = "let"
            source = _HOSTS_PRELUDE + _fn(
                _cell_body(position, host, literal))
            cells.append((f"{shape}-{host}-{position}", source, value))
    return cells


_CLASS_CELLS = _class_cells()


class TestLiteralClassMatrix:
    def test_matrix_covers_every_shape_host_and_position(self) -> None:
        names = [n for n, _s, _w in _CLASS_CELLS]
        assert len(names) == len(_SHAPES) * len(_HOSTS)
        assert {n.split("-")[0] for n in names} == set(_SHAPES)
        assert {n.split("-")[1] for n in names} == set(_HOSTS)
        assert {n.split("-")[2] for n in names} == set(_POSITIONS)

    @pytest.mark.parametrize(
        ("name", "source", "want"), _CLASS_CELLS,
        ids=[c[0] for c in _CLASS_CELLS])
    def test_cell_verifies_and_returns_the_literal(
            self, name: str, source: str, want: int) -> None:
        assert _codes(source) == [], name
        assert _run(source, "f", [0]) == want, name


# A literal whose context is `@Nat`: the type its result is expected at, a
# `@Nat` sibling argument, a closure's `@Nat` parameter, a `@Box<Nat>` or an
# `@Array<Nat>` consumer.  A non-negative literal runs; a negative one is
# refused (E503) — the context decides, in both directions.
_NAT_PRELUDE = _HOSTS_PRELUDE + """
private fn nat_of(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

private fn unbox_nat(@Box<Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box<Nat>.0 { MkBox(@Nat) -> @Nat.0 }
}

private fn nats_of(@Array<Nat> -> @Array<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Array<Nat>.0
}

type Small = { @Nat | @Nat.0 < 100 };

private fn small_of(@Small -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(@Small.0)
}
"""

_NAT_HOSTS = {
    "expected_result": "let @Nat = id({L});\n  nat_to_int(@Nat.0)",
    # A tuple whose component type is `Nat`, and a refinement of `Nat`, as
    # the type the call's result is expected at (PR #1583 review): the
    # tuple's components and the refinement's base are the literal's
    # context too.
    "tuple_id_let": ("let Tuple<@Nat, @Nat> = id(Tuple(1, {L}));\n"
                     "  nat_to_int(@Nat.0)"),
    "tuple_sibling": ("match second(Tuple(nat_of(1), nat_of(1)), "
                      "Tuple(1, {L})) { Tuple(@Nat, @Nat) -> "
                      "nat_to_int(@Nat.0) }"),
    "tuple_second_let": ("let Tuple<@Nat, @Nat> = second(Tuple(1, 2), "
                         "Tuple(5, {L}));\n  nat_to_int(@Nat.0)"),
    "small_let_id": "let @Small = id({L});\n  nat_to_int(@Small.0)",
    "small_arg_id": "small_of(id({L}))",
    "small_sibling": ("let @Small = 5;\n"
                      "  nat_to_int(second(@Small.0, {L}))"),
    "option_id_let": ("let @Option<Nat> = id(Some({L}));\n"
                      "  match @Option<Nat>.0 { Some(@Nat) -> "
                      "nat_to_int(@Nat.0), None -> 0 }"),
    "nested_id_let": "let @Nat = id(id({L}));\n  nat_to_int(@Nat.0)",
    "nat_sibling": "nat_to_int(second(nat_of(3), {L}))",
    "nat_closure": ("nat_to_int(array_fold([1, 2], {L}, fn(@Nat, @Int -> "
                    "@Nat) effects(pure) { @Nat.0 }))"),
    "nat_box_consumer": "nat_to_int(unbox_nat(id(MkBox({L}))))",
    "nat_array_consumer": "nat_to_int(array_reverse(nats_of([{L}]))[0])",
    "nat_element_sibling": "nat_to_int(array_reverse([nat_of(3), {L}])[0])",
}

_NAT_CELLS = [
    (f"{shape}-{host}", _NAT_PRELUDE + _fn(body.replace("{L}", literal)),
     value)
    for shape, (literal, value) in sorted(_SHAPES.items())
    for host, body in sorted(_NAT_HOSTS.items())
] + [
    # The same contexts one level further in, where the value read back is
    # not the literal: a tuple inside a `Box`, and inside an array.
    (f"{shape}-{host}", _NAT_PRELUDE + _fn(body.replace("{L}", literal)),
     want if value >= 0 else value)
    for shape, (literal, value) in sorted(_SHAPES.items())
    for host, (body, want) in sorted({
        "box_tuple_let": (
            "let @Box<Tuple<Nat, Nat>> = id(MkBox(Tuple(1, {L})));\n"
            "  match @Box<Tuple<Nat, Nat>>.0 { MkBox(@Tuple<Nat, Nat>) -> 7 }",
            7),
        "arr_tuple_let": (
            "let @Array<Tuple<Nat, Nat>> = id([Tuple(1, {L})]);\n"
            "  nat_to_int(array_length(@Array<Tuple<Nat, Nat>>.0))", 1),
    }.items())
]


class TestNatContextMatrix:
    @pytest.mark.parametrize(
        ("name", "source", "value"), _NAT_CELLS,
        ids=[c[0] for c in _NAT_CELLS])
    def test_context_decides(self, name: str, source: str,
                             value: int) -> None:
        if value < 0:
            # A `Small` sibling meets the literal at the refinement itself,
            # whose predicate refutes it first (E505).
            refusals = ({"E503", "E505"} if name.endswith("-small_sibling")
                        else {"E503"})
            assert refusals & set(_codes(source)), name
        else:
            assert _codes(source) == [], name
            assert _run(source, "f", [0]) == value, name


# A literal cannot have the enclosing function's rigid type parameter:
# inside `forall<T>` a `T` is opaque.  A literal's hole must not be
# overwritten by `T` whichever argument comes first (PR #1583 review) —
# accepted, the clone at `T = String` received an i64 where a string was
# expected and the module failed to load.
_RIGID_HOSTS = {
    "call_literal_first": "second({L}, @T.0)",
    "call_literal_second": "second(@T.0, {L})",
    "ctor_literal_first": "match MkTwo({L}, @T.0) { MkTwo(@T, @T) -> @T.0 }",
    "ctor_literal_second": "match MkTwo(@T.0, {L}) { MkTwo(@T, @T) -> @T.0 }",
    "nested_call_first": "second(id({L}), @T.0)",
    "tuple_first": ("match second(Tuple({L}, 1), Tuple(@T.0, @T.0)) "
                    "{ Tuple(@T, @T) -> @T.0 }"),
}


def _rigid_source(body: str) -> str:
    return _HOSTS_PRELUDE + f"""
private forall<T> fn g(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}

public fn f(@String -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{{
  string_length(g(@String.0))
}}
"""


_RIGID_CELLS = [
    (f"{shape}-{host}", _rigid_source(body.replace("{L}", literal)))
    for shape, (literal, _value) in sorted(_SHAPES.items())
    for host, body in sorted(_RIGID_HOSTS.items())
]


class TestRigidTypeParameter:
    @pytest.mark.parametrize(("name", "source"), _RIGID_CELLS,
                             ids=[c[0] for c in _RIGID_CELLS])
    def test_a_literal_is_not_a_rigid_type_parameter(
            self, name: str, source: str) -> None:
        ast = parse_to_ast(source)
        diags, _arts = typecheck_with_artifacts(ast, source)
        assert [d for d in diags if d.severity == "error"], name


# A literal-only expression the checker types `Int` although its value is
# not negative (a negation, an `Int` operand) falls back to `Int` when
# nothing constrains it, as it did before #1541 (PR #1583 review): its own
# type is its type by value.
_INT_TYPED_NONNEGATIVE = ("-0", "(0 - 3) + 4", "-(0 - 3)")


class TestIntTypedNonNegativeFallsBackToInt:
    @pytest.mark.parametrize("expr", _INT_TYPED_NONNEGATIVE)
    def test_instantiation(self, expr: str) -> None:
        source = _ID + _fn(f"let Tuple<@Int, @Int> = Tuple(0, id({expr}));"
                           "\n  @Int.0")
        ast = parse_to_ast(source)
        _diags, arts = typecheck_with_artifacts(ast, source)
        line = source.splitlines().index(
            f"  let Tuple<@Int, @Int> = Tuple(0, id({expr}));") + 1
        col = len("  let Tuple<@Int, @Int> = Tuple(0, ") + 1
        key = (line, col, line, col + len(f"id({expr})"))
        assert arts.expr_types[key] == "Int"


# ---------------------------------------------------------------------
# A genuine `@Nat` operand beside an `@Int` one (PR #1583 review).
#
# With `0 - 3` an `Int`, `@Nat.0 + (0 - 3)` is a `Nat + Int`: the operation
# runs at the signed width, on the `@Nat`'s bits.  A `@Nat` above
# `i64.MAX` reads there as a negative `@Int`, and the result came back
# wrong and silent — against a Tier-1 `ensures` too — where `main` had
# read `0 - 3` as a `Nat` and trapped.  `@Nat.0 + @Int.0` did the same on
# every revision (#1588).  The `@Nat` operand is widened into the `@Int`
# operation, so it carries that widening's obligation and its guard.
#
# Every operator, both operand orders, each way a `@Nat` reaches the
# operation (a slot, a call's result, a constructor field, an array
# element), beside a negative literal and beside an `@Int` slot, with the
# result read at `@Int` and — for arithmetic — narrowed into `@Nat`.  At
# `@Nat.0 = 5` each cell computes its value; above `i64.MAX` it traps on
# the widening and returns nothing.
# ---------------------------------------------------------------------

_U64_MAX = 2 ** 64 - 1
_BIG_NATS = (2 ** 63, 2 ** 63 + 5, _U64_MAX)
_WIDEN_TRAP = "@Nat value above i64.MAX widened into an @Int slot"

_MIXED_PRELUDE = """private data NatBox { NB(Nat) }

private fn nat_of(@Nat -> @Nat)
  requires(true)
  ensures(@Nat.result == @Nat.0)
  effects(pure)
{
  @Nat.0
}
"""

#: How the `@Nat` operand is read.  The field form binds the constructor's
#: `@Nat` field as the arm's `@Nat.0`, around the whole body; the element
#: form indexes an `Array<Nat>` bound first.
_NAT_OPERANDS = {
    "slot": "@Nat.0",
    "call": "nat_of(@Nat.0)",
    "field": "@Nat.0",
    "element": "@Array<Nat>.0[0]",
}

#: The `@Int` sibling, and the value it holds (the slot is passed -3).
#: Neither operand is zero (`requires`), so a division is not refused for
#: its divisor.
_INT_OPERANDS = {"literal": "(0 - 3)", "slot": "@Int.0"}

_MIXED_ARITH = {"+": int.__add__, "-": int.__sub__, "*": int.__mul__,
                "/": lambda a, b: _trunc_div(a, b),
                "%": lambda a, b: a - b * _trunc_div(a, b)}
_MIXED_CMP = {"<": int.__lt__, "<=": int.__le__, ">": int.__gt__,
              ">=": int.__ge__, "==": int.__eq__, "!=": int.__ne__}

#: A constructor pattern binding a `@Nat` above `i64.MAX` traps as a
#: negative value on every revision, before the operation is reached
#: (#1589).  The field form's run above `i64.MAX` is that trap; its
#: widening is held to its site statically, as every cell's is.
_FIELD_BIND_TRAP = "Negative value bound into a @Nat slot"


def _trunc_div(a: int, b: int) -> int:
    """`i64.div_s`: truncation toward zero."""
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def _mixed_cells() -> list[tuple[str, str, str, int | None, str]]:
    """(id, source, result type, the value at `@Nat.0 = 5` or None where
    the program must refuse it: a negative result narrowed into `@Nat`,
    the operation's text).  An id is `order:op:source:sibling:result`."""
    cells = []
    for op, fn in {**_MIXED_ARITH, **_MIXED_CMP}.items():
        for order in ("nat_left", "nat_right"):
            for source, nat in _NAT_OPERANDS.items():
                for sibling, int_text in _INT_OPERANDS.items():
                    a, b = (5, -3) if order == "nat_left" else (-3, 5)
                    left, right = ((nat, int_text) if order == "nat_left"
                                   else (int_text, nat))
                    expr = f"{left} {op} {right}"
                    value = fn(a, b)
                    results = (("Int", "Nat") if op in _MIXED_ARITH
                               else ("Int",))
                    for ret in results:
                        if op in _MIXED_CMP:
                            body = f"if {expr} then {{ 1 }} else {{ 0 }}"
                            want: int | None = int(value)
                        elif ret == "Int":
                            body = f"let @Int = {expr};\n  @Int.0"
                            want = value
                        else:
                            body = (f"let @Nat = {expr};\n"
                                    "  nat_to_int(@Nat.0)")
                            want = value if value >= 0 else None
                        if source == "element":
                            body = ("let @Array<Nat> = [@Nat.0];\n  "
                                    + body)
                        if source == "field":
                            body = ("match NB(@Nat.0) {\n"
                                    f"    NB(@Nat) -> {{\n  {body}\n  }}"
                                    "\n  }")
                        program = _MIXED_PRELUDE + (
                            "public fn f(@Nat, @Int -> @Int)\n"
                            "  requires(@Nat.0 != 0 && @Int.0 != 0)\n"
                            "  ensures(true)\n"
                            f"  effects(pure)\n{{\n  {body}\n}}\n")
                        cells.append((
                            f"{order}:{op}:{source}:{sibling}:{ret}",
                            program, ret, want, expr))
    return cells


_MIXED_CELLS = _mixed_cells()


def _compile(source: str):  # type: ignore[no-untyped-def]
    ast = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(
        ast, source, collect_module_artifacts=True)
    assert not [d for d in diags if d.severity == "error"], diags
    result = codegen_compile(
        ast, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts)
    assert result.ok, result.diagnostics
    return result


def _run_many(source: str, fn: str,
              args_list: list[list[int]]) -> list[int | str]:
    """:func:`_run` for several argument lists over one compilation."""
    result = _compile(source)
    out: list[int | str] = []
    for args in args_list:
        try:
            out.append(execute(result, fn_name=fn, args=args).value)
        except WasmTrapError as exc:
            out.append(f"trap: {exc}")
    return out


def _widening_sites(source: str) -> tuple[set, set]:
    """The `nat_to_int_coerce` obligations' sites and the widening guards'
    sites, as (line, column)."""
    ast = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(
        ast, source, collect_module_artifacts=True)
    verified = verify(ast, source,
                      expr_types=arts.expr_semantic_types,
                      expr_target_types=arts.expr_target_types,
                      module_artifacts=arts.module_artifacts)
    claimed = {(o.line, o.column) for o in verified.obligations
               if o.kind == "nat_to_int_coerce"}
    guarded = {(c.line, c.column) for c in _compile(source).emitted_checks
               if c.emitter == "wasm/operators.py:_emit_int_widen_guard"}
    return claimed, guarded


class TestANatOperandBesideAnIntIsWidened:
    def test_the_matrix_covers_the_class(self) -> None:
        ids = [c[0].split(":") for c in _MIXED_CELLS]
        assert {i[1] for i in ids} == set(_MIXED_ARITH) | set(_MIXED_CMP)
        assert {i[0] for i in ids} == {"nat_left", "nat_right"}
        assert {i[2] for i in ids} == set(_NAT_OPERANDS)
        assert {i[3] for i in ids} == set(_INT_OPERANDS)
        assert {i[4] for i in ids} == {"Int", "Nat"}

    @pytest.mark.parametrize(
        ("name", "source", "ret", "want"), [c[:4] for c in _MIXED_CELLS],
        ids=[c[0] for c in _MIXED_CELLS])
    def test_computes_in_range_and_traps_above_it(
            self, name: str, source: str, ret: str,
            want: int | None) -> None:
        # A result narrowed into `@Nat` is refused (E503) where the
        # verifier cannot show it non-negative; nothing else is refused.
        codes = _codes(source)
        assert codes == [] or (ret == "Nat" and codes == ["E503"]), (
            name, codes)
        runs = _run_many(source, "f", [[5, -3]]
                         + [[big, -3] for big in _BIG_NATS])
        if want is None:
            assert str(runs[0]).startswith("trap:"), (name, runs)
        else:
            assert runs[0] == want, (name, runs)
        trap = _FIELD_BIND_TRAP if ":field:" in name else _WIDEN_TRAP
        for big, got in zip(_BIG_NATS, runs[1:]):
            assert trap in str(got), (name, big, got)

    @pytest.mark.parametrize(
        ("name", "source", "expr"), [(c[0], c[1], c[4]) for c in _MIXED_CELLS],
        ids=[c[0] for c in _MIXED_CELLS])
    def test_the_claim_and_the_guard_share_a_site(
            self, name: str, source: str, expr: str) -> None:
        """The `@Nat` operand's widening is obligated and guarded at the
        operand: the verifier's record and code generation's guard name
        the same sites, and the operation's line holds one."""
        claimed, guarded = _widening_sites(source)
        line = next(i for i, ln in enumerate(source.splitlines(), 1)
                    if expr in ln)
        assert claimed == guarded, (name, claimed, guarded)
        assert any(site[0] == line for site in claimed), (
            name, line, claimed)


# The finding's own programs, with a Tier-1 `ensures`: the widening traps
# before the postcondition could be reached with a reinterpreted value.
_MIXED_ENSURES = {
    "nat_plus_literal": ("@Nat.0 + (0 - 1)", "@Int.result >= 0 - 1"),
    "literal_times_nat": ("(0 - 1) * @Nat.0", "@Int.result <= 0"),
    "nat_minus_literal": ("@Nat.0 - (0 - 3)", "@Int.result >= 3"),
    "nat_plus_int": ("@Nat.0 + @Int.0", "@Int.result >= @Int.0"),
}


class TestATierOneEnsuresOverAMixedOperation:
    @pytest.mark.parametrize("name", sorted(_MIXED_ENSURES))
    def test_proved_and_never_violated(self, name: str) -> None:
        expr, post = _MIXED_ENSURES[name]
        source = ("public fn f(@Nat, @Int -> @Int)\n  requires(true)\n"
                  f"  ensures({post})\n  effects(pure)\n{{\n  {expr}\n}}\n")
        ast = parse_to_ast(source)
        _diags, arts = typecheck_with_artifacts(
            ast, source, collect_module_artifacts=True)
        result = verify(ast, source,
                        expr_types=arts.expr_semantic_types,
                        expr_target_types=arts.expr_target_types,
                        module_artifacts=arts.module_artifacts)
        assert not [d for d in result.diagnostics
                    if d.severity == "error"], name
        assert ("ensures", "verified") in {
            (o.kind, o.status) for o in result.obligations}, (
            name, result.obligations)
        runs = _run_many(source, "f", [[5, -1]]
                         + [[big, -1] for big in _BIG_NATS])
        assert isinstance(runs[0], int), (name, runs)
        for got in runs[1:]:
            assert _WIDEN_TRAP in str(got), (name, got)


# The `@Nat`-subtraction guard reads its operands as the verifier's
# `nat_sub` obligation does, the checker's type first (PR #1583 review).
# Read from their syntax, a call to a non-generic function declared `@Nat`
# was no `@Nat`, so the subtraction below was recorded and compiled with no
# check, and returned -3 from a `@Nat` function (#1557); `(0 - 3) - @Nat.0`
# was guarded as a `@Nat` subtraction the verifier did not record.
_NAT_ID = """private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""


class TestTheNatSubtractionGuardIsWhereItIsRecorded:
    @pytest.mark.parametrize(("body", "ret", "recorded"), [
        ("nat_id(@Nat.1) - @Nat.0", "Nat", True),
        ("(0 - 3) - @Nat.0", "Int", False),
    ], ids=["a call declared @Nat", "a negative literal"])
    def test_claim_and_guard(self, body: str, ret: str,
                             recorded: bool) -> None:
        source = _NAT_ID + f"""
public fn f(@Nat, @Nat -> @{ret})
  requires(true)
  ensures(true)
  effects(pure)
{{
  {body}
}}
"""
        ast = parse_to_ast(source)
        _diags, arts = typecheck_with_artifacts(
            ast, source, collect_module_artifacts=True)
        verified = verify(ast, source,
                          expr_types=arts.expr_semantic_types,
                          expr_target_types=arts.expr_target_types,
                          module_artifacts=arts.module_artifacts)
        claimed = {(o.line, o.column) for o in verified.obligations
                   if o.kind == "nat_sub"}
        guarded = {(c.line, c.column) for c in _compile(source).emitted_checks
                   if c.emitter == "wasm/operators.py:_emit_nat_sub_guard"}
        assert claimed == guarded, (claimed, guarded)
        assert bool(claimed) is recorded, claimed
        runs = _run_many(source, "f", [[2, 5]])
        if recorded:
            assert "would be negative" in str(runs[0]), runs
        else:
            assert runs[0] == -8, runs
