"""Every position that binds or passes a value at a written type holds the
value to `is_subtype(value, written)` in the direction it flows (#1896).

A `let` held its value to `is_subtype`; three other positions judged by a
test of their own:

- a handler clause's parameter (`throw(@T)`, `put(@T)`) was compared with
  nothing, and bound at the operation's type under the written name;
- a `match` binder asked whether the two types were related in EITHER
  direction, and skipped a function-typed scrutinee and one holding a type
  variable, so it could claim a type the value does not have;
- a call argument, a destructured component, an array element and a generic
  call's adopted result whose pair holds a type variable were fitted by the
  join, which compares an effect row inside a parameter's function type
  covariantly.

The rule: each reads every type variable the join or the call left open as
unknown (the enclosing function's own stay rigid), then asks `is_subtype`.
A pair that fits only by a narrowing inside a function type is E190; any
other is the site's own refusal: E342 at a clause parameter, E314 at a
binder, E202 at an argument, E170 at a component, an element or the `let`
an adopted result reaches.  A constructor or literal pattern over the
enclosing function's own bare type variable is E314 too: nothing says an
`A` is an `Option`.

The matrix: position x mismatch x context (inside a generic, outside).  A
refused cell asserts its code is the one error; an accepted cell checks
clean.  The narrower-row cells are what holds the binder refusal that
replaced the `effect_bind` disclosure (E542).
"""

from __future__ import annotations

import re

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/types.py", "vera/checker/core.py", "vera/checker/control.py",
    "vera/checker/calls.py", "vera/checker/expressions.py"])

_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"
_IO_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(<IO>)\n"


def _fn(signature: str, body: str, *, visibility: str = "private",
        contract: str = _CONTRACT) -> str:
    return f"{visibility} fn {signature}\n{contract}{{\n  {body}\n}}\n\n"


def _codes(source: str) -> list[str]:
    return sorted(d.error_code for d in pipeline.check(source).errors)


def _ran(source: str) -> str:
    ran = pipeline.run(source, fn="main")
    assert ran.trap is None, str(ran.trap)[:300]
    return ran.stdout


# =====================================================================
# The reported members, red before the fix
# =====================================================================

_SOME_ABC = _fn(
    "run(@Option<T> -> @Int)",
    "match @Option<T>.0 {\n    @Option<Int> -> option_unwrap_or(@Option<Int>.0, 0) + 1\n  }",
).replace("private fn run", "private forall<T> fn run") + _fn(
    "main(@Unit -> @Int)", 'run(Some("abc"))', visibility="public")


def test_repro_a_binder_at_a_concrete_type_over_a_type_variable_1896() -> None:
    """Was accepted, and `run(Some("abc"))` printed 4: the binder claimed
    `Option<Int>` of an `Option<T>`."""
    assert _codes(_SOME_ABC) == ["E314"], _SOME_ABC


_WHOLE_ROW = (
    "type W = fn(Int -> Int) effects(pure);\n"
    "type IOF = fn(Int -> Int) effects(<IO>);\n\n"
    + _fn("run(@Option<IOF> -> @Int)",
          "match @Option<IOF>.0 {\n    @Option<W> -> match @Option<W>.0 {\n"
          "      Some(@W) -> apply_fn(@W.0, 5),\n      None -> 0\n    }\n  }")
    + _fn("main(@Unit -> @Int)",
          'run(Some(fn(@Int -> @Int) effects(<IO>) { IO.print("leak\\n"); @Int.0 }))',
          visibility="public", contract=_IO_CONTRACT))


def test_repro_a_whole_type_binder_holding_a_narrower_row_1896() -> None:
    """Was accepted with no disclosure, and a `pure` function printed."""
    assert _codes(_WHOLE_ROW) == ["E314"], _WHOLE_ROW


_JOIN_A4 = (
    "type P = fn(Int -> Int) effects(pure);\n"
    "type I = fn(Int -> Int) effects(<IO>);\n"
    "type H<U> = fn(I, U -> Int) effects(pure);\n\n"
    + _fn("helper(@H<U>, @I, @U -> @Int)", "apply_fn(@H<U>.0, @I.0, @U.0)"
          ).replace("private fn", "private forall<U> fn")
    + _fn("outer(@I, @T -> @Int)",
          "helper(fn(@P, @T -> @Int) effects(pure) { apply_fn(@P.0, 1) }, "
          "@I.0, @T.0)").replace("private fn", "private forall<T> fn")
    + _fn("main(@Unit -> @Int)",
          'outer(fn(@Int -> @Int) effects(<IO>) { IO.print("leak\\n"); @Int.0 }, 7)',
          visibility="public", contract=_IO_CONTRACT))


def test_repro_the_join_compares_a_parameter_s_row_the_right_way_round_1896(
        ) -> None:
    """Was accepted (6 Tier 1) and printed from functions declared pure."""
    assert _codes(_JOIN_A4) == ["E202"], _JOIN_A4


_CLAUSE = _fn(
    "go(@Int -> @Int)",
    "handle[Exn<Int>] {\n    throw(@String) -> { @String.0 + 1 }\n"
    "  } in {\n    throw(@Int.0)\n  }", visibility="public")


def test_repro_a_clause_parameter_is_held_to_the_operation_s_type_1896(
        ) -> None:
    """Was accepted: `go(41)` gave 42 out of a slot declared `@String`.  The
    slot now has the type the clause writes, so the body's `String + 1` is
    refused as well (E140), as it is wherever a `String` is added to."""
    assert _codes(_CLAUSE) == ["E140", "E342"], _CLAUSE


def test_e342_s_fix_applied_as_written_checks() -> None:
    """E342's fix names the type the operation takes; the clause written at
    it checks with no E342."""
    diagnostic = next(d for d in pipeline.check(_CLAUSE).errors
                      if d.error_code == "E342")
    assert diagnostic.fix.startswith("Write the parameter as `@Int`"), (
        diagnostic.fix)
    fixed = _CLAUSE.replace("throw(@String) -> { @String.0 + 1 }",
                            "throw(@Int) -> { @Int.0 + 1 }")
    assert fixed != _CLAUSE
    assert _codes(fixed) == [], fixed


def test_a_function_typed_binder_s_fix_writes_no_slot_of_a_function_type(
        ) -> None:
    """A slot names a function type through an alias, so E314's fix gives
    the scrutinee's type in prose, never as `@fn(...)`."""
    diagnostic = next(d for d in pipeline.check(_WHOLE_ROW).errors
                      if d.error_code == "E314")
    assert "@fn(" not in diagnostic.fix and "@Option<fn(" not in diagnostic.fix, (
        diagnostic.fix)
    assert "named by a type alias" in diagnostic.fix, diagnostic.fix


_HEAD = _fn("run(@A -> @Int)",
            "match @A.0 {\n    Some(@Int) -> @Int.0 + 1,\n    _ -> 0\n  }"
            ).replace("private fn", "private forall<A> fn") + _fn(
    "main(@Unit -> @Int)", "run(Some(true))", visibility="public")


def test_repro_a_head_over_the_function_s_own_type_variable_1896() -> None:
    """Was accepted, verify clean, and the `Bool` read as an `Int`."""
    assert _codes(_HEAD) == ["E314"], _HEAD


def test_repro_a_wider_clause_binder_reads_its_written_type_1896() -> None:
    """`throw(@Int)` under `Exn<Nat>` binds an `Int`: the slot has the type
    the clause writes, and an `Int` use of it is not a `Nat`."""
    source = _fn("go(@Nat -> @Int)",
                 "handle[Exn<Nat>] {\n    throw(@Int) -> { @Int.0 - 10 }\n"
                 "  } in {\n    throw(@Nat.0)\n  }", visibility="public")
    assert _codes(source) == [], source


def test_repro_the_sound_shapes_stay_accepted_1896() -> None:
    """An open variable under a binder, a `@Nat` binder over an `Int`, and a
    wider function-typed binder check clean."""
    for source in (
            _fn("main(@Unit -> @Int)",
                "match None {\n    Some(@Int) -> @Int.0,\n    None -> 5\n  }",
                visibility="public"),
            _fn("main(@Unit -> @Int)",
                "match Ok(99) {\n    Ok(@Int) -> @Int.0,\n    Err(@String) -> 0\n  }",
                visibility="public"),
            _fn("run(@Int -> @Int)", "match @Int.0 {\n    @Nat -> nat_to_int(@Nat.0)\n  }"),
            "type II = fn(Int -> Int) effects(pure);\n"
            "type NI = fn(Nat -> Int) effects(pure);\n\n"
            + _fn("run(@II -> @Int)", "match @II.0 {\n    @NI -> apply_fn(@NI.0, 4)\n  }")):
        assert _codes(source) == [], source


# =====================================================================
# The matrix: position x mismatch x context
# =====================================================================

#: mismatch -> (the value's type, the written type, the value): the types
#: are aliases `VV` and `WW` where they can be written; `T` is the enclosing
#: generic's own variable, `?` a variable a call leaves open.
MISMATCHES: dict[str, tuple[str, str, str]] = {
    "same": ("fn(Int -> Int) effects(pure)", "fn(Int -> Int) effects(pure)",
             "fn(@Int -> @Int) effects(pure) { @Int.0 }"),
    "row-root": ("fn(Int -> Int) effects(<IO>)", "fn(Int -> Int) effects(pure)",
                 "fn(@Int -> @Int) effects(<IO>) { @Int.0 }"),
    "row-in-parameter": (
        "fn(fn(Int -> Int) effects(pure) -> Int) effects(pure)",
        "fn(fn(Int -> Int) effects(<IO>) -> Int) effects(pure)",
        "fn(@PF -> @Int) effects(pure) { apply_fn(@PF.0, 1) }"),
    "parameter-base": ("fn(String -> Int) effects(pure)",
                       "fn(Int -> Int) effects(pure)",
                       "fn(@String -> @Int) effects(pure) { 0 }"),
    "arity": ("fn(Int, Int -> Int) effects(pure)", "fn(Int -> Int) effects(pure)",
              "fn(@Int, @Int -> @Int) effects(pure) { @Int.0 }"),
    "result": ("fn(Int -> String) effects(pure)", "fn(Int -> Int) effects(pure)",
               'fn(@Int -> @String) effects(pure) { "s" }'),
    "narrowing": ("fn(Int -> Int) effects(pure)", "fn(Int -> Nat) effects(pure)",
                  "fn(@Int -> @Int) effects(pure) { @Int.0 }"),
    "scalar-nat": ("Int", "Nat", "5"),
    "rigid": ("T", "Int", "@T.0"),
    "open": ("?", "Option<Int>", "none_of(())"),
    # The enclosing generic's variable inside the function type itself, so
    # the pair reaches the join wherever it flows (generic cells only).
    "row-in-parameter-beside-T": (
        "fn(fn(Int -> Int) effects(pure), T -> Int) effects(pure)",
        "fn(fn(Int -> Int) effects(<IO>), T -> Int) effects(pure)",
        "fn(@PF, @T -> @Int) effects(pure) { apply_fn(@PF.0, 1) }"),
    "parameter-base-beside-T": (
        "fn(String, T -> Int) effects(pure)", "fn(Int, T -> Int) effects(pure)",
        "fn(@String, @T -> @Int) effects(pure) { 0 }"),
    "same-beside-T": (
        "fn(Int, T -> Int) effects(pure)", "fn(Int, T -> Int) effects(pure)",
        "fn(@Int, @T -> @Int) effects(pure) { @Int.0 }"),
}

POSITIONS = (
    "exn-clause", "state-clause", "binder-top", "binder-some", "binder-tuple",
    "binder-ctor", "binder-nested", "binder-whole", "argument", "component",
    "element", "adopted")

_SITE_CODE = {
    "exn-clause": "E342", "state-clause": "E342", "binder-top": "E314",
    "binder-some": "E314", "binder-tuple": "E314", "binder-ctor": "E314",
    "binder-nested": "E314", "binder-whole": "E314", "argument": "E202",
    "component": "E170", "element": "E170", "adopted": "E170"}

_PRELUDE = (
    "type PF = fn(Int -> Int) effects(pure);\n"
    "private data Box<Z> {\n  Box(Z)\n}\n\n"
    + _fn("none_of(@Unit -> @Option<X>)", "None").replace(
        "private fn", "private forall<X> fn")
    + _fn("idt(@Y -> @Y)", "@Y.0").replace("private fn", "private forall<Y> fn"))


def _skipped(position: str, mismatch: str, generic: bool) -> str | None:
    """Why a cell has no program, or None."""
    if (mismatch == "rigid" or mismatch.endswith("-beside-T")) and not generic:
        return "a rigid variable is the enclosing generic's"
    if mismatch == "open" and position in ("exn-clause", "state-clause"):
        return "a handled effect's type argument is written"
    if mismatch == "open" and position == "binder-whole":
        return "the whole-type binder writes `Option<WW>`, the open one's own"
    return None


def cell_program(position: str, mismatch: str, generic: bool) -> str:
    value_ty, written, value = MISMATCHES[mismatch]
    aliases = ""
    if value_ty not in ("T", "?"):
        aliases += f"type VV = {value_ty};\n"
    aliases += f"type WW = {written};\n"
    # The value, bound once where its type can be written.
    if value_ty in ("T", "?"):
        bind, v, vt = "", value, value_ty
    else:
        bind, v, vt = f"let @VV = {value};\n  ", "@VV.0", "VV"
    t_arg = "@T.0" if generic else "1"
    t_ty = "T" if generic else "Int"
    helpers = ""
    if position == "exn-clause":
        body = (f"handle[Exn<{vt}>] {{\n    throw(@WW) -> {{ 0 }}\n"
                f"  }} in {{\n    throw({v})\n  }}")
    elif position == "state-clause":
        body = (f"handle[State<{vt}>](@{vt} = {v}) {{\n"
                f"    get(@Unit) -> {{ resume(@{vt}.0) }},\n"
                f"    put(@WW) -> {{ resume(()) }}\n"
                f"  }} in {{\n    put({v});\n    0\n  }}")
    elif position == "binder-top":
        body = f"match {v} {{\n    @WW -> 0\n  }}"
    elif position == "binder-some":
        body = f"match Some({v}) {{\n    Some(@WW) -> 0,\n    None -> 1\n  }}"
    elif position == "binder-tuple":
        body = f"match Tuple({v}, 1) {{\n    Tuple(@WW, @Int) -> 0\n  }}"
    elif position == "binder-ctor":
        body = f"match Box({v}) {{\n    Box(@WW) -> 0\n  }}"
    elif position == "binder-nested":
        body = (f"match Some(Some({v})) {{\n    Some(Some(@WW)) -> 0,\n"
                f"    _ -> 1\n  }}")
    elif position == "binder-whole":
        body = f"match Some({v}) {{\n    @Option<WW> -> 0\n  }}"
    elif position == "argument":
        sig = ("take(@Tuple<WW, U> -> @Int)")
        helpers = _fn(sig, "0").replace("private fn", "private forall<U> fn")
        body = f"take(Tuple({v}, {t_arg}))"
    elif position == "component":
        body = f"let Tuple<@WW, @{t_ty}> = Tuple({v}, {t_arg});\n  0"
    elif position == "element":
        body = (f"let @Array<Tuple<WW, {t_ty}>> = [Tuple({v}, {t_arg})];\n  0")
    elif position == "adopted":
        body = (f"let @Tuple<WW, Option<Int>> = idt(Tuple({v}, none_of(())));\n  0")
    else:
        raise AssertionError(position)
    if mismatch.endswith("-beside-T"):
        # The aliases take the variable: `VV<T>` in the body, `WW<U>` in the
        # generic helper whose own variable it is.
        aliases = re.sub(r"type (VV|WW) =", r"type \1<T> =", aliases)
        body = re.sub(r"\b(VV|WW)\b", r"\1<T>", body)
        helpers = re.sub(r"\bWW\b", "WW<U>", helpers)
        bind = re.sub(r"\bVV\b", "VV<T>", bind)
    body = bind + body
    if generic:
        outer = _fn("outer(@T -> @Int)", body).replace(
            "private fn", "private forall<T> fn")
        main = _fn("main(@Unit -> @Int)", "outer(3)", visibility="public")
    else:
        outer = ""
        main = _fn("main(@Unit -> @Int)", body, visibility="public")
    return aliases + _PRELUDE + helpers + outer + main


def expected_codes(position: str, mismatch: str) -> list[str]:
    if mismatch in ("same", "open", "scalar-nat", "same-beside-T"):
        return []
    if mismatch == "narrowing":
        return ["E190"]
    return [_SITE_CODE[position]]


CELLS = [
    pytest.param(position, mismatch, generic,
                 id=f"{position}-{mismatch}-{'generic' if generic else 'plain'}")
    for position in POSITIONS for mismatch in MISMATCHES
    for generic in (False, True)
    if _skipped(position, mismatch, generic) is None]


@pytest.mark.parametrize(("position", "mismatch", "generic"), CELLS)
def test_every_binding_position_holds_its_value_to_is_subtype(
        position: str, mismatch: str, generic: bool) -> None:
    source = cell_program(position, mismatch, generic)
    assert _codes(source) == expected_codes(position, mismatch), source


# =====================================================================
# A head over the enclosing function's own bare type variable
# =====================================================================

#: (the arm's pattern, a type variable's own or an open one): refused only
#: over the function's own variable.
HEADS = {
    "option": "Some(@Int) -> 1",
    "nullary": "None -> 1",
    "tuple": "Tuple(@Int, @Int) -> 1",
    "ctor": "Box(@Int) -> 1",
    "int-literal": "5 -> 1",
    "string-literal": '"x" -> 1',
    "bool-literal": "true -> 1",
}


@pytest.mark.parametrize("head", sorted(HEADS))
def test_a_head_over_the_function_s_own_type_variable_is_refused(
        head: str) -> None:
    body = f"match @A.0 {{\n    {HEADS[head]},\n    _ -> 0\n  }}"
    source = (_PRELUDE + _fn("run(@A -> @Int)", body).replace(
        "private fn", "private forall<A> fn")
        + _fn("main(@Unit -> @Int)", "run(Some(1))", visibility="public"))
    assert _codes(source) == ["E314"], source


@pytest.mark.parametrize("head", ["option", "nullary"])
def test_a_head_over_an_open_variable_stays_accepted(head: str) -> None:
    """A variable a call left open: the scrutinee is an `Option` whatever
    fixes it, and the binder under the head reads it as unknown."""
    source = _PRELUDE + _fn(
        "main(@Unit -> @Int)",
        f"match idt(none_of(())) {{\n    {HEADS[head]},\n    _ -> 0\n  }}",
        visibility="public")
    assert _codes(source) == [], source


def test_a_head_over_a_bare_open_variable_reads_its_fields_as_unknown(
        ) -> None:
    """`first([])` leaves its result a bare open variable: the head decides
    nothing, and `Some`'s field, whose own parameter is named `T` like the
    enclosing function's, is read as unknown, not as that `T`."""
    source = _fn("run(@T -> @Int)",
                 "match first_of([]) {\n    Some(@Int) -> @Int.0,\n    _ -> 0\n  }"
                 ).replace("private fn", "private forall<T> fn") + _fn(
        "first_of(@Array<X> -> @X)", "@Array<X>.0[0]").replace(
        "private fn", "private forall<X> fn").replace(
        "requires(true)", "requires(array_length(@Array<X>.0) > 0)")
    assert "E314" not in _codes(source), source


# =====================================================================
# The slot a clause parameter binds has the type the clause writes
# =====================================================================

def test_a_narrower_clause_binder_is_guarded_once_1896() -> None:
    """`throw(@Nat)` under `Exn<Int>` binds a `Nat`: the bind is the one
    narrowing, so the clause's `@Nat.0` returned at `-> @Nat` is no second
    `nat_bind` (it was one at the function's return when the slot held the
    operation's `Int`)."""
    source = _fn("go(@Int -> @Nat)",
                 "handle[Exn<Int>] {\n    throw(@Nat) -> { @Nat.0 }\n"
                 "  } in {\n    throw(@Int.0)\n  }", visibility="public")
    verified = pipeline.verify(source, reconcile=True)
    kinds = [o.kind for o in verified.result.obligations]
    assert kinds.count("nat_bind") == 1, kinds


# =====================================================================
# A built-in's variable a failed substitution lost (#1688)
# =====================================================================

_LOST = (
    "type P = fn(Int -> Int) effects(pure);\n"
    "type I = fn(Int -> Int) effects(<IO>);\n"
    "type F = fn(I -> Int) effects(pure);\n\n"
    + _fn("first(@Array<T> -> @T)", "@Array<T>.0[0]").replace(
        "private fn", "private forall<T> fn").replace(
        "requires(true)", "requires(array_length(@Array<T>.0) > 0)")
    + _fn("idt(@A -> @A)", "@A.0").replace("private fn", "private forall<A> fn")
    + _fn("take(@Tuple<Int, F> -> @Int)", "0"))
_LOST_VALUE = ("Tuple(array_map([1], first([]))[0], "
               "fn(@P -> @Int) effects(pure) { apply_fn(@P.0, 1) })")


@pytest.mark.parametrize(("form", "code"), [
    ("argument", "E202"), ("element", "E170"), ("adopted", "E170")])
def test_a_lost_variable_beside_a_parameter_row_the_wrong_way_round(
        form: str, code: str) -> None:
    """The lost variable is read as unknown, and the `fn(P -> Int)` beside
    it is held to `fn(I -> Int)` by `is_subtype`: refused, where the
    either-way reading passed it to a function code generation then
    skipped (E602)."""
    body = {
        "argument": f"take({_LOST_VALUE})",
        "element": f"let @Array<Tuple<Int, F>> = [{_LOST_VALUE}];\n  0",
        "adopted": f"let @Tuple<Int, F> = idt({_LOST_VALUE});\n  0",
    }[form]
    source = _LOST + _fn("outer(@Unit -> @Int)", body)
    assert _codes(source) == [code], source


# =====================================================================
# One type for an open variable met twice: the narrower one fits both
# =====================================================================

_TWIN = (
    "type W = fn(Int -> Int) effects(pure);\n"
    "type IOF = fn(Int -> Int) effects(<IO>);\n\n"
    + _fn("twin(@Unit -> @Tuple<Option<X>, Option<X>>)", "Tuple(None, None)"
          ).replace("private fn", "private forall<X> fn")
    + _fn("take(@Tuple<Option<W>, Option<IOF>> -> @Int)", "0")
    + _fn("idt(@A -> @A)", "@A.0").replace("private fn", "private forall<A> fn"))


@pytest.mark.parametrize("body", [
    "take(twin(()))", "take(idt(twin(())))",
    "let @Tuple<Option<W>, Option<IOF>> = twin(());\n  0",
    "let @Tuple<Option<W>, Option<IOF>> = idt(twin(()));\n  0",
    "let Tuple<@Option<W>, @Option<IOF>> = twin(());\n  0"],
    ids=["argument", "argument-through-idt", "let", "let-through-idt",
         "destructure"])
def test_an_open_variable_met_twice_fits_at_the_narrower_type(
        body: str) -> None:
    """`twin(())`'s one `X` meets `W` and `IOF`, a pure function type and
    the same under `<IO>`: `X = W` gives both positions their types, so the
    value fits.  The join binds `X` to the two types' join, the wider
    `IOF`; with that binding substituted the fit was refused, at every
    position, where it is accepted at main."""
    source = _TWIN + _fn("main(@Unit -> @Int)", body, visibility="public")
    assert _codes(source) == [], source
