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


#: `mk(())` leaves `X` open inside a function type: the closure is compiled
#: at a type of its own, which the binder's `Int` does not fix.
_OPEN_IN_FN = (
    "type II = fn(Int -> Int) effects(pure);\n\n"
    + _fn("mk(@Unit -> @Option<fn(X -> Int) effects(pure)>)",
          "Some(fn(@X -> @Int) effects(pure) { 40 })").replace(
              "private fn", "private forall<X> fn"))


def test_repro_a_binder_over_an_open_variable_inside_a_function_type_1896(
        ) -> None:
    """Was accepted, verified clean, and trapped `indirect call type
    mismatch`: an open variable inside a function type was read as unknown,
    so `fn(X -> Int)` held at `fn(Int -> Int)`.  The matrix's `open-in-*`
    shapes hold every position and shape of it."""
    source = _OPEN_IN_FN + _fn(
        "main(@Unit -> @Int)",
        "match mk(()) {\n    Some(@II) -> apply_fn(@II.0, 3),\n    None -> 7\n  }",
        visibility="public")
    (error,) = pipeline.check(source).errors
    assert error.error_code == "E314", source
    # The variable the call left open is shown as `?`, not by its own name.
    assert error.description.endswith(
        "but the scrutinee has type fn(? -> Int) effects(pure)."), error.description


_CALLBACK = (
    "private data Callback<A> {\n  MkCb(fn(A -> Int) effects(pure))\n}\n\n"
    "type CI = fn(Int -> Int) effects(pure);\n\n"
    + _fn("mk(@Unit -> @Callback<X>)",
          "MkCb(fn(@X -> @Int) effects(pure) { 40 })").replace(
              "private fn", "private forall<X> fn")
    + _fn("main(@Unit -> @Int)",
          "match Some(mk(())) {\n    Some(@Callback<Int>) -> match "
          "@Callback<Int>.0 {\n      MkCb(@CI) -> apply_fn(@CI.0, 3)\n    },\n"
          "    None -> 7\n  }", visibility="public"))


def test_repro_a_binder_over_a_data_type_holding_behaviour_open_1896(
        ) -> None:
    """Was accepted, verified clean, and trapped at the indirect call: the
    variable `mk(())` left open in `Callback<X>`, a parameter a constructor
    field holds inside a function type, was read as unknown, so the value
    held at `Callback<Int>`."""
    (error,) = pipeline.check(_CALLBACK).errors
    assert error.error_code == "E314", _CALLBACK
    assert error.description.endswith(
        "but the scrutinee has type Callback<?>."), error.description


def test_a_nested_match_leaves_the_outer_scrutinee_to_a_later_arm() -> None:
    """The fix names the scrutinee of the `match` whose arm it is in: an
    arm's body holding a `match` of its own leaves the outer one's for the
    arms after it."""
    source = _OPEN_IN_FN + _fn(
        "main(@Int -> @Int)",
        "match mk(()) {\n    None -> match @Int.0 {\n      _ -> 1\n    },\n"
        "    Some(@II) -> apply_fn(@II.0, 3)\n  }", visibility="public")
    (error,) = pipeline.check(source).errors
    assert "`let @Instance = mk(());`" in error.fix, error.fix


def test_the_fix_s_alias_takes_a_name_nothing_declares() -> None:
    source = ("type Instance = Int;\n\n" + _OPEN_IN_FN + _fn(
        "main(@Unit -> @Int)",
        "match mk(()) {\n    Some(@II) -> apply_fn(@II.0, 3),\n    None -> 7\n  }",
        visibility="public"))
    (error,) = pipeline.check(source).errors
    assert "`type Instance2 = Option<fn(Int -> Int) effects(pure)>;`" in (
        error.fix), error.fix


def test_the_fix_s_alias_passes_over_a_data_type_of_its_name() -> None:
    source = ("private data Instance {\n  Inst\n}\n\n" + _OPEN_IN_FN + _fn(
        "main(@Unit -> @Int)",
        "match mk(()) {\n    Some(@II) -> apply_fn(@II.0, 3),\n    None -> 7\n  }",
        visibility="public"))
    (error,) = pipeline.check(source).errors
    assert "`type Instance2 = " in error.fix, error.fix


def test_a_refinement_of_a_data_type_holding_behaviour_open_is_refused(
        ) -> None:
    """The reading goes through a refinement to the data type under it."""
    source = (
        "type CR = { @Cb<Int> | true };\n" + _PRELUDE + _OPEN_PRODUCERS
        + _fn("mk_cr(@Unit -> @{ @Cb<X> | true })", f"MkCb({_FX})").replace(
            "private fn", _G)
        + _fn("main(@Unit -> @Int)",
              "match Some(mk_cr(())) {\n    Some(@CR) -> 0,\n    None -> 1\n  }",
              visibility="public"))
    assert _codes(source) == ["E314"], source


def test_an_open_variable_inside_a_function_type_its_context_fixes_runs(
        ) -> None:
    """Where the context fixes the variable (a `let`'s type, a parameter's),
    the call is instantiated there, and the closure runs at that type."""
    for body in ("let @Option<II> = mk(());\n  match @Option<II>.0 {\n"
                 "    Some(@II) -> apply_fn(@II.0, 3),\n    None -> 7\n  }",):
        source = _OPEN_IN_FN + _fn("main(@Unit -> @Int)", body,
                                   visibility="public")
        assert _codes(source) == [], source
        ran = pipeline.run(source, fn="main")
        assert ran.trap is None and ran.value == 40, (ran.trap, source)


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
    # A variable a generic call leaves open INSIDE a function type, which
    # no context fixes once the call is typed: the function was compiled at
    # a type of its own, so it is no function of the written type (the
    # binder at `fn(Int -> Int)` over `fn(X -> Int)` trapped `indirect call
    # type mismatch`).  The producers are `_OPEN_PRODUCERS`.
    "open-in-parameter": ("?", "fn(Int -> Int) effects(pure)", "mk_par(())"),
    "open-in-result": ("?", "fn(Int -> Int) effects(pure)", "mk_res([])"),
    "open-in-both": ("?", "fn(Int -> Int) effects(pure)", "mk_both(())"),
    "open-in-one-of-two": ("?", "fn(Int, Int -> Int) effects(pure)",
                                "mk_two(())"),
    "open-under-data": ("?", "fn(Option<Int> -> Int) effects(pure)",
                        "mk_data(())"),
    "open-in-nested": (
        "?", "fn(fn(Int -> Int) effects(pure) -> Int) effects(pure)",
        "mk_nested(())"),
    "open-in-row": ("?", "fn(Int -> Int) effects(<Exn<Int>>)", "mk_row(())"),
    # The same variable at a data type's parameter that a constructor field
    # holds inside a function type (`_behaviour_params`): the data type
    # carries compiled behaviour over it, as a function type does.
    "open-in-data-field": ("?", "Cb<Int>", "mk_cb(())"),
    "open-in-data-option-field": ("?", "Ho<Int>", "mk_ho(())"),
    "open-in-data-array-field": ("?", "Ar<Int>", "mk_ar(())"),
    "open-in-data-tuple-field": ("?", "Tu<Int>", "mk_tu(())"),
    "open-in-data-two-levels": ("?", "Wr<Int>", "mk_wr(())"),
    "open-in-data-recursive": ("?", "Ls<Int>", "mk_ls(())"),
    "open-in-data-plain-and-function": ("?", "Pr<Int>", "mk_pr(None)"),
    "open-in-data-alias": ("?", "CbA<Int>", "mk_al(())"),
    "open-in-data-behaviour-parameter": ("?", "Two<Int, Int>", "mk_bp(Some(1))"),
    # Its plain parameter open beside a closed behaviour parameter: an
    # ordinary open container, accepted wherever it stands.
    "open-in-data-plain-parameter": ("?", "Two<Int, Int>", "mk_tp(None)"),
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

_G = "private forall<X> fn"
_FX = "fn(@X -> @Int) effects(pure) { 40 }"

#: Each shape's generic producer: its result holds `X` inside a function
#: type, and `mk(())` (`mk_res([])`) leaves `X` open.
_OPEN_PRODUCERS = (
    "type GX<X> = fn(X -> Int) effects(pure);\n"
    + _fn("mk_par(@Unit -> @fn(X -> Int) effects(pure))",
          "fn(@X -> @Int) effects(pure) { 40 }").replace("private fn", _G)
    + _fn("mk_res(@Array<X> -> @fn(Int -> X) effects(pure))",
          "fn(@Int -> @X) effects(pure) { @Array<X>.0[0] }").replace(
              "private fn", _G)
    + _fn("mk_two(@Unit -> @fn(X, Int -> Int) effects(pure))",
          "fn(@X, @Int -> @Int) effects(pure) { 40 }").replace("private fn", _G)
    + _fn("mk_both(@Unit -> @fn(X -> X) effects(pure))",
          "fn(@X -> @X) effects(pure) { @X.0 }").replace("private fn", _G)
    + _fn("mk_data(@Unit -> @fn(Option<X> -> Int) effects(pure))",
          "fn(@Option<X> -> @Int) effects(pure) { 40 }").replace(
              "private fn", _G)
    + _fn("mk_nested(@Unit -> @fn(GX<X> -> Int) effects(pure))",
          "fn(@GX<X> -> @Int) effects(pure) { 40 }").replace("private fn", _G)
    + _fn("mk_row(@Unit -> @fn(Int -> Int) effects(<Exn<X>>))",
          "fn(@Int -> @Int) effects(<Exn<X>>) { 40 }").replace(
              "private fn", _G)
    + "private data Cb<A> {\n  MkCb(fn(A -> Int) effects(pure))\n}\n\n"
    "private data Ho<A> {\n  MkHo(Option<fn(A -> Int) effects(pure)>)\n}\n\n"
    "private data Ar<A> {\n  MkAr(Array<fn(A -> Int) effects(pure)>)\n}\n\n"
    "private data Tu<A> {\n  MkTu(Tuple<Int, fn(A -> Int) effects(pure)>)\n}\n\n"
    "private data Wr<A> {\n  MkWr(Cb<A>)\n}\n\n"
    "private data Ls<A> {\n  Nil,\n  Cons(fn(A -> Int) effects(pure), Ls<A>)\n}\n\n"
    "private data Pr<A> {\n  MkPr(Option<A>, fn(A -> Int) effects(pure))\n}\n\n"
    "private data Two<A, B> {\n  MkTwo(Option<A>, fn(B -> Int) effects(pure))\n}\n\n"
    "type CbA<A> = Cb<A>;\n\n"
    + "".join(
        _fn(sig, body).replace("private fn", _G) for sig, body in (
            ("mk_cb(@Unit -> @Cb<X>)", f"MkCb({_FX})"),
            ("mk_ho(@Unit -> @Ho<X>)", f"MkHo(Some({_FX}))"),
            ("mk_ar(@Unit -> @Ar<X>)", f"MkAr([{_FX}])"),
            ("mk_tu(@Unit -> @Tu<X>)", f"MkTu(Tuple(1, {_FX}))"),
            ("mk_wr(@Unit -> @Wr<X>)", f"MkWr(MkCb({_FX}))"),
            ("mk_ls(@Unit -> @Ls<X>)", f"Cons({_FX}, Nil)"),
            ("mk_pr(@Option<X> -> @Pr<X>)", f"MkPr(@Option<X>.0, {_FX})"),
            ("mk_al(@Unit -> @CbA<X>)", f"MkCb({_FX})"),
            ("mk_tp(@Option<X> -> @Two<X, Int>)",
             "MkTwo(@Option<X>.0, fn(@Int -> @Int) effects(pure) { 40 })")))
    + _fn("mk_bp(@Option<X> -> @Two<X, Y>)",
          "MkTwo(@Option<X>.0, fn(@Y -> @Int) effects(pure) { 40 })").replace(
              "private fn", "private forall<X, Y> fn"))

_OPEN_SHAPES = frozenset(m for m in MISMATCHES
                         if m.startswith(("open-in-", "open-under-")))


def _skipped(position: str, mismatch: str, generic: bool) -> str | None:
    """Why a cell has no program, or None."""
    if (mismatch == "rigid" or mismatch.endswith("-beside-T")) and not generic:
        return "a rigid variable is the enclosing generic's"
    if (mismatch == "open" or mismatch in _OPEN_SHAPES) and position in (
            "exn-clause", "state-clause"):
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
    prelude = _PRELUDE + (_OPEN_PRODUCERS if mismatch in _OPEN_SHAPES
                          else "")
    return aliases + prelude + helpers + outer + main


def expected_codes(position: str, mismatch: str) -> list[str]:
    if mismatch in ("same", "open", "scalar-nat", "same-beside-T"):
        return []
    if mismatch in _OPEN_SHAPES:
        return _open_shape_codes(position, mismatch)
    if mismatch == "narrowing":
        return ["E190"]
    return [_SITE_CODE[position]]


def _open_shape_codes(position: str, mismatch: str) -> list[str]:
    """A binder under a head, or at the scrutinee's root, holds the value at
    a type its function was not compiled for: E314.  Where the written type
    reaches the call as its expected type (an argument, a whole-type binder
    over `Some(...)`), the call is instantiated there and the program runs
    at that type: no refusal.  The join's positions refuse the pair, as on
    `main`: a variable inside a function type is not open at the join
    (#1684), and an effect row holding one is compared as written.  A data
    type's behaviour parameter reads as a function type does; its plain
    parameter, beside a closed behaviour one, is an ordinary open container
    and is accepted everywhere."""
    if mismatch == "open-in-data-plain-parameter":
        return []
    row = mismatch == "open-in-row"
    if position.startswith("binder-") and position != "binder-whole":
        return ["E314"]
    if position == "binder-whole":
        return ["E314"] if row else []
    if position == "argument":
        return ["E202"] if row else []
    if position == "adopted":
        return ["E170"] if row else ["E170", "E202"]
    return ["E170"]


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

#: Each head's E314 says what the pattern matches, as its own kind of
#: pattern does (`_rigid_head_mismatch`).
HEAD_SAYS = {
    "option": "Pattern 'Some' is a constructor of Option<T>",
    "nullary": "Pattern 'None' is a constructor of Option<T>",
    "tuple": "Pattern 'Tuple(...)' matches a tuple",
    "ctor": "Pattern 'Box' is a constructor of Box<Z>",
    "int-literal": "Pattern literal 5 has type Int",
    "string-literal": 'Pattern literal "x" has type String',
    "bool-literal": "Pattern literal true has type Bool",
}


@pytest.mark.parametrize("head", sorted(HEADS))
def test_a_head_over_the_function_s_own_variable_says_what_it_matches(
        head: str) -> None:
    body = f"match @A.0 {{\n    {HEADS[head]},\n    _ -> 0\n  }}"
    source = _PRELUDE + _fn("run(@A -> @Int)", body).replace(
        "private fn", "private forall<A> fn")
    (error,) = pipeline.check(source).errors
    assert error.description == (
        f"{HEAD_SAYS[head]}, but the scrutinee has type A."), error.description
    assert error.rationale.startswith(
        "A is a type parameter of the enclosing function"), error.rationale


def test_repro_a_refused_head_over_a_t_reads_its_fields_as_unknown_1896(
        ) -> None:
    """`Option`'s own parameter is named `T`, as the enclosing function's
    is: once the head is refused, its field is read as unknown, not as the
    function's `T`, so the binder under it draws no second E314."""
    source = _fn("run(@T -> @Int)",
                 "match @T.0 {\n    Some(@Int) -> @Int.0,\n    _ -> 0\n  }"
                 ).replace("private fn", "private forall<T> fn")
    assert _codes(source) == ["E314"], source


#: (the program's function, the reason the rationale gives): each of the
#: binder's three reasons (`_binder_mismatch`), the type parameter's from
#: either side and from inside a function type's parameters.
_BINDER_REASONS = {
    "variable-in-value": (
        _fn("run(@Tuple<T, Int> -> @Int)",
            "match @Tuple<T, Int>.0 {\n    @Tuple<Int, Int> -> 0\n  }"
            ).replace("private fn", "private forall<T> fn"),
        "A type parameter of the enclosing function"),
    "variable-in-binder": (
        _fn("run(@Option<Int> -> @Int)",
            "match @Option<Int>.0 {\n    @Option<T> -> 0\n  }"
            ).replace("private fn", "private forall<T> fn"),
        "A type parameter of the enclosing function"),
    "variable-in-a-parameter": (
        "type FT<T> = fn(T, Int -> Int) effects(pure);\n"
        "type FI = fn(Int, Int -> Int) effects(pure);\n\n"
        + _fn("run(@FT<T> -> @Int)", "match @FT<T>.0 {\n    @FI -> 0\n  }"
              ).replace("private fn", "private forall<T> fn"),
        "A type parameter of the enclosing function"),
    "the-other-way-function": (
        "type W = fn(Int -> Int) effects(pure);\n"
        "type IOF = fn(Int -> Int) effects(<IO>);\n\n"
        + _fn("run(@IOF -> @Int)", "match @IOF.0 {\n    @W -> 0\n  }"),
        "A binder claims every value it binds has the type it writes"),
    "the-other-way-never": (
        _fn("run(@Int -> @Int)", "match @Int.0 {\n    @Never -> 0\n  }"),
        "A binder claims every value it binds has the type it writes"),
    "unrelated": (
        _fn("run(@String -> @Int)", "match @String.0 {\n    @Int -> 0\n  }"),
        "Every value reaching a match arm has the scrutinee's type"),
}


@pytest.mark.parametrize("case", sorted(_BINDER_REASONS))
def test_a_refused_binder_gives_the_reason_that_holds(case: str) -> None:
    source, reason = _BINDER_REASONS[case]
    (error,) = pipeline.check(source).errors
    assert error.error_code == "E314", source
    assert error.rationale.startswith(reason), error.rationale
    if case.startswith("the-other-way"):
        function = case.endswith("function")
        assert error.rationale.endswith(
            "does not declare)." if function else "can tell."), error.rationale


def test_a_binder_over_an_open_variable_shows_it_as_unknown() -> None:
    """The scrutinee's type is shown as the binder judged it: a variable the
    call left open is `?`, not the call's own name for it."""
    source = _PRELUDE + _fn(
        "run(@Int -> @Int)",
        "match Some(none_of(())) {\n    Some(@String) -> 0,\n    None -> 1\n  }")
    (error,) = pipeline.check(source).errors
    assert error.description.endswith(
        "but the scrutinee has type Option<?>."), error.description


def test_a_clause_parameter_at_an_undeclared_type_binds_the_operation_s(
        ) -> None:
    """Where the written type names nothing (E136), the slot takes the
    operation's type, so the body is still checked against it."""
    source = _fn("go(@Int -> @Int)",
                 "handle[Exn<Int>] {\n    throw(@Foo) -> { string_length(@Foo.0) }\n"
                 "  } in {\n    throw(@Int.0)\n  }")
    assert _codes(source) == ["E136", "E202"], source


def test_a_match_arm_beside_a_lost_variable_is_judged_both_ways_round(
        ) -> None:
    """`_branches_agree` asks of two arms side by side, the earlier arm's
    holding a built-in's lost variable (#1688): a function value narrower
    than its neighbour's in either arm draws E302 there, not a join at the
    later arm's type."""
    source = (
        "type FI = fn(Int -> Int) effects(pure);\n\n"
        + _fn("first(@Array<T> -> @T)", "@Array<T>.0[0]").replace(
            "private fn", "private forall<T> fn").replace(
            "requires(true)", "requires(array_length(@Array<T>.0) > 0)")
        + _fn("main(@Int -> @Int)",
              "let @Tuple<Int, FI> = match @Int.0 {\n"
              "    0 -> Tuple(array_map([1], first([]))[0], "
              "fn(@Nat -> @Int) effects(pure) { 1 }),\n"
              "    _ -> Tuple(0, fn(@Int -> @Int) effects(pure) { 2 })\n  };\n  0",
              visibility="public"))
    assert _codes(source) == ["E190", "E302"], source


_SPAN = re.compile(r"`([^`]+)`")


@pytest.mark.parametrize(("position", "shape", "generic"), [
    pytest.param(position, shape, generic,
                 id=f"{position}-{shape}-{'generic' if generic else 'plain'}")
    for position in ("binder-top", "binder-some", "binder-tuple",
                     "binder-ctor", "binder-nested")
    for shape in sorted(_OPEN_SHAPES - {"open-in-row", "open-in-data-plain-parameter"})
    for generic in (False, True)])
def test_the_open_variable_fix_applied_as_written_clears_e314(
        position: str, shape: str, generic: bool) -> None:
    """E314's fix over a function type a call left open declares the
    instantiated type, binds the scrutinee with a `let` at it, and matches
    its slot: applied as written, at every binder position and shape."""
    source = cell_program(position, shape, generic)
    (error,) = pipeline.check(source).errors
    given = _SPAN.findall(error.fix)
    alias = next(g for g in given if g.startswith("type "))
    let = next(g for g in given if g.startswith("let "))
    slot = next(g for g in given if g.startswith("@"))
    scrutinee = let.split(" = ", 1)[1].rstrip(";")
    site = f"match {scrutinee} {{"
    assert source.count(site) == 1, (site, source)
    fixed = alias + "\n\n" + source.replace(site, f"{let}\n  match {slot} {{")
    assert _codes(fixed) == [], (error.fix, fixed)


#: (the `match`, whether the fix writes the `let`): a binder whose pair
#: binds each open variable to one type gets the `let` that fixes them; a
#: variable met at two types, a data type other than the value's, or a
#: variable the binder does not reach leaves no type to write, and the
#: fix says what to do in prose.
_OPEN_FIX_FORMS = {
    "a-variable-at-two-types": (
        "match Some(mk_both(())) {\n    Some(@IS) -> 0,\n    None -> 1\n  }",
        False),
    "another-data-type": (
        "match Some(Some(mk_par(()))) {\n    Some(@Box<WW>) -> 0,\n    _ -> 1\n  }",
        False),
    "another-open-variable": (
        "match Tuple(none_of(()), mk_par(())) {\n    Tuple(_, @WW) -> 0\n  }",
        False),
}


@pytest.mark.parametrize("form", sorted(_OPEN_FIX_FORMS))
def test_the_open_variable_fix_writes_a_let_only_where_one_type_fixes_it(
        form: str) -> None:
    body, writes = _OPEN_FIX_FORMS[form]
    source = ("type WW = fn(Int -> Int) effects(pure);\n"
              "type IS = fn(Int -> String) effects(pure);\n"
              + _PRELUDE + _OPEN_PRODUCERS
              + _fn("main(@Unit -> @Int)", body, visibility="public"))
    (error,) = pipeline.check(source).errors
    assert error.error_code == "E314", source
    assert error.fix.startswith("The scrutinee holds a function whose"), error.fix
    assert ("`type Instance = " in error.fix) is writes, error.fix
    if writes:
        given = _SPAN.findall(error.fix)
        alias, let, slot = (next(g for g in given if g.startswith(s))
                            for s in ("type ", "let ", "@"))
        scrutinee = let.split(" = ", 1)[1].rstrip(";")
        fixed = alias + "\n\n" + source.replace(
            f"match {scrutinee} {{", f"{let}\n  match {slot} {{")
        assert _codes(fixed) == [], fixed


#: A function value in each arm beside a built-in's lost variable (#1688):
#: (the first arm's, the second's) -> whether the arms are refused (E301 at
#: an `if` whose branches lose two variables, E302 at a `match` whose first
#: arm loses one).  `_branches_agree` asks the symmetric question: a
#: narrower parameter, or a row the first arm's type would drop, either way.
_SIBLING_FNS = {
    "nat": "fn(@Nat -> @Int) effects(pure) { 1 }",
    "int": "fn(@Int -> @Int) effects(pure) { 2 }",
    "io": 'fn(@Int -> @Int) effects(<IO>) { IO.print("x"); 3 }',
}
_SIBLINGS = {
    ("if", "int", "int"): False, ("if", "nat", "int"): False,
    ("if", "int", "nat"): True, ("if", "io", "int"): False,
    ("if", "int", "io"): True,
    ("match", "int", "int"): False, ("match", "int", "nat"): False,
    ("match", "nat", "int"): True, ("match", "io", "int"): True,
    ("match", "int", "io"): False,
}


@pytest.mark.parametrize(("form", "first", "second"), sorted(_SIBLINGS))
def test_arms_beside_a_lost_variable_are_compared_side_by_side(
        form: str, first: str, second: str) -> None:
    lost = "array_map([1], first_of([]))[0]"
    a = f"Tuple({lost}, {_SIBLING_FNS[first]})"
    if form == "if":
        b = f"Tuple(map_values(first_of([]))[0], {_SIBLING_FNS[second]})"
        join = f"if @Int.0 > 0 then {{ {a} }} else {{ {b} }}"
    else:
        b = f"Tuple(0, {_SIBLING_FNS[second]})"
        join = f"match @Int.0 {{\n    0 -> {a},\n    _ -> {b}\n  }}"
    source = (_fn("first_of(@Array<X> -> @X)", "@Array<X>.0[0]").replace(
        "private fn", "private forall<X> fn").replace(
        "requires(true)", "requires(array_length(@Array<X>.0) > 0)")
        + _fn("main(@Int -> @Int)", f"let @Tuple<Int, Int> = {join};\n  0",
              visibility="public", contract=_IO_CONTRACT))
    refusal = "E301" if form == "if" else "E302"
    assert (refusal in _codes(source)) is _SIBLINGS[(form, first, second)], source


#: E314's two fix texts over a function a call left open, whole.
_PROSE_FIX = (
    "The scrutinee holds a function whose type variable the call leaves "
    "open, which no binder can name: fix the variable first, binding the "
    "scrutinee with a `let` at the type this binder needs, named by a type "
    "alias, so the call is instantiated at it, and match the `let`'s slot.")


def _concrete_fix(name: str, written: str, scrutinee: str) -> str:
    return ("The scrutinee holds a function whose type variable the call "
            "leaves open, which no binder can name: fix the variable first, "
            "so the call is instantiated at the type this binder needs.  "
            f"Declare `type {name} = {written};`, bind the scrutinee before "
            f"the `match` with `let @{name} = {scrutinee};`, and match "
            f"`@{name}.0`.")


def _open_fix(body: str, *, before: str = "", generic: bool = False) -> str:
    fn = _fn("run(@T -> @Int)" if generic else "main(@Unit -> @Int)", body)
    if generic:
        fn = fn.replace("private fn", "private forall<T> fn")
    source = ("type WW = fn(Int -> Int) effects(pure);\n"
              "type IS = fn(Int -> String) effects(pure);\n" + before
              + _PRELUDE + _OPEN_PRODUCERS + fn)
    (error,) = pipeline.check(source).errors
    assert error.error_code == "E314", source
    return error.fix


def test_the_open_variable_fix_whole_where_one_type_fixes_it() -> None:
    assert _open_fix(
        "match Some(mk_par(())) {\n    Some(@WW) -> 0,\n    None -> 1\n  }"
    ) == _concrete_fix("Instance", "Option<fn(Int -> Int) effects(pure)>",
                       "Some(mk_par(()))")


def test_the_open_variable_fix_whole_under_a_taken_name() -> None:
    assert _open_fix(
        "match Some(mk_par(())) {\n    Some(@WW) -> 0,\n    None -> 1\n  }",
        before="type Instance = Int;\n"
    ) == _concrete_fix("Instance2", "Option<fn(Int -> Int) effects(pure)>",
                       "Some(mk_par(()))")


def test_the_open_variable_fix_whole_over_the_function_s_own_variable(
        ) -> None:
    """A type holding the enclosing function's own `T` is an alias over
    `T`, which the slot passes on; applied as written, it clears E314."""
    fix = _open_fix("match Tuple(@T.0, mk_par(())) {\n    Tuple(@T, @WW) -> 0\n  }",
                    generic=True)
    assert fix == _concrete_fix(
        "Instance<T>", "Tuple<T, fn(Int -> Int) effects(pure)>",
        "Tuple(@T.0, mk_par(()))")


_OWN_VARIABLE_FORMS = {
    # `T` twice: the alias takes it once
    "twice": ("match Tuple(@T.0, Tuple(@T.0, mk_par(()))) {\n"
              "    Tuple(@T, Tuple(@T, @WW)) -> 0\n  }",
              "Tuple<T, Tuple<T, fn(Int -> Int) effects(pure)>>",
              "Tuple(@T.0, Tuple(@T.0, mk_par(())))"),
    # `T` only in a function's parameter, and only in its result
    "in-a-parameter": ("match Some(mk_tp2(@T.0)) {\n    Some(@FT<T>) -> 0,\n"
                       "    None -> 1\n  }",
                       "Option<fn(Int, T -> Int) effects(pure)>",
                       "Some(mk_tp2(@T.0))"),
    "in-a-result": ("match Some(mk_rt(@T.0)) {\n    Some(@FR<T>) -> 0,\n"
                    "    None -> 1\n  }",
                    "Option<fn(Int -> T) effects(pure)>", "Some(mk_rt(@T.0))"),
}


@pytest.mark.parametrize("form", sorted(_OWN_VARIABLE_FORMS))
def test_the_open_variable_fix_names_each_own_variable_once(form: str) -> None:
    body, written, scrutinee = _OWN_VARIABLE_FORMS[form]
    before = ("type FT<T> = fn(Int, T -> Int) effects(pure);\n"
              "type FR<T> = fn(Int -> T) effects(pure);\n"
              + _fn("mk_tp2(@Y -> @fn(X, Y -> Int) effects(pure))",
                    "fn(@X, @Y -> @Int) effects(pure) { 40 }").replace(
                        "private fn", "private forall<X, Y> fn")
              + _fn("mk_rt(@Y -> @fn(X -> Y) effects(pure))",
                    "fn(@X -> @Y) effects(pure) { @Y.0 }").replace(
                        "private fn", "private forall<X, Y> fn"))
    fix = _open_fix(body, before=before, generic=True)
    assert fix == _concrete_fix("Instance<T>", written, scrutinee), fix


@pytest.mark.parametrize("body", [
    # a variable at two types: no one type gives the binder's
    pytest.param("match Some(mk_both(())) {\n    Some(@IS) -> 0,\n    None -> 1\n  }",
                 id="two-types"),
    # another variable left open: the instantiated type has no written form
    pytest.param("match Tuple(none_of(()), mk_par(())) {\n    Tuple(_, @WW) -> 0\n  }",
                 id="no-written-form"),
    # the variable fixed, the binder still refused: its result differs
    pytest.param("match Some(mk_oi(())) {\n    Some(@WW) -> 0,\n    None -> 1\n  }",
                 id="a-misfit-beside-it"),
])
def test_the_open_variable_fix_whole_in_prose(body: str) -> None:
    before = _fn("mk_oi(@Unit -> @fn(X -> Option<Int>) effects(pure))",
                 "fn(@X -> @Option<Int>) effects(pure) { None }").replace(
                     "private fn", _G)
    assert _open_fix(body, before=before) == _PROSE_FIX


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


# =====================================================================
# A clause parameter's refusal, read whole (#1908's mutation lane)
# =====================================================================

_CLAUSE_FN_TYPES = (
    "type G = fn(Int -> Int) effects(pure);\n"
    "type F = fn(Int -> Nat) effects(pure);\n"
    "type IOF = fn(Int -> Int) effects(<IO>);\n\n")


def _clause_over(op_ty: str, written: str) -> str:
    """`go` throws a `G` closure under `Exn<op_ty>` and binds it at
    `written` in the clause."""
    return _CLAUSE_FN_TYPES + _fn(
        "go(@Int -> @Int)",
        f"let @{op_ty} = fn(@Int -> @Int) effects(pure) {{ @Int.0 }};\n"
        f"  handle[Exn<{op_ty}>] {{\n    throw(@{written}) -> {{ 0 }}\n"
        f"  }} in {{\n    throw(@{op_ty}.0)\n  }}", visibility="public")


_E190_CLAUSE_DESCRIPTION = (
    "A function value of type fn(Int -> Int) effects(pure) is used where the "
    "parameter of the 'throw' clause gives it the type fn(Int -> Nat) "
    "effects(pure): its result is declared `Int`, and that type promises "
    "`Nat`, which a result declared `Int` does not guarantee.")
#: The parameter is the one rewrite: the value is the operation's, at the
#: handled effect's type, which no rewrite of a closure changes.
_E190_CLAUSE_FIX = (
    "Write the parameter at the type 'throw' takes, "
    "`fn(Int -> Int) effects(pure)`, named by a type alias where it holds "
    "a function type: its result is `Int`, where the parameter's type "
    "states `Nat`.")


def test_repro_a_clause_parameter_narrower_by_a_result_is_e190_read_whole(
        ) -> None:
    """`throw(@F)` under `Exn<G>`: `F` promises a `Nat` result `G` does not
    guarantee.  E190 names the clause as what gave the position its type,
    and its fix names the clause's parameter as the declaration to change;
    written at `G`, the clause checks."""
    source = _clause_over("G", "F")
    (diagnostic,) = pipeline.check(source).errors
    assert diagnostic.error_code == "E190"
    assert diagnostic.description == _E190_CLAUSE_DESCRIPTION, (
        diagnostic.description)
    assert diagnostic.fix == _E190_CLAUSE_FIX, diagnostic.fix
    assert _codes(_clause_over("G", "G")) == []


def test_repro_a_function_typed_clause_parameter_s_e342_fix_is_prose(
        ) -> None:
    """`throw(@G)` under `Exn<IOF>`: the operation's value performs IO the
    parameter's type does not declare, which is no narrowing, so E342.  A
    slot names a function type through an alias, so the fix names the
    operation's type in prose, never `@fn(...)`; written at the operation's
    type, the clause checks."""
    source = _clause_over("IOF", "G").replace(
        "  effects(pure)\n{\n  let @IOF", "  effects(<IO>)\n{\n  let @IOF")
    (diagnostic,) = pipeline.check(source).errors
    assert diagnostic.error_code == "E342"
    assert diagnostic.description == (
        "Handler clause 'throw' binds its parameter at type fn(Int -> Int) "
        "effects(pure), but the operation is performed with a value of type "
        "fn(Int -> Int) effects(<IO>).")
    assert diagnostic.fix == (
        "Write the parameter at the type 'throw' takes, and bind the value "
        "at another type with a `let` in the clause body where it fits "
        "there."), diagnostic.fix
    fixed = source.replace("throw(@G) ->", "throw(@IOF) ->")
    assert fixed != source
    assert _codes(fixed) == [], fixed


#: (the operation's type, the parameter's, the value thrown, the whole fix):
#: the fix is the one instruction that clears E190 whichever parts are
#: unfit, the type the operation takes, with the first unfit part as its
#: reason.  Each cell's clause written at that type checks.
_CLAUSE_PART_TYPES = (
    "type G = fn(Int -> Int) effects(pure);\n"
    "type F = fn(Int -> Nat) effects(pure);\n"
    "type P = fn(Nat -> Int) effects(pure);\n"
    "type H = fn(G -> Int) effects(pure);\n"
    "type HF = fn(F -> Int) effects(pure);\n\n")
_TAKES = ("Write the parameter at the type 'throw' takes, `{ty}`, named by a "
          "type alias where it holds a function type: {why}.")
_CLAUSE_PARTS = {
    "result-unfit": ("G", "F", "fn(@Int -> @Int) effects(pure) { @Int.0 }",
                     _TAKES.format(
                         ty="fn(Int -> Int) effects(pure)",
                         why="its result is `Int`, where the parameter's "
                             "type states `Nat`")),
    "parameter-unfit": ("P", "G", "fn(@Nat -> @Int) effects(pure) { 0 }",
                        _TAKES.format(
                            ty="fn(Nat -> Int) effects(pure)",
                            why="its parameter 0 is `Nat`, where the "
                                "parameter's type states `Int`")),
    "both-unfit": ("P", "F", "fn(@Nat -> @Int) effects(pure) { 0 }",
                   _TAKES.format(
                       ty="fn(Nat -> Int) effects(pure)",
                       why="its parameter 0 is `Nat`, where the parameter's "
                           "type states `Int`")),
    "nested": ("Option<G>", "Option<F>",
               "Some(fn(@Int -> @Int) effects(pure) { @Int.0 })",
               _TAKES.format(
                   ty="Option<fn(Int -> Int) effects(pure)>",
                   why="inside it, a function type's result is `Int`, where "
                       "the parameter's type states `Nat`")),
    "function-typed-parameter": (
        "HF", "H", "fn(@F -> @Int) effects(pure) { 0 }",
        _TAKES.format(
            ty="fn(fn(Int -> Nat) effects(pure) -> Int) effects(pure)",
            why="its parameter 0 is `fn(Int -> Nat) effects(pure)`, where "
                "the parameter's type states `fn(Int -> Int) "
                "effects(pure)`")),
}


def _clause_part(op_ty: str, written: str, value: str) -> str:
    return _CLAUSE_PART_TYPES + _fn(
        "go(@Int -> @Int)",
        f"let @{op_ty} = {value};\n"
        f"  handle[Exn<{op_ty}>] {{\n    throw(@{written}) -> {{ 0 }}\n"
        f"  }} in {{\n    throw(@{op_ty}.0)\n  }}", visibility="public")


@pytest.mark.parametrize("cell", list(_CLAUSE_PARTS))
def test_repro_a_clause_parameter_s_e190_fix_clears_it_whichever_part(
        cell: str) -> None:
    """The fix named only the part reported: with the parameter and the
    result both unfit, written as it said (`fn(Nat -> Nat)`) the clause was
    E190 again, for the result.  The type the operation takes clears it in
    every cell."""
    op_ty, written, value, fix = _CLAUSE_PARTS[cell]
    source = _clause_part(op_ty, written, value)
    (diagnostic,) = pipeline.check(source).errors
    assert diagnostic.error_code == "E190", diagnostic.description
    assert diagnostic.fix == fix, diagnostic.fix
    fixed = source.replace(f"throw(@{written}) ->", f"throw(@{op_ty}) ->")
    assert fixed != source
    assert _codes(fixed) == [], fixed
