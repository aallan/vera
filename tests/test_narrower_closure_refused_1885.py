"""A function value whose parameter is narrower than the function type it
reaches is refused at check (#1885, spec §2.8).

A function type is contravariant in its parameters: a function value fits
one only if it accepts every value the type's parameter admits.  The
checker's permission to narrow a VALUE (an `Int` where a `Nat` or a
refinement of `Int` is expected, obligated and checked where the value
flows) used to reach a function type's parameter through `is_subtype`'s
function rule, where there is no value to check.  So a `fn(@Pos -> @Int)`
was accepted at `fn(Int -> Int)` with nothing recorded, and trapped at its
own entry on a value the type admits, and a `fn(@Nat -> @Int)` bound -5 to
its `@Nat` parameter with no check at all.  Two refinements of one base were
compared by their base alone, so a `fn(@Big -> @Int)` passed at
`fn(Pos -> Int)` too.

The rule: inside a function type's parameter the comparison is the formal
relation (`is_formal_subtype`): never `Int <: Nat`, never a type to a
refinement of it, and two refinements of one base only where they state the
same predicate.  Every flow refuses with E189, whose fix names the closure's
parameter type, the position's, and what gave the position its type.

The matrix is the flow (each place a function value meets a function type)
x the relation of the closure's parameter to the position's (narrower by a
refinement, by `Nat`, by predicate, wider only by implication, equal,
wider) x how the narrowness arises (a closure written in place, a slot bound
at its own function type, a refinement inside the parameter's type
argument).  A refused cell asserts E189 is the one error; an accepted cell
verifies with reconciliation and runs to the value it should.
"""

from __future__ import annotations

import json
from dataclasses import dataclass

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/types.py", "vera/checker/core.py", "vera/checker/control.py"])

_ALIASES = (
    "type Pos = { @Int | @Int.0 > 0 };\n"
    "type Big = { @Int | @Int.0 > 10 };\n"
)

_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _fn(signature: str, body: str, *, visibility: str = "private",
        requires: str = "true") -> str:
    return (f"{visibility} fn {signature}\n  requires({requires})\n"
            f"  ensures(true)\n  effects(pure)\n{{\n  {body}\n}}\n\n")


def _codes(source: str) -> list[str]:
    checked = pipeline.check(source)
    return [d.error_code for d in checked.errors]


def _only_diagnostic(source: str) -> dict[str, object]:
    envelope = pipeline.check(source).envelope()
    diagnostics = envelope["diagnostics"]
    assert isinstance(diagnostics, list)
    assert [d["error_code"] for d in diagnostics] == ["E189"], json.dumps(
        diagnostics, indent=1)[:2000]
    return diagnostics[0]


def _accepted(source: str, value: int) -> None:
    verified = pipeline.verify(source, reconcile=True)
    assert verified.ok, verified.diagnostics
    ran = pipeline.run(source, fn="main", args=[50])
    assert ran.trap is None, str(ran.trap)[:300]
    assert ran.execution.value == value


# =====================================================================
# The reported forms
# =====================================================================

_LET = _ALIASES + "type F = fn(Int -> Int) effects(pure);\n\n" + _fn(
    "main(@Int -> @Int)",
    "let @F = fn(@Pos -> @Int) effects(pure) { @Pos.0 };\n"
    "  apply_fn(@F.0, @Int.0)", visibility="public")

_NAT_LET = "type F = fn(Int -> Int) effects(pure);\n\n" + _fn(
    "main(@Int -> @Int)",
    "let @F = fn(@Nat -> @Int) effects(pure) { @Nat.0 };\n"
    "  apply_fn(@F.0, @Int.0)", visibility="public")

_ARRAY_MAP = _ALIASES + _fn(
    "main(@Int -> @Int)",
    "let @Array<Int> = array_map([@Int.0], fn(@Pos -> @Int) effects(pure) "
    "{ @Pos.0 });\n  @Array<Int>.0[0]", visibility="public")

_GENERIC = _ALIASES + "type G<T> = fn(T -> Int) effects(pure);\n\n" + _fn(
    "forall<T> fn app(@G<T>, @T -> @Int)".removeprefix("forall<T> fn "),
    "apply_fn(@G<T>.0, @T.0)").replace(
        "private fn app", "private forall<T> fn app") + _fn(
    "main(@Int -> @Int)",
    "app(fn(@Pos -> @Int) effects(pure) { @Pos.0 }, @Int.0)",
    visibility="public")

_IMPLIED = _ALIASES + "type FB = fn(Big -> Int) effects(pure);\n\n" + _fn(
    "main(@Int -> @Int)",
    "let @FB = fn(@Pos -> @Int) effects(pure) { @Pos.0 };\n"
    "  let @Big = @Int.0;\n  apply_fn(@FB.0, @Big.0)",
    visibility="public", requires="@Int.0 > 10")


def test_repro_a_narrower_closure_bound_by_a_let_is_refused_1885() -> None:
    """The issue's form: was accepted, and trapped at the closure's entry
    at -5, a value `fn(Int -> Int)` admits."""
    diagnostic = _only_diagnostic(_LET)
    assert diagnostic["description"] == (
        "A function value of type fn({ @Int | @Int.0 > 0 } -> Int) "
        "effects(pure) is used where the `let` binding gives it the type "
        "fn(Int -> Int) effects(pure): its parameter 0 is declared `Pos`, "
        "and that type hands it any `Int`, not only a `Pos`.")
    assert diagnostic["fix"] == (
        "Declare the closure's parameter 0 as `@Int`, the type the position "
        "hands it, and narrow inside, where there is a value to check: "
        "`fn(@Int -> @Int) effects(pure) { let @Pos = @Int.0; ... }`.  Or "
        "declare the binding at a function type whose parameter 0 is "
        "`Pos`.")
    assert diagnostic["spec_ref"] == 'Chapter 2, Section 2.8 "Subtyping Rules"'


def test_repro_a_nat_closure_at_an_int_type_is_refused_1885() -> None:
    """The silent member: the `@Nat` parameter held -5, with check and
    verify clean.  Also #1819's parameter line."""
    assert _codes(_NAT_LET) == ["E189"]


def test_repro_array_map_names_its_instance_and_the_argument_1885() -> None:
    """The generic route: `A` is `Int`, fixed by the array, and the fix
    says to pass an `Array<Pos>` or to narrow inside."""
    diagnostic = _only_diagnostic(_ARRAY_MAP)
    assert diagnostic["description"] == (
        "A function value of type fn({ @Int | @Int.0 > 0 } -> Int) "
        "effects(pure) is used where 'array_map', instantiated at `A = Int` "
        "by argument 0 (`Array<Int>`), gives it the type fn(Int -> Int) "
        "effects(pure): its parameter 0 is declared `Pos`, and that type "
        "hands it any `Int`, not only a `Pos`.")
    assert diagnostic["fix"] == (
        "Declare the closure's parameter 0 as `@Int`, the type the position "
        "hands it, and narrow inside, where there is a value to check: "
        "`fn(@Int -> @Int) effects(pure) { let @Pos = @Int.0; ... }`.  Or "
        "pass argument 0 as `Array<Pos>`, which fixes `A` at `Pos`.")


def test_repro_a_user_generic_names_its_instance_1885() -> None:
    """`app(@G<T>, @T)` at `T = Int` from its second argument."""
    diagnostic = _only_diagnostic(_GENERIC)
    description = diagnostic["description"]
    assert isinstance(description, str)
    assert ("'app', instantiated at `T = Int` by argument 1 (`Int`)"
            in description), description
    assert "pass argument 1 as `Pos`, which fixes `T` at `Pos`" in str(
        diagnostic["fix"])


def test_repro_a_closure_wider_only_by_implication_is_refused_1885() -> None:
    """`Big` implies `Pos`, but two refinements fit only where they state
    the same predicate."""
    diagnostic = _only_diagnostic(_IMPLIED)
    assert "one that implies the other is not enough" in str(
        diagnostic["description"])


def test_repro_both_rewrites_the_fix_names_check_and_run_1885() -> None:
    """The two rewrites E189's fix gives for the generic route are programs
    that check, verify and run."""
    narrowed = _ALIASES + _fn(
        "main(@Int -> @Int)",
        "let @Array<Int> = array_map([@Int.0], fn(@Int -> @Int) "
        "effects(pure) { let @Pos = @Int.0; @Pos.0 });\n  @Array<Int>.0[0]",
        visibility="public", requires="@Int.0 > 10")
    _accepted(narrowed, 50)
    narrower_array = _ALIASES + _fn(
        "main(@Int -> @Int)",
        "let @Array<Pos> = [@Int.0];\n"
        "  let @Array<Int> = array_map(@Array<Pos>.0, fn(@Pos -> @Int) "
        "effects(pure) { @Pos.0 });\n  @Array<Int>.0[0]",
        visibility="public", requires="@Int.0 > 10")
    _accepted(narrower_array, 50)




# =====================================================================
# The result direction (#1819)
# =====================================================================

_RESULT_POS = _ALIASES + "type RP = fn(Int -> Pos) effects(pure);\n\n" + _fn(
    "main(@Int -> @Nat)",
    "let @RP = fn(@Int -> @Int) effects(pure) { @Int.0 };\n"
    "  let @Pos = apply_fn(@RP.0, @Int.0);\n  let @Nat = @Pos.0;\n  @Nat.0",
    visibility="public")

_RESULT_NAT = "type IntToNat = fn(Int -> Nat) effects(pure);\n\n" + _fn(
    "main(@Int -> @Nat)",
    "let @IntToNat = fn(@Int -> @Int) effects(pure) { @Int.0 };\n"
    "  apply_fn(@IntToNat.0, @Int.0)", visibility="public")


def test_repro_a_wider_result_read_back_as_pos_is_refused_1819() -> None:
    """Was accepted: the `Pos` read back from the closure was trusted, so
    `let @Nat = @Pos.0` was proved at Tier 1 from a fact nothing checked,
    and the run at -5 trapped at the `Nat` guard."""
    diagnostic = _only_diagnostic(_RESULT_POS)
    assert diagnostic["description"] == (
        "A function value of type fn(Int -> Int) effects(pure) is used where "
        "the `let` binding gives it the type fn(Int -> { @Int | @Int.0 > 0 }) "
        "effects(pure): its result is declared `Int`, and that type promises "
        "`{ @Int | @Int.0 > 0 }`, which a result declared `Int` does not "
        "guarantee.")
    assert diagnostic["fix"] == (
        "Declare the closure's result as `@{ @Int | @Int.0 > 0 }`, the type "
        "the position states: `fn(@Int -> @{ @Int | @Int.0 > 0 }) "
        "effects(pure) { ... }`; the closure's own return is then proved or "
        "checked, where the value is.  Or declare the binding at a function "
        "type whose result is `Int`.")


def test_repro_a_wider_result_at_a_nat_type_is_refused_1819() -> None:
    """Was silent: `main`, declared `-> @Nat`, returned -5, with check and
    verify clean."""
    assert _codes(_RESULT_NAT) == ["E189"]


def test_repro_the_issue_s_program_and_its_wrapper_1819() -> None:
    """#1819's program: refused at the call, and the fix is the wrapper the
    issue names, which checks and puts the `Int` to `Nat` flow on a closure's
    own return, guarded there."""
    issue = (
        "type IntToNat = fn(Int -> Nat) effects(pure);\n"
        "type IntToInt = fn(Int -> Int) effects(pure);\n\n"
        + _fn("apply_nat(@IntToNat, @Int -> @Nat)",
              "apply_fn(@IntToNat.0, @Int.0)")
        + _fn("main(@Int -> @Nat)",
              "let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 };\n"
              "  apply_nat(@IntToInt.0, @Int.0)", visibility="public"))
    diagnostic = _only_diagnostic(issue)
    wrapper = ("fn(@Int -> @Nat) effects(pure) "
               "{ apply_fn(@IntToInt.0, @Int.0) }")
    assert f"`{wrapper}`" in str(diagnostic["fix"]), diagnostic["fix"]
    fixed = issue.replace(
        "  apply_nat(@IntToInt.0, @Int.0)",
        f"  let @IntToNat = {wrapper};\n  apply_nat(@IntToNat.0, @Int.0)")
    assert pipeline.verify(fixed, reconcile=True).ok
    assert pipeline.run(fixed, fn="main", args=[-5]).trap is not None
    assert pipeline.run(fixed, fn="main", args=[5]).execution.value == 5


def test_repro_the_sound_directions_stay_admitted_1819() -> None:
    """#1819's controls: `fn(Int -> Nat)` at `fn(Int -> Int)` and
    `fn(Int -> Int)` at `fn(Nat -> Int)` check, verify and run."""
    narrower_result = "type IntToInt = fn(Int -> Int) effects(pure);\n\n" + _fn(
        "main(@Int -> @Int)",
        "let @IntToInt = fn(@Int -> @Nat) effects(pure) { 7 };\n"
        "  apply_fn(@IntToInt.0, @Int.0)", visibility="public")
    _accepted(narrower_result, 7)
    wider_param = "type NatToInt = fn(Nat -> Int) effects(pure);\n\n" + _fn(
        "main(@Int -> @Int)",
        "let @NatToInt = fn(@Int -> @Int) effects(pure) { @Int.0 };\n"
        "  let @Nat = @Int.0;\n  apply_fn(@NatToInt.0, @Nat.0)",
        visibility="public", requires="@Int.0 >= 0")
    _accepted(wider_param, 50)


# =====================================================================
# The matrix
# =====================================================================

#: The types a cell pairs, and the formal relation among them, written out
#: independently of `is_formal_subtype`: a type, `Nat`, `Pos` and `Big`
#: each below `Int`, and nothing else (two refinements of one base meet
#: only where they state the same predicate).
_BELOW = {("Nat", "Int"), ("Pos", "Int"), ("Big", "Int")}


def _le(a: str, b: str) -> bool:
    return a == b or (a, b) in _BELOW


#: (position's type, value's type) at the parameter or the result.
PAIRS = (("Int", "Pos"), ("Int", "Nat"), ("Pos", "Big"), ("Big", "Pos"),
         ("Pos", "Pos"), ("Pos", "Int"), ("Nat", "Int"), ("Int", "Int"))

#: How the pair arises: a closure written in place, a slot bound at the
#: closure's own function type, the pair inside a type argument, and the
#: pair one function type deeper, at its result (variance kept) or its
#: parameter (variance flipped).
FORMS = ("in-place", "slot", "type-argument", "nested-kept", "nested-flipped")

FLOWS = ("let", "argument", "field", "if-join", "match-join", "return",
         "array-element", "tuple-element", "option", "closure-return",
         "apply-fn-argument", "handler-state", "state-put", "state-update",
         "generic", "array-map")


@dataclass(frozen=True)
class Shape:
    """One cell's texts: the types the position and the value have (`F`
    and `G`), the value written in place, a value of the position's type
    for a join's other arm, the argument `F` is applied to and its type,
    the expression that turns the application's result into an `Int`
    (`{}` the application), and the value `main` returns at 50."""

    aliases: str
    value: str
    exact: str
    arg: str
    arg_type: str
    use: str
    result: int


def _shape(kind: str, form: str, p: str, c: str) -> Shape:
    if kind == "parameter":
        if form == "type-argument":
            return Shape(
                f"type F = fn(Array<{p}> -> Int) effects(pure);\n"
                f"type G = fn(Array<{c}> -> Int) effects(pure);\n",
                f"fn(@Array<{c}> -> @Int) effects(pure) "
                f"{{ array_length(@Array<{c}>.0) }}",
                f"fn(@Array<{p}> -> @Int) effects(pure) "
                f"{{ array_length(@Array<{p}>.0) }}",
                f"[@{p}.0]", f"Array<{p}>", "{}", 1)
        if form.startswith("nested"):
            inner = ("fn(Int -> {}) effects(pure)" if form == "nested-kept"
                     else "fn({} -> Int) effects(pure)")
            arg = (f"fn(@Int -> @{p}) effects(pure) {{ @Int.0 }}"
                   if form == "nested-kept"
                   else f"fn(@{p} -> @Int) effects(pure) {{ @{p}.0 }}")
            return Shape(
                f"type PF = {inner.format(p)};\n"
                f"type CF = {inner.format(c)};\n"
                "type F = fn(PF -> Int) effects(pure);\n"
                "type G = fn(CF -> Int) effects(pure);\n",
                "fn(@CF -> @Int) effects(pure) { apply_fn(@CF.0, 50) }",
                "fn(@PF -> @Int) effects(pure) { apply_fn(@PF.0, 50) }",
                arg, "PF", "{}", 50)
        return Shape(
            f"type F = fn({p} -> Int) effects(pure);\n"
            f"type G = fn({c} -> Int) effects(pure);\n",
            f"fn(@{c} -> @Int) effects(pure) {{ @{c}.0 }}",
            f"fn(@{p} -> @Int) effects(pure) {{ @{p}.0 }}",
            f"@{p}.0", p, "{}", 50)
    if form == "type-argument":
        return Shape(
            f"type F = fn(Int -> Array<{p}>) effects(pure);\n"
            f"type G = fn(Int -> Array<{c}>) effects(pure);\n",
            f"fn(@Int -> @Array<{c}>) effects(pure) {{ [@Int.0] }}",
            f"fn(@Int -> @Array<{p}>) effects(pure) {{ [@Int.0] }}",
            "@Int.0", "Int", "array_length({})", 1)
    if form.startswith("nested"):
        kept = form == "nested-kept"
        inner = ("fn(Int -> {}) effects(pure)" if kept
                 else "fn({} -> Int) effects(pure)")

        def literal(t: str) -> str:
            body = (f"fn(@Int -> @{t}) effects(pure) {{ @Int.0 }}" if kept
                    else f"fn(@{t} -> @Int) effects(pure) {{ @{t}.0 }}")
            return f"fn(@Int -> @{'PF' if t == p else 'CF'}) effects(pure) {{ {body} }}"
        return Shape(
            f"type PF = {inner.format(p)};\n"
            f"type CF = {inner.format(c)};\n"
            "type F = fn(Int -> PF) effects(pure);\n"
            "type G = fn(Int -> CF) effects(pure);\n",
            literal(c), literal(p), "@Int.0", "Int",
            "apply_fn({}, 50)", 50)
    return Shape(
        f"type F = fn(Int -> {p}) effects(pure);\n"
        f"type G = fn(Int -> {c}) effects(pure);\n",
        f"fn(@Int -> @{c}) effects(pure) {{ @Int.0 }}",
        f"fn(@Int -> @{p}) effects(pure) {{ @Int.0 }}",
        "@Int.0", "Int", "{}", 50)


def _flow(flow: str, kind: str, pre: str, v: str, s: Shape) -> tuple[str, str]:
    """The helpers and `main`'s body for *flow*, with *pre* the statements
    that bind the value and *v* the value."""
    x = s.arg

    def apply(fn_value: str, arg: str = x) -> str:
        return s.use.format(f"apply_fn({fn_value}, {arg})")

    if flow == "let":
        return "", f"{pre}let @F = {v};\n  {apply('@F.0')}"
    if flow == "argument":
        helper = _fn(f"run_f(@F, @{s.arg_type} -> @Int)",
                     apply("@F.0", f"@{s.arg_type}.0"))
        return helper, f"{pre}run_f({v}, {x})"
    if flow == "field":
        return ("private data H {\n  MkH(F)\n}\n\n",
                f"{pre}match MkH({v}) {{\n    MkH(@F) -> {apply('@F.0')}\n  }}")
    if flow == "if-join":
        return "", (f"{pre}let @F = if @Int.0 > 100 then {{ {s.exact} }} "
                    f"else {{ {v} }};\n  {apply('@F.0')}")
    if flow == "match-join":
        return "", (f"{pre}let @F = match @Int.0 > 100 {{\n"
                    f"    true -> {s.exact},\n    false -> {v}\n  }};\n"
                    f"  {apply('@F.0')}")
    if flow == "return":
        return (_fn("mk(@Unit -> @F)", f"{pre}{v}"),
                f"let @F = mk(());\n  {apply('@F.0')}")
    if flow == "array-element":
        return "", (f"{pre}let @Array<F> = [{v}];\n"
                    f"  {apply('@Array<F>.0[0]')}")
    if flow == "tuple-element":
        return "", (f"{pre}let @Tuple<F, Bool> = Tuple({v}, true);\n"
                    f"  match @Tuple<F, Bool>.0 {{\n"
                    f"    Tuple(@F, @Bool) -> {apply('@F.0')}\n  }}")
    if flow == "option":
        return "", (f"{pre}let @Option<F> = Some({v});\n"
                    f"  match @Option<F>.0 {{\n"
                    f"    Some(@F) -> {apply('@F.0')},\n    None -> 0\n  }}")
    if flow == "closure-return":
        return ("type MkF = fn(Unit -> F) effects(pure);\n\n",
                f"let @MkF = fn(@Unit -> @F) effects(pure) {{ {pre}{v} }};\n"
                f"  {apply('apply_fn(@MkF.0, ())')}")
    if flow == "apply-fn-argument":
        return ("type UseF = fn(F -> Int) effects(pure);\n\n",
                f"let @UseF = fn(@F -> @Int) effects(pure) "
                f"{{ {apply('@F.0')} }};\n  {pre}apply_fn(@UseF.0, {v})")
    if flow == "handler-state":
        return "", (f"{pre}handle[State<F>](@F = {v}) {{\n"
                    f"    get(@Unit) -> {{ resume(@F.0) }},\n"
                    f"    put(@F) -> {{ resume(()) }}\n"
                    f"  }} in {{\n    {apply('get(())')}\n  }}")
    if flow == "state-put":
        return "", (f"{pre}handle[State<F>](@F = {s.exact}) {{\n"
                    f"    get(@Unit) -> {{ resume(@F.0) }},\n"
                    f"    put(@F) -> {{ resume(()) }}\n"
                    f"  }} in {{\n    put({v});\n    {apply('get(())')}\n  }}")
    if flow == "state-update":
        return "", (f"{pre}handle[State<F>](@F = {s.exact}) {{\n"
                    f"    get(@Unit) -> {{ resume(@F.0) }},\n"
                    f"    put(@F) -> {{ resume(()) }} with @F = {v}\n"
                    f"  }} in {{\n    put({s.exact});\n"
                    f"    {apply('get(())')}\n  }}")
    if flow == "generic" and kind == "parameter":
        helper = ("type GP<T> = fn(T -> Int) effects(pure);\n\n"
                  + _fn("app(@GP<T>, @T -> @Int)", "apply_fn(@GP<T>.0, @T.0)")
                  .replace("private fn app", "private forall<T> fn app"))
        return helper, f"{pre}app({v}, {x})"
    if flow == "generic":
        helper = ("type GR<T> = fn(Int -> T) effects(pure);\n\n"
                  + _fn("app(@GR<T>, @Int -> @T)", "apply_fn(@GR<T>.0, @Int.0)")
                  .replace("private fn app", "private forall<T> fn app"))
        return helper, f"{pre}{s.use.format(f'app({v}, {x})')}"
    if flow == "array-map" and kind == "parameter":
        return "", (f"{pre}let @Array<Int> = array_map([{x}], {v});\n"
                    f"  @Array<Int>.0[0]")
    if flow == "array-map":
        return "", f"{pre}array_length(array_map([{x}], {v}))"
    raise AssertionError(flow)


def program(flow: str, kind: str, form: str, p: str, c: str) -> str:
    s = _shape(kind, form, p, c)
    if form == "slot":
        pre, v = f"let @G = {s.value};\n  ", "@G.0"
    else:
        pre, v = "", s.value
    helpers, body = _flow(flow, kind, pre, v, s)
    bind = f"let @{p} = @Int.0;\n  " if kind == "parameter" else ""
    return (_ALIASES + s.aliases + "\n" + helpers
            + _fn("main(@Int -> @Int)", bind + body, visibility="public",
                  requires="@Int.0 > 10"))


def expected_refused(flow: str, kind: str, form: str, p: str, c: str) -> bool:
    """A parameter fits where the position's type is below the value's, a
    result where the value's is below the position's; one function type
    deeper at a parameter, the direction flips.  Two exceptions, both the
    generic's instance being chosen from the closure itself (spec §4.2): a
    `Nat` parameter the closure declares at a generic's variable fixes the
    variable at `Nat`, so the `Int` argument is the narrowing, and at the
    result the closure's own type fixes the variable."""
    if flow in ("generic", "array-map"):
        if kind == "result":
            return False
        if c == "Nat" and form in ("in-place", "slot"):
            return False
    flipped = form == "nested-flipped"
    if kind == "parameter":
        return not (_le(c, p) if flipped else _le(p, c))
    return not (_le(p, c) if flipped else _le(c, p))


#: A user generic whose variable the closure, its first argument, gives one
#: refinement and the value another of the same base is instantiated at the
#: closure's: the order of the arguments decides the instance (with the value
#: first the closure is refused).  Sound (the value is narrowed into the
#: closure's refinement, obligated), but against spec §5.9's rule B; its own
#: mechanism, the first binding `_unify_for_inference` keeps.
_ORDER_DECIDES = (
    "the closure's refinement, the first argument's, is the instance: the "
    "order of the arguments decides a variable two refinements of one base "
    "give (spec §5.9 rule B)")


def _cell(flow: str, kind: str, form: str, p: str, c: str) -> object:
    cell = (flow, kind, form, p, c)
    if ((flow, kind) == ("generic", "parameter")
            and form in ("in-place", "slot", "type-argument")
            and {p, c} == {"Pos", "Big"}):
        return pytest.param(*cell, id="-".join(cell), marks=pytest.mark.xfail(
            strict=True, reason=_ORDER_DECIDES))
    return pytest.param(*cell, id="-".join(cell))


CELLS = [_cell(flow, kind, form, p, c) for flow in FLOWS
         for kind in ("parameter", "result") for form in FORMS
         for p, c in PAIRS]


@pytest.mark.parametrize(("flow", "kind", "form", "p", "c"), CELLS)
def test_a_function_value_meets_a_function_type(
        flow: str, kind: str, form: str, p: str, c: str) -> None:
    source = program(flow, kind, form, p, c)
    if expected_refused(flow, kind, form, p, c):
        assert _codes(source) == ["E189"], source
    else:
        # `array_map`'s result column counts the mapped array.
        _accepted(source, 1 if (flow, kind) == ("array-map", "result")
                  else _shape(kind, form, p, c).result)


#: What each flow names as giving the position its type, and the
#: declaration its fix's second rewrite changes (a `Pos` closure at an `Int`
#: parameter, written in place).
_NAMED = {
    "let": ("the `let` binding", "declare the binding at"),
    "argument": ("parameter 0 of 'run_f'",
                 "declare parameter 0 of 'run_f' at"),
    "field": ("field 0 of 'MkH'", "declare field 0 of 'MkH' at"),
    "if-join": ("the `let` binding", "declare the binding at"),
    "match-join": ("the `let` binding", "declare the binding at"),
    "return": ("the return type of 'mk'", "declare the return type of 'mk' at"),
    "array-element": ("the `let` binding", "declare the binding at"),
    "tuple-element": ("the `let` binding", "declare the binding at"),
    "option": ("the `let` binding", "declare the binding at"),
    "closure-return": ("the closure's declared return type",
                       "declare the closure's return type at"),
    "apply-fn-argument": ("parameter 0 of the applied function type",
                          "declare parameter 0 of the applied function type at"),
    "handler-state": ("the handler's state type",
                      "declare the handler's state at"),
    "state-put": ("parameter 0 of 'put'", "declare parameter 0 of 'put' at"),
    "state-update": ("the handler's state type",
                     "declare the handler's state at"),
}


_BUILT_AROUND = ("if-join", "match-join", "array-element", "tuple-element",
                 "option")


def test_every_flow_names_what_gave_the_position_its_type() -> None:
    """One message shape at every flow: the description names what gave the
    position its type, and the fix's second rewrite the declaration to
    change, here a `Pos` closure where an `Int` parameter is."""
    for flow, (gave, declare) in _NAMED.items():
        diagnostic = _only_diagnostic(
            program(flow, "parameter", "in-place", "Int", "Pos"))
        description, fix = str(diagnostic["description"]), str(diagnostic["fix"])
        assert f"where {gave} gives it the type" in description, (flow, description)
        # A closure written in place is named as written; a value built
        # around it (a join, an element) by its type, the predicate spelt.
        spelt = ("{ @Int | @Int.0 > 0 }" if flow in _BUILT_AROUND else "Pos")
        assert (f"Or {declare} a function type whose parameter 0 is "
                f"`{spelt}`." in fix), (flow, fix)
        assert diagnostic["rationale"] == _RATIONALE, flow


def test_a_join_no_type_accepts_names_the_join() -> None:
    """Two refinements of one base at a parameter, joined with nothing
    expected: the join keeps their base, which neither arm accepts."""
    source = _ALIASES + _fn(
        "main(@Int -> @Int)",
        "apply_fn(if @Int.0 > 100 then { fn(@Pos -> @Int) effects(pure) "
        "{ @Pos.0 } } else { fn(@Big -> @Int) effects(pure) { @Big.0 } }, "
        "@Int.0)", visibility="public", requires="@Int.0 > 10")
    diagnostic = _only_diagnostic(source)
    assert "where the join with its sibling arms gives it the type" in str(
        diagnostic["description"])
    assert "Or declare every arm at a function type whose parameter 0 is" in str(
        diagnostic["fix"])


_RATIONALE = (
    "A function type is contravariant in its parameters and covariant in its "
    "result (spec §2.8 rule 5): a function value fits it only if it accepts "
    "every value the type's parameter admits and guarantees the result the "
    "type promises.  The narrowing the checker permits for a value (an `Int` "
    "where a `Nat` or a refinement is expected) is obligated and checked "
    "where the value is; inside a function type there is none: an argument "
    "is the caller's to check, at the call, and a result the function's own, "
    "on its return.")


# =====================================================================
# Outside the class: each flow keeps its own diagnostic
# =====================================================================

_FN = "type F = fn(Int -> Int) effects(pure);\n\n"

#: A function value that fits its function type by no narrowing (a
#: parameter of another base, another data type, another arity, a result of
#: another base, a wider effect row, a narrowing beside one of these), each
#: at a `let`: the `let`'s own mismatch, E170, never E189.
_OUTSIDE = {
    "another base": (_FN, "fn(@String -> @Int) effects(pure) { 0 }"),
    "another data type": (
        "type F = fn(Array<Int> -> Int) effects(pure);\n\n",
        "fn(@Option<Int> -> @Int) effects(pure) { 0 }"),
    "another data type around a narrowing": (
        "type F = fn(Option<Int> -> Int) effects(pure);\n\n",
        "fn(@Array<Pos> -> @Int) effects(pure) { 0 }"),
    "another arity beside a narrowing": (
        _FN, "fn(@Pos, @Int -> @Int) effects(pure) { 0 }"),
    "a result of another base beside a narrowing": (
        _FN, "fn(@Pos -> @String) effects(pure) { \"\" }"),
    "a wider effect row beside a narrowing": (
        _FN, "fn(@Pos -> @Int) effects(<IO>) { 0 }"),
}


def test_a_mismatch_outside_the_class_keeps_the_let_s_code() -> None:
    for name, (alias, value) in _OUTSIDE.items():
        source = _ALIASES + alias + _fn(
            "main(@Int -> @Int)", f"let @F = {value};\n  0",
            visibility="public")
        assert _codes(source) == ["E170"], name


def test_a_function_value_where_no_function_type_is_keeps_its_code() -> None:
    """A closure where a data type or a scalar is expected: no function
    type to compare, so the `let`'s own E170."""
    for declared in ("Option<F>", "Int"):
        source = _ALIASES + _FN + _fn(
            "main(@Int -> @Int)",
            f"let @{declared} = fn(@Pos -> @Int) effects(pure) {{ 0 }};\n  0",
            visibility="public")
        assert _codes(source) == ["E170"], declared


#: A `String`-taking closure at each flow whose own mismatch E189 replaces
#: for the class: the flow's code stands for a value outside it.
_OWN_CODE = {
    "let": "E170", "argument": "E202", "field": "E213", "return": "E121",
    "closure-return": "E171", "apply-fn-argument": "E202",
    "handler-state": "E331", "state-put": "E204", "state-update": "E335",
}


def test_every_flow_keeps_its_own_code_outside_the_class() -> None:
    for flow, code in _OWN_CODE.items():
        source = program(flow, "parameter", "in-place", "Int", "Pos").replace(
            "fn(@Pos -> @Int) effects(pure) { @Pos.0 }",
            "fn(@String -> @Int) effects(pure) { 0 }")
        assert code in _codes(source), (flow, _codes(source))
        assert "E189" not in _codes(source), flow


def test_an_unresolved_parameter_type_draws_no_cascade() -> None:
    """A closure whose parameter names a type nothing declares: its E136
    alone, as everywhere (the unknown fits a function type's position)."""
    source = _FN + _fn(
        "main(@Int -> @Int)",
        "let @F = fn(@Missing -> @Int) effects(pure) { 0 };\n  0",
        visibility="public")
    assert _codes(source) == ["E136"]


def test_a_generic_s_concrete_function_parameter_is_named_as_a_parameter(
        ) -> None:
    """A generic whose function-typed parameter is concrete: the position
    is that parameter, no instance to name."""
    source = _ALIASES + "type F = fn(Int -> Int) effects(pure);\n\n" + _fn(
        "run(@F, @T -> @T)", "@T.0").replace(
            "private fn run", "private forall<T> fn run") + _fn(
        "main(@Int -> @Int)",
        "run(fn(@Pos -> @Int) effects(pure) { @Pos.0 }, @Int.0)",
        visibility="public")
    diagnostic = _only_diagnostic(source)
    assert "where parameter 0 of 'run' gives it the type" in str(
        diagnostic["description"])
    assert "Or declare parameter 0 of 'run' at a function type" in str(
        diagnostic["fix"])


def test_a_variable_met_below_the_head_is_refused_at_each_argument() -> None:
    """A generic's variable two closures give below the head of their
    arguments (`Some(...)`): no arm of the variable's join is an expression,
    so each argument is refused where it is passed, once."""
    source = _ALIASES + _fn(
        "second(@Option<T>, @Option<T> -> @Option<T>)", "@Option<T>.0"
    ).replace("private fn second", "private forall<T> fn second") + _fn(
        "main(@Int -> @Int)",
        "second(Some(fn(@Pos -> @Int) "
        "effects(pure) { @Pos.0 }), Some(fn(@Big -> @Int) effects(pure) "
        "{ @Big.0 }));\n  0", visibility="public")
    assert _codes(source) == ["E189", "E189"]


def test_never_and_a_variable_inside_a_function_type_still_fit() -> None:
    """The formal relation's other members: `Never` is below every type,
    so a `fn(Int -> Int)` fits `fn(Never -> Int)`; a type variable fits
    itself, so a generic's own `fn(@T -> @T)` fits `Endo<T>`."""
    source = (
        "type NeverToInt = fn(Never -> Int) effects(pure);\n"
        "type Endo<T> = fn(T -> T) effects(pure);\n\n"
        + _fn("twice(@T -> @T)",
              "let @Endo<T> = fn(@T -> @T) effects(pure) { @T.0 };\n"
              "  apply_fn(@Endo<T>.0, @T.0)").replace(
                  "private fn twice", "private forall<T> fn twice")
        + _fn("main(@Int -> @Int)",
              "let @NeverToInt = fn(@Int -> @Int) effects(pure) "
              "{ @Int.0 };\n  twice(@Int.0)", visibility="public"))
    assert _codes(source) == []
    assert pipeline.run(source, fn="main", args=[7]).execution.value == 7


def test_a_function_and_a_scalar_or_data_type_inside_do_not_meet() -> None:
    """Inside a function type, a function type where a scalar or a data
    type is: no narrowing, the `let`'s own E170."""
    for position, value in (
            ("fn(IntToInt -> Int)", "fn(@Int -> @Int) effects(pure) { 0 }"),
            ("fn(Option<Int> -> Int)",
             "fn(@IntToInt -> @Int) effects(pure) { 0 }")):
        source = (
            "type IntToInt = fn(Int -> Int) effects(pure);\n"
            f"type F = {position} effects(pure);\n\n"
            + _fn("main(@Int -> @Int)", f"let @F = {value};\n  0",
                  visibility="public"))
        assert _codes(source) == ["E170"], position
