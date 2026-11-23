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
same predicate.  Every flow refuses with E190, whose fix names the closure's
parameter type, the position's, and what gave the position its type.

The matrix is the flow (each place a function value meets a function type)
x the relation of the closure's parameter to the position's (narrower by a
refinement, by `Nat`, by predicate, wider only by implication, equal,
wider) x how the narrowness arises (a closure written in place, a slot bound
at its own function type, a refinement inside the parameter's type
argument).  A refused cell asserts E190 is the one error; an accepted cell
verifies with reconciliation and runs to the value it should.
"""

from __future__ import annotations

import json
import pathlib
import re
from collections.abc import Callable, Sequence
from dataclasses import dataclass

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/types.py", "vera/checker/core.py", "vera/checker/control.py",
    "vera/checker/calls.py", "vera/checker/expressions.py"])

_ALIASES = (
    "type Pos = { @Int | @Int.0 > 0 };\n"
    "type Big = { @Int | @Int.0 > 10 };\n"
)

_CONTRACT = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

#: The sentence every parameter's fix closes its rewrite with: E190 prints
#: no code for a closure written in place (spec §2.8).
_RENUMBER = (
    "Changing a parameter's type and binding the narrowed value both "
    "renumber the body's slot references of those two types: rewrite each "
    "to the binding it read before.")


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
    assert [d["error_code"] for d in diagnostics] == ["E190"], json.dumps(
        diagnostics, indent=1)[:2000]
    return diagnostics[0]


def _accepted(source: str, value: int) -> None:
    verified = pipeline.verify(source, reconcile=True)
    assert verified.ok, verified.diagnostics
    ran = pipeline.run(source, fn="main", args=[50])
    assert ran.trap is None, str(ran.trap)[:300]
    assert ran.execution.value == value


class _KnownVerdict(Exception):
    """An open issue's recorded verdict, still given: the one failure a
    strict xfail of this file expects (`raises=_KnownVerdict`)."""


def _known(got: list[str], *, known: list[str],
           fixed: Callable[[list[str]], bool]) -> None:
    """A strict xfail's verdict: return where *fixed* holds of the codes
    *got* (the issue is fixed, and the xfail reports an unexpected pass);
    raise `_KnownVerdict` where *got* is the issue's *known* verdict; and
    fail the test on any other, so an unrelated error is no xfail."""
    if fixed(got):
        return
    assert got == known, (got, known)
    raise _KnownVerdict(got)


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
        "hands it, and narrow inside with a `let`, where there is a value to "
        "check.  " + _RENUMBER + "  Or declare the binding at a function "
        "type whose parameter 0 is `Pos`.")
    assert diagnostic["spec_ref"] == 'Chapter 2, Section 2.8 "Subtyping Rules"'


def test_repro_a_nat_closure_at_an_int_type_is_refused_1885() -> None:
    """The silent member: the `@Nat` parameter held -5, with check and
    verify clean.  Also #1819's parameter line."""
    assert _codes(_NAT_LET) == ["E190"]


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
        "hands it, and narrow inside with a `let`, where there is a value to "
        "check.  " + _RENUMBER + "  Or pass argument 0 as `Array<Pos>`, "
        "which fixes `A` at `Pos`.")


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
    assert ("whether one implies the other is the verifier's to decide, of "
            "a value at a flow, and a function type's positions hold none"
            in str(diagnostic["description"]))


def test_repro_both_rewrites_the_fix_names_check_and_run_1885() -> None:
    """The two rewrites E190's fix gives for the generic route are programs
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
        "the position states; the closure's own return is then proved or "
        "checked, where the value is.  Or declare the binding at a function "
        "type whose result is `Int`.")


def test_repro_a_wider_result_at_a_nat_type_is_refused_1819() -> None:
    """Was silent: `main`, declared `-> @Nat`, returned -5, with check and
    verify clean."""
    assert _codes(_RESULT_NAT) == ["E190"]


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
    result the closure's own type fixes the variable.  So `array_map` over
    an `Array<Int>` with a `fn(@Nat -> @Int)` closure is accepted, and is
    sound: the instance is `Nat` by the polarity pin, the array is narrowed
    at the call (a `nat_bind` row, checked at run time where it is not
    proved), and a negative element traps there; a `Pos` closure, whose
    refinement no pin chooses, is E190."""
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
    "give (spec §5.9 rule B), #1891")


def _order_cell(flow: str, kind: str, form: str, p: str, c: str) -> bool:
    """A cell #1891's order decides: accepted, though refused by the
    relation table."""
    return ((flow, kind) == ("generic", "parameter")
            and form in ("in-place", "slot", "type-argument")
            and {p, c} == {"Pos", "Big"})


def _cell(flow: str, kind: str, form: str, p: str, c: str) -> object:
    cell = (flow, kind, form, p, c)
    if _order_cell(*cell):
        return pytest.param(*cell, id="-".join(cell), marks=pytest.mark.xfail(
            strict=True, raises=_KnownVerdict, reason=_ORDER_DECIDES))
    return pytest.param(*cell, id="-".join(cell))


CELLS = [_cell(flow, kind, form, p, c) for flow in FLOWS
         for kind in ("parameter", "result") for form in FORMS
         for p, c in PAIRS]


@pytest.mark.parametrize(("flow", "kind", "form", "p", "c"), CELLS)
def test_a_function_value_meets_a_function_type(
        flow: str, kind: str, form: str, p: str, c: str) -> None:
    source = program(flow, kind, form, p, c)
    if _order_cell(flow, kind, form, p, c):
        _known(_codes(source), known=[], fixed=lambda g: g == ["E190"])
    elif expected_refused(flow, kind, form, p, c):
        assert _codes(source) == ["E190"], source
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
_HELD_INSIDE = ("array-element", "tuple-element", "option")


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
        # Inside a value built around it (an element, a component), the
        # declaration to change holds the function type there.
        holding = ("a type holding, where this one sits, "
                   if flow in _HELD_INSIDE else "")
        assert (f"Or {declare} {holding}a function type whose parameter 0 "
                f"is `{spelt}`." in fix), (flow, fix)
        assert (", inside a value of type " in description) == (
            flow in _HELD_INSIDE), (flow, description)
        # A value that is not the closure itself (a join, a container) is
        # given its rewrites in prose: no code is printed for it.
        if flow in _BUILT_AROUND:
            assert "`fn(" not in fix, (flow, fix)
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
#: at a `let`: the `let`'s own mismatch, E170, never E190.
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
    # A mismatch below the head beside a narrowing: what is left once the
    # narrowings are set aside still differs, inside a type argument, a
    # function type's parameter or its result (`_narrowing_erased`).
    "another type argument beside a narrowing": (
        "type F = fn(Option<Int>, Int -> Int) effects(pure);\n\n",
        "fn(@Option<String>, @Pos -> @Int) effects(pure) { 0 }"),
    "another function parameter beside a narrowing": (
        "type IntToInt = fn(Int -> Int) effects(pure);\n"
        "type StrToInt = fn(String -> Int) effects(pure);\n"
        "type F = fn(IntToInt, Int -> Int) effects(pure);\n\n",
        "fn(@StrToInt, @Pos -> @Int) effects(pure) { 0 }"),
    "another function result beside a narrowing": (
        "type IntToInt = fn(Int -> Int) effects(pure);\n"
        "type IntToStr = fn(Int -> String) effects(pure);\n"
        "type F = fn(IntToInt, Int -> Int) effects(pure);\n\n",
        "fn(@IntToStr, @Pos -> @Int) effects(pure) { 0 }"),
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


#: A `String`-taking closure at each flow whose own mismatch E190 replaces
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
        assert "E190" not in _codes(source), flow


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
    assert _codes(source) == ["E190", "E190"]


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


# =====================================================================
# Inside a generic: the pair holds the enclosing function's variable
# =====================================================================

#: (position's parameter, value's parameter, position's result, value's
#: result): the four that fit only by a narrowing, one wider only by
#: implication, and three that fit.
GENERIC_RELATIONS = (
    ("Int", "Nat", "Int", "Int"), ("Int", "Pos", "Int", "Int"),
    ("Pos", "Big", "Int", "Int"), ("Int", "Int", "Nat", "Int"),
    ("Int", "Int", "Pos", "Int"), ("Int", "Int", "Int", "Int"),
    ("Nat", "Int", "Int", "Int"), ("Int", "Int", "Int", "Nat"))

#: Where the value meets `F2<T> = fn(P, T -> R)` inside `forall<T> fn
#: outer`: a call's argument (a `where` helper's, a generic callee's,
#: `apply_fn`'s) and a destructure's component, where a fit the pair's
#: variable makes is decided by the join (`_fits`), and the flows the
#: matrix above lists, here with the variable in the pair.
GENERIC_FLOWS = ("where-helper", "generic-callee", "apply-fn-argument",
                 "destructure", "let", "field", "option", "array-element",
                 "if-join", "match-join", "return")


def generic_program(flow: str, p: str, c: str, r: str, cr: str) -> str:
    """`main` calls `outer(true, 50)`, which applies a `F2<T>` built from a
    closure `fn(@c, @T -> @cr)` to its `Int` argument as a `p`."""
    body = "50" if cr == "Nat" else f"@{c}.0"
    v = f"fn(@{c}, @T -> @{cr}) effects(pure) {{ {body} }}"
    exact = f"fn(@{p}, @T -> @{r}) effects(pure) {{ 50 }}"
    bind = f"let @{p} = @Int.0;\n  " if p != "Int" else ""

    def apply(fn_value: str, var: str = "T") -> str:
        return f"apply_fn({fn_value}, @{p}.0, @{var}.0)"

    helpers, inner, where = "", "", ""
    if flow == "where-helper":
        inner = f"helper({v}, @T.0, @{p}.0)"
        where = ("where {\n  fn helper(@F2<T>, @T, @" + p + " -> @Int)\n"
                 "    requires(true)\n    ensures(true)\n    effects(pure)\n"
                 "  {\n    " + apply("@F2<T>.0") + "\n  }\n}\n")
    elif flow == "generic-callee":
        helpers = _fn(f"helper(@F2<U>, @U, @{p} -> @Int)",
                      apply("@F2<U>.0", "U")).replace(
                          "private fn helper", "private forall<U> fn helper")
        inner = f"helper({v}, @T.0, @{p}.0)"
    elif flow == "apply-fn-argument":
        helpers = "type UseF<T> = fn(F2<T> -> Int) effects(pure);\n\n"
        inner = (f"let @UseF<T> = fn(@F2<T> -> @Int) effects(pure) "
                 f"{{ {apply('@F2<T>.0')} }};\n  apply_fn(@UseF<T>.0, {v})")
    elif flow == "destructure":
        helpers = _fn("mk(@A -> @Tuple<A, Bool>)", "Tuple(@A.0, true)").replace(
            "private fn mk", "private forall<A> fn mk")
        inner = (f"let Tuple<@F2<T>, @Bool> = mk({v});\n  "
                 + apply("@F2<T>.0"))
    elif flow == "let":
        inner = f"let @F2<T> = {v};\n  " + apply("@F2<T>.0")
    elif flow == "field":
        helpers = "private data H<T> {\n  MkH(F2<T>)\n}\n\n"
        inner = (f"match MkH({v}) {{\n    MkH(@F2<T>) -> "
                 f"{apply('@F2<T>.0')}\n  }}")
    elif flow == "option":
        inner = (f"let @Option<F2<T>> = Some({v});\n  "
                 f"match @Option<F2<T>>.0 {{\n    Some(@F2<T>) -> "
                 f"{apply('@F2<T>.0')},\n    None -> 0\n  }}")
    elif flow == "array-element":
        inner = (f"let @Array<F2<T>> = [{v}];\n  "
                 + apply("@Array<F2<T>>.0[0]"))
    elif flow == "if-join":
        inner = (f"let @F2<T> = if @Int.0 > 100 then {{ {exact} }} "
                 f"else {{ {v} }};\n  " + apply("@F2<T>.0"))
    elif flow == "match-join":
        inner = (f"let @F2<T> = match @Int.0 > 100 {{\n    true -> {exact},"
                 f"\n    false -> {v}\n  }};\n  " + apply("@F2<T>.0"))
    elif flow == "return":
        helpers = _fn("mk(@T -> @F2<T>)", v).replace(
            "private fn mk", "private forall<T> fn mk")
        inner = "let @F2<T> = mk(@T.0);\n  " + apply("@F2<T>.0")
    else:
        raise AssertionError(flow)
    outer = (_fn("outer(@T, @Int -> @Int)", bind + inner,
                 requires="@Int.0 > 10")
             .replace("private fn outer", "private forall<T> fn outer"))
    if where:
        outer = outer.rstrip("\n") + "\n" + where + "\n"
    return (_ALIASES + f"type F2<T> = fn({p}, T -> {r}) effects(pure);\n\n"
            + helpers + outer
            + _fn("main(@Int -> @Int)", "outer(true, @Int.0)",
                  visibility="public", requires="@Int.0 > 10"))


GENERIC_CELLS = [
    pytest.param(flow, *rel, id="-".join((flow, *rel)))
    for flow in GENERIC_FLOWS for rel in GENERIC_RELATIONS]


@pytest.mark.parametrize(("flow", "p", "c", "r", "cr"), GENERIC_CELLS)
def test_a_function_value_meets_a_function_type_inside_a_generic(
        flow: str, p: str, c: str, r: str, cr: str) -> None:
    """The pair holds the enclosing generic's variable, so a call's
    argument and a destructure's component are fitted by the join, which
    compares a `Nat` beside an `Int` and a refinement beside its base by a
    relaxed rule of its own: a fit it gives is held to rule 9 (#1885,
    #1819), and E190 is what the site reports."""
    source = generic_program(flow, p, c, r, cr)
    if not (_le(p, c) and _le(cr, r)):
        assert _codes(source) == ["E190"], source
    else:
        _accepted(source, 50)


def test_repro_a_narrower_closure_at_a_generic_s_where_helper_1885() -> None:
    """The reported form: a `fn(@Nat, @T -> @Int)` closure passed to a
    `where` helper's `fn(Int, T -> Int)` parameter inside `forall<T> fn
    outer`, accepted while the join judged the fit, bound -5 to its `@Nat`
    parameter."""
    diagnostic = _only_diagnostic(
        generic_program("where-helper", "Int", "Nat", "Int", "Int"))
    assert "where parameter 0 of 'helper' gives it the type" in str(
        diagnostic["description"])


def test_repro_a_wider_result_at_a_generic_callee_1819() -> None:
    """The result direction through a generic callee: a `fn(@Int, @T ->
    @Int)` closure at `fn(Int, U -> Pos)`."""
    assert _codes(generic_program(
        "generic-callee", "Int", "Int", "Pos", "Int")) == ["E190"]


# =====================================================================
# Every form of the grammar that binds or admits a value
# =====================================================================

#: (position or result, the position's type, the value's type): the four
#: that fit only by a narrowing, then two that fit.
BINDING_RELATIONS = (
    ("parameter", "Int", "Nat"), ("parameter", "Int", "Pos"),
    ("result", "Nat", "Int"), ("result", "Pos", "Int"),
    ("parameter", "Nat", "Int"), ("result", "Int", "Nat"))

#: Each place `vera/grammar.lark` binds a value or admits one at a declared
#: type (`let_stmt`, `let_destruct`, `match_arm` and its patterns, a
#: handler's state, clause parameters and `with`, a call plain, piped and
#: `where`-scoped, `resume`, an effect operation, a constructor, a join, a
#: block, an index), each with a value `@G.0` of type `G` met at `F`.
BINDING_FORMS = (
    "let", "match-binder", "option-subpattern", "ctor-subpattern",
    "option-subpattern-of-slot", "tuple-subpattern", "nested-subpattern",
    "result-subpattern", "let-destructure", "let-destructure-slot",
    "result-payload", "piped-call", "where-helper", "exn-payload",
    "exn-clause-param", "state-clause-param", "state-resume",
    "user-op-argument", "user-op-clause-param", "user-op-resume",
    "adopted-generic-result", "adopted-apply-fn-result", "if-join-both",
    "block-tail", "array-index", "option-unwrap-or")

#: A user effect's operation over a function type is not lowered (E340):
#: the form's own refusal, beside the relation's.
_FORM_OWN_CODES = {"user-op-argument": {"E340"},
                   "user-op-clause-param": {"E340"},
                   "user-op-resume": {"E340"}}

#: A form that meets the value twice: `resume` hands the state's `get` the
#: value the handler's state is initialised with.
_E190_COUNT = {"state-resume": 2}


def _binding_types(kind: str, p: str, c: str, generic: bool) -> tuple[str, str]:
    """`F` and `G` (over the enclosing generic's `T` too, inside one), and
    a closure of type `G`."""
    t, tp = (", T", "<T>") if generic else ("", "")
    if kind == "parameter":
        lam = (f"fn(@{c}{', @T' if generic else ''} -> @Int) effects(pure) "
               f"{{ @{c}.0 }}")
        return (f"type F{tp} = fn({p}{t} -> Int) effects(pure);\n"
                f"type G{tp} = fn({c}{t} -> Int) effects(pure);\n", lam)
    body = "7" if c == "Nat" else "@Int.0"
    lam = (f"fn(@Int{', @T' if generic else ''} -> @{c}) effects(pure) "
           f"{{ {body} }}")
    return (f"type F{tp} = fn(Int{t} -> {p}) effects(pure);\n"
            f"type G{tp} = fn(Int{t} -> {c}) effects(pure);\n", lam)


def binding_form_program(form: str, kind: str, p: str, c: str,
                         generic: bool) -> str:
    """`main` (or, *generic*, `forall<T> fn outer`) binds a closure of type
    `G` to `@G` and meets `@G.0` at `F` by *form*, then applies the `F` it
    holds to its `Int` argument."""
    aliases, lam = _binding_types(kind, p, c, generic)
    f, g = ("F<T>", "G<T>") if generic else ("F", "G")
    tp, targ = ("<T>", ", @T.0") if generic else ("", "")
    g0 = f"@{g}.0"

    def app(fn_value: str) -> str:
        return f"apply_fn({fn_value}, @Int.0{targ})"

    def generic_fn(signature: str, body: str, variables: str,
                   requires: str = "true") -> str:
        return _fn(signature, body, requires=requires).replace(
            "private fn", f"private forall<{variables}> fn")

    use = app(f"@{f}.0")
    helpers = effect = where = ""
    if form == "let":
        body = f"let @{f} = {g0};\n  {use}"
    elif form == "match-binder":
        body = f"match {g0} {{\n    @{f} -> {use}\n  }}"
    elif form == "option-subpattern":
        body = (f"match Some({g0}) {{\n    Some(@{f}) -> {use},\n"
                f"    None -> 0\n  }}")
    elif form == "ctor-subpattern":
        helpers = f"private data H{tp} {{\n  MkH({g})\n}}\n\n"
        body = f"match MkH({g0}) {{\n    MkH(@{f}) -> {use}\n  }}"
    elif form == "option-subpattern-of-slot":
        body = (f"let @Option<{g}> = Some({g0});\n  match @Option<{g}>.0 {{\n"
                f"    Some(@{f}) -> {use},\n    None -> 0\n  }}")
    elif form == "tuple-subpattern":
        body = (f"match Tuple({g0}, true) {{\n    Tuple(@{f}, @Bool) -> "
                f"{use}\n  }}")
    elif form == "nested-subpattern":
        body = (f"let @Option<Tuple<{g}, Bool>> = Some(Tuple({g0}, true));\n"
                f"  match @Option<Tuple<{g}, Bool>>.0 {{\n"
                f"    Some(Tuple(@{f}, @Bool)) -> {use},\n    None -> 0\n  }}")
    elif form == "result-subpattern":
        body = (f"let @Result<{g}, Int> = Ok({g0});\n"
                f"  match @Result<{g}, Int>.0 {{\n"
                f"    Ok(@{f}) -> {use},\n    Err(@Int) -> 0\n  }}")
    elif form == "let-destructure":
        body = f"let Tuple<@{f}, @Bool> = Tuple({g0}, true);\n  {use}"
    elif form == "let-destructure-slot":
        body = (f"let @Tuple<{g}, Bool> = Tuple({g0}, true);\n"
                f"  let Tuple<@{f}, @Bool> = @Tuple<{g}, Bool>.0;\n  {use}")
    elif form == "result-payload":
        body = (f"let @Result<{f}, Int> = Ok({g0});\n"
                f"  match @Result<{f}, Int>.0 {{\n"
                f"    Ok(@{f}) -> {use},\n    Err(@Int) -> 0\n  }}")
    elif form == "piped-call":
        signature = f"run_f(@{f}, @Int{', @T' if generic else ''} -> @Int)"
        helpers = (generic_fn(signature, use, "T", "@Int.0 >= 0") if generic
                   else _fn(signature, use, requires="@Int.0 >= 0"))
        body = f"{g0} |> run_f(@Int.0{targ})"
    elif form == "where-helper":
        body = f"helper({g0}, @Int.0{targ})"
        where = (f"where {{\n  fn helper(@{f}, @Int"
                 f"{', @T' if generic else ''} -> @Int)\n"
                 "    requires(@Int.0 >= 0)\n    ensures(true)\n"
                 f"    effects(pure)\n  {{\n    {use}\n  }}\n}}\n")
    elif form == "exn-payload":
        body = (f"handle[Exn<{f}>] {{\n    throw(@{f}) -> {{ {use} }}\n"
                f"  }} in {{\n    throw({g0})\n  }}")
    elif form == "exn-clause-param":
        body = (f"handle[Exn<{g}>] {{\n    throw(@{f}) -> {{ {use} }}\n"
                f"  }} in {{\n    throw({g0})\n  }}")
    elif form == "state-clause-param":
        body = (f"handle[State<{g}>](@{g} = {g0}) {{\n"
                f"    get(@Unit) -> {{ resume(@{g}.0) }},\n"
                f"    put(@{f}) -> {{ resume(()) }} with @{g} = @{g}.0\n"
                f"  }} in {{\n    put({g0});\n    {app('get(())')}\n  }}")
    elif form == "state-resume":
        body = (f"handle[State<{f}>](@{f} = {g0}) {{\n"
                f"    get(@Unit) -> {{ resume({g0}) }},\n"
                f"    put(@{f}) -> {{ resume(()) }}\n"
                f"  }} in {{\n    {app('get(())')}\n  }}")
    elif form == "user-op-argument":
        effect = f"effect E{tp} {{\n  op take({f} -> Int);\n}}\n\n"
        body = (f"handle[E{tp}] {{\n    take(@{f}) -> {{ resume({use}) }}\n"
                f"  }} in {{\n    take({g0})\n  }}")
    elif form == "user-op-clause-param":
        effect = f"effect E{tp} {{\n  op take({g} -> Int);\n}}\n\n"
        body = (f"handle[E{tp}] {{\n    take(@{f}) -> {{ resume({use}) }}\n"
                f"  }} in {{\n    take({g0})\n  }}")
    elif form == "user-op-resume":
        effect = f"effect E{tp} {{\n  op mk(Unit -> {f});\n}}\n\n"
        body = (f"handle[E{tp}] {{\n    mk(@Unit) -> {{ resume({g0}) }}\n"
                f"  }} in {{\n    {app('mk(())')}\n  }}")
    elif form == "adopted-generic-result":
        helpers = generic_fn(f"mk(@{g} -> @Tuple<{g}, Option<U>>)",
                             f"Tuple(@{g}.0, None)",
                             "T, U" if generic else "U")
        body = (f"let @Tuple<{f}, Option<Int>> = mk({g0});\n"
                f"  match @Tuple<{f}, Option<Int>>.0 {{\n"
                f"    Tuple(@{f}, @Option<Int>) -> {use}\n  }}")
    elif form == "adopted-apply-fn-result":
        # `let @Tuple<W, Option<Int>> = apply_fn(make(()), ());`: the
        # expected type adopted by a function value's result.  Inside a
        # generic `make` takes a `T`, which fixes its variable.
        aliases += (f"type MkT{tp} = fn(Unit -> Tuple<{g}, Option<Int>>) "
                    "effects(pure);\n")
        made = (f"fn(@Unit -> @Tuple<{g}, Option<Int>>) effects(pure) "
                f"{{ Tuple({lam}, None) }}")
        helpers = (generic_fn(f"make(@T -> @MkT{tp})", made, "T") if generic
                   else _fn(f"make(@Unit -> @MkT{tp})", made))
        made_from = "@T.0" if generic else "()"
        body = (f"let @Tuple<{f}, Option<Int>> = apply_fn(make({made_from}), "
                f"());\n  match @Tuple<{f}, Option<Int>>.0 {{\n"
                f"    Tuple(@{f}, @Option<Int>) -> {use}\n  }}")
    elif form == "if-join-both":
        body = (f"let @{f} = if @Int.0 > 100 then {{ {g0} }} "
                f"else {{ {g0} }};\n  {use}")
    elif form == "block-tail":
        body = f"let @{f} = {{ {g0} }};\n  {use}"
    elif form == "array-index":
        body = (f"let @Array<{g}> = [{g0}];\n  let @{f} = @Array<{g}>.0[0];\n"
                f"  {use}")
    elif form == "option-unwrap-or":
        body = (f"let @{f} = option_unwrap_or(Some({g0}), {g0});\n  {use}")
    else:
        raise AssertionError(form)
    body = f"let @{g} = {lam};\n  {body}"
    if generic:
        outer = _fn("outer(@T, @Int -> @Int)", body,
                    requires="@Int.0 >= 0").replace(
                        "private fn", "private forall<T> fn")
        if where:
            outer = outer.rstrip("\n") + "\n" + where + "\n"
        main = _fn("main(@Int -> @Int)", "outer(true, @Int.0)",
                   visibility="public", requires="@Int.0 >= 0")
    else:
        outer = ""
        main = _fn("main(@Int -> @Int)", body, visibility="public",
                   requires="@Int.0 >= 0")
        if where:
            main = main.rstrip("\n") + "\n" + where + "\n"
    return _ALIASES + aliases + "\n" + effect + helpers + outer + main


def _binding_cell(form: str, generic: bool, kind: str, p: str,
                  c: str) -> object:
    cell_id = "-".join((form, "generic" if generic else "plain", kind, p, c))
    return pytest.param(form, generic, kind, p, c, id=cell_id)


BINDING_CELLS = [_binding_cell(form, generic, *rel)
                 for form in BINDING_FORMS for generic in (False, True)
                 for rel in BINDING_RELATIONS]


def test_repro_a_match_binder_at_a_stricter_function_type_is_refused_1819(
        ) -> None:
    """Was accepted: the binder `@W` took a `fn(Int -> Int)` value at
    `fn(Int -> Nat)`, and `t(-5)` gave -5 out of a `@Nat`, with check and
    verify clean.  A pattern is not the value: the fix prints no code."""
    source = (
        "type V = fn(Int -> Int) effects(pure);\n"
        "type W = fn(Int -> Nat) effects(pure);\n\n"
        + _fn("t(@Int -> @Int)",
              "let @V = fn(@Int -> @Int) effects(pure) { @Int.0 };\n"
              "  match @V.0 {\n    @W -> nat_to_int(apply_fn(@W.0, @Int.0))\n"
              "  }", visibility="public"))
    diagnostic = _only_diagnostic(source)
    assert diagnostic["description"] == (
        "A function value of type fn(Int -> Int) effects(pure) is used where "
        "the binding pattern gives it the type fn(Int -> Nat) effects(pure): "
        "its result is declared `Int`, and that type promises `Nat`, which a "
        "result declared `Int` does not guarantee.")
    assert diagnostic["fix"] == (
        "Declare the closure's result as `@Nat`, the type the position "
        "states; the closure's own return is then proved or checked, where "
        "the value is.  Or write the binding pattern at a function type "
        "whose result is `Int`.")


@pytest.mark.parametrize(("form", "generic", "kind", "p", "c"), BINDING_CELLS)
def test_every_binding_form_meets_a_function_type(
        form: str, generic: bool, kind: str, p: str, c: str) -> None:
    """Every form of the grammar that binds a value or admits one at a
    declared type, outside a generic and inside one: a pair that fits only
    by a narrowing is E190 (with the form's own refusal, where the form has
    one), and a pair that fits checks clean and verifies.  A judge the
    function-type rule does not reach is a failing cell here."""
    source = binding_form_program(form, kind, p, c, generic)
    refused = not (_le(p, c) if kind == "parameter" else _le(c, p))
    own = _FORM_OWN_CODES.get(form, set())
    # A clause parameter is held to the operation's type (#1896), a user
    # effect's beside its handler's E340.
    assert sorted(_codes(source)) == sorted(
        ["E190"] * _E190_COUNT.get(form, 1) * refused + list(own)), source
    if not refused and not own:
        verified = pipeline.verify(source, reconcile=True)
        assert verified.ok, (verified.diagnostics, source)


# =====================================================================
# The fix reads back: the wrapper E190 prints checks where it is pasted
# =====================================================================

#: Parameter lists of a stored `fn(... -> Int)` met at `fn(... -> Nat)`:
#: (the type's parameters, the closure's declared parameters, whether the
#: fix gives a wrapper).  A function-typed parameter has no slot name to
#: write and a `Future<Unit>` no local to read, so neither has a wrapper.
_READ_BACK = {
    "none": ("", "", True),
    "one": ("Int", "@Int", True),
    "two-of-one-type": ("Int, Int", "@Int, @Int", True),
    "a-unit-alone": ("Unit", "@Unit", True),
    "a-unit-among-others": ("Int, Unit, Int", "@Int, @Unit, @Int", True),
    "a-refined-one": ("Pos", "@Pos", True),
    "a-refined-unit": ("U", "@U", True),
    "a-function-typed-one": ("IntToInt, Int", "@IntToInt, @Int", False),
    "a-future-unit": ("Future<Unit>", "@Future<Unit>", False),
}


def _stored(types: str, declared: str, value: str) -> str:
    return (_ALIASES + "type IntToInt = fn(Int -> Int) effects(pure);\n"
            "type U = { @Unit | true };\n"
            f"type V = fn({types} -> Int) effects(pure);\n"
            f"type W = fn({types} -> Nat) effects(pure);\n\n"
            + _fn("main(@Int -> @Int)",
                  f"let @V = fn({declared} -> @Int) effects(pure) {{ 0 }};\n"
                  f"  let @W = {value};\n  0", visibility="public"))


@pytest.mark.parametrize("shape", list(_READ_BACK))
def test_repro_the_wrapper_e190_prints_checks_pasted_back_1819(
        shape: str) -> None:
    """The wrapper E190's fix prints for a value in a slot, pasted where
    the value was, checks: a `Unit` parameter is passed as `()`, since it
    has no local to read (E182), and its declaration keeps the other
    slots' indices.  Where no wrapper would check, none is printed, and the
    fix keeps its other rewrites."""
    types, declared, wrapped = _READ_BACK[shape]
    fix = str(_only_diagnostic(_stored(types, declared, "@V.0"))["fix"])
    found = re.findall(r"`(fn\([^`]*\{ apply_fn\(@V\.0[^`]*\})`", fix)
    if not wrapped:
        assert found == [], fix
        assert "Declare the closure's result as `@Nat`" in fix, fix
        return
    assert len(found) == 1, fix
    assert _codes(_stored(types, declared, found[0])) == [], found[0]
    if shape in _READ_BACK_EXACT:
        assert found[0] == _READ_BACK_EXACT[shape], found[0]


#: The wrappers whose slots a wrong index or a wrong name would still let
#: check: each reads its parameters in order, the most recent `@Int.0`.
_READ_BACK_EXACT = {
    "two-of-one-type": ("fn(@Int, @Int -> @Nat) effects(pure) "
                        "{ apply_fn(@V.0, @Int.1, @Int.0) }"),
    "a-unit-among-others": ("fn(@Int, @Unit, @Int -> @Nat) effects(pure) "
                            "{ apply_fn(@V.0, @Int.1, (), @Int.0) }"),
    "a-refined-one": ("fn(@{ @Int | @Int.0 > 0 } -> @Nat) effects(pure) "
                      "{ apply_fn(@V.0, @Int.0) }"),
}


def test_repro_the_wrapper_writes_an_effect_row_over_a_type_parameter_1819(
        ) -> None:
    """Inside a generic, a stored function value whose effect row names
    the enclosing function's type parameter: the wrapper writes the row as
    the program does, and checks pasted back."""
    def source(value: str) -> str:
        return (
            "type V<T> = fn(Int -> Int) effects(<State<T>>);\n"
            "type W<T> = fn(Int -> Nat) effects(<State<T>>);\n\n"
            "private forall<T> fn f(@T -> @Int)\n  requires(true)\n"
            "  ensures(true)\n  effects(<State<T>>)\n{\n"
            "  let @V<T> = fn(@Int -> @Int) effects(<State<T>>) { 0 };\n"
            f"  let @W<T> = {value};\n  0\n}}\n\n"
            + _fn("main(@Int -> @Int)", "0", visibility="public"))
    fix = str(_only_diagnostic(source("@V<T>.0"))["fix"])
    wrapper = ("fn(@Int -> @Nat) effects(<State<T>>) "
               "{ apply_fn(@V<T>.0, @Int.0) }")
    assert f"`{wrapper}`" in fix, fix
    assert _codes(source(wrapper)) == []


# =====================================================================
# The text E190 prints, pasted: a generator over parameter lists
# =====================================================================

#: The alphabet of a function type's parameters: (how a parameter of that
#: type is written, the slot it is read by, by DE_BRUIJN.md's rule written
#: out here: an alias by its name, a refinement written in place by its
#: base, a data type by its head and arguments, the argument `main` passes,
#: whether the body reads it as a number).
_ALPHABET = {
    "Int": ("Int", "Int", None, True),
    "Bool": ("Bool", "Bool", "true", False),
    "Pos": ("Pos", "Pos", None, True),
    "inline": ("{ @Int | @Int.0 > 0 }", "Int", None, True),
    "Nat": ("Nat", "Nat", None, True),
    "Unit": ("Unit", "Unit", "()", False),
    "Option": ("Option<Int>", "Option<Int>", "Some(5)", False),
    "Fn": ("IntToInt", "IntToInt", "fn(@Int -> @Int) effects(pure) { @Int.0 }",
           False),
}

#: Unequal numbers for the numeric parameters, by position, and the
#: weights the body gives them, a subtraction among them: two slots read
#: in each other's place change the value.
_VALUES = (100, 7, 3)
_WEIGHTS = (1, -2, 3)


def _lists() -> list[tuple[str, ...]]:
    """Every list of one or two letters, and every list of three over the
    letters that share a slot name or have no value to read."""
    letters = list(_ALPHABET)
    out: list[tuple[str, ...]] = [(a,) for a in letters]
    out += [(a, b) for a in letters for b in letters]
    three = ("Int", "Pos", "Unit", "inline")
    out += [(a, b, c) for a in three for b in three for c in three]
    return out


def _reads(params: list[str]) -> list[str]:
    """Each parameter's slot reference, DE_BRUIJN.md's rule: the index
    counts the parameters after it read by the same name."""
    slots = [_ALPHABET[p][1] if p in _ALPHABET else p for p in params]
    return [f"@{s}.{slots[j + 1:].count(s)}" for j, s in enumerate(slots)]


def _body(params: list[str], reads: list[str]) -> str:
    """1000 plus each numeric parameter at its weight: a positive number
    that changes when two parameters are read in each other's place."""
    terms = ["1000"]
    for j, p in enumerate(params):
        if _ALPHABET.get(p, ("", "", None, True))[3]:
            terms.append(f"{_WEIGHTS[j]} * {reads[j]}")
    return " + ".join(terms)


def _expected(params: list[str]) -> int:
    return 1000 + sum(_WEIGHTS[j] * _VALUES[j] for j, p in enumerate(params)
                      if _ALPHABET[p][3])


def _fix_program(params: list[str], kind: str, narrowed: int | None,
                 form: str, value: str | None = None) -> str:
    """A function type `F` over *params* (the result `Nat` where the
    result is the narrowed position), and a closure narrower at parameter
    *narrowed* (declared `Pos` where `F` has `Int`) or wider in its result
    (declared `Int`), written in place or held in a slot at its own type
    `G`; `main` applies the value of `F` to unequal arguments.  *value*
    replaces the value `F` is bound to."""
    written = [_ALPHABET[p][0] for p in params]
    closure = list(written)
    if kind == "parameter":
        assert narrowed is not None
        closure[narrowed] = "Pos"
    result = "Nat" if kind == "result" else "Int"
    closure_result = "Int"
    reads = _reads([("Pos" if kind == "parameter" and j == narrowed else p)
                    for j, p in enumerate(params)])
    lit = (f"fn({', '.join('@' + t for t in closure)} -> @{closure_result}) "
           f"effects(pure) {{ {_body(params, reads)} }}")
    args = [str(_VALUES[j]) if _ALPHABET[p][2] is None else str(_ALPHABET[p][2])
            for j, p in enumerate(params)]
    aliases = (_ALIASES
               + "type IntToInt = fn(Int -> Int) effects(pure);\n"
               + f"type F = fn({', '.join(written)} -> {result}) effects(pure);\n"
               + f"type G = fn({', '.join(closure)} -> {closure_result}) "
                 "effects(pure);\n\n")
    if value is None:
        value = lit if form == "in-place" else "@G.0"
    pre = "" if form == "in-place" else f"let @G = {lit};\n  "
    return aliases + _fn(
        "main(@Int -> @Int)",
        f"{pre}let @F = {value};\n  apply_fn(@F.0, {', '.join(args)})",
        visibility="public")


def _fix_cells() -> list[object]:
    cells: list[object] = []
    for params in _lists():
        for form in ("in-place", "slot"):
            cells.append(pytest.param(params, "result", None, form,
                                      id=f"{'-'.join(params)}-result-{form}"))
            for i, p in enumerate(params):
                if p == "Int":
                    cells.append(pytest.param(
                        params, "parameter", i, form,
                        id=f"{'-'.join(params)}-parameter{i}-{form}"))
    return cells


def _ran(source: str) -> int:
    assert _codes(source) == [], source
    ran = pipeline.run(source, fn="main", args=[0])
    assert ran.trap is None, (str(ran.trap)[:300], source)
    return int(ran.execution.value)


@pytest.mark.parametrize(("params", "kind", "narrowed", "form"), _fix_cells())
def test_every_rewrite_e190_prints_checks_and_runs_pasted(
        params: tuple[str, ...], kind: str, narrowed: int | None,
        form: str) -> None:
    """The code E190's fix prints is the wrapper of a value held in a slot
    alone, and pasted it checks and gives the value the original function
    gives on unequal arguments: the wrapper reads each parameter by the
    compiler's slot rule, so a slot read in another's place changes the
    value, and a `Unit` or another type between two parameters of one type
    shifts nothing.  A closure written in place is given prose and no
    code, whatever its parameter list: nothing here rebuilds a body."""
    plist = list(params)
    source = _fix_program(plist, kind, narrowed, form)
    fix = str(_only_diagnostic(source)["fix"])
    expected = _expected(plist)
    if form == "in-place":
        # Written in place, the rewrites are prose: no header is printed
        # around a body the reader keeps, whose slot references it would
        # renumber.
        assert not re.search(r"`fn\(", fix), fix
        if kind == "parameter":
            assert f"parameter {narrowed} as `@Int`" in fix, fix
            assert _RENUMBER in fix, fix
        else:
            assert "Declare the closure's result as `@Nat`" in fix, fix
        return
    # Held in a slot, the wrapper alone is code: it applies the value, and
    # nothing of the reader's is pasted into it.  Pasted, it checks and
    # gives the original function's value on unequal arguments.
    wrapper = re.findall(r"`(fn\([^`]*\{ apply_fn\(@G\.0[^`]*\})`", fix)
    assert len(re.findall(r"`fn\(", fix)) == len(wrapper), fix
    if "Fn" in plist:
        # A function-typed parameter is not written out in a header
        # (`@fn(Int -> Int) effects(pure)` does not parse): no wrapper.
        assert wrapper == [], fix
        return
    assert len(wrapper) == 1, fix
    assert _ran(_fix_program(plist, kind, narrowed, "slot",
                             wrapper[0])) == expected, wrapper[0]


# =====================================================================
# Every rewrite every refused cell prints, pasted where the value is
# =====================================================================

def _refused_cells() -> list[object]:
    """Every refused cell of the three matrices above: the program, the
    closure the cell writes (whose body a rewrite's `...` stands for), and
    the type the closure's own narrowed parameter is read by there."""
    cells: list[object] = []
    for flow in FLOWS:
        for kind in ("parameter", "result"):
            for form in FORMS:
                for p, c in PAIRS:
                    if expected_refused(flow, kind, form, p, c):
                        # The order cells (#1891) are accepted: no E190.
                        order = _order_cell(flow, kind, form, p, c)
                        cells.append(pytest.param(
                            "flows", (flow, kind, form, p, c), c,
                            id="-".join(("flows", flow, kind, form, p, c)),
                            marks=[pytest.mark.xfail(
                                strict=True, raises=_KnownVerdict,
                                reason=_ORDER_DECIDES)]
                            if order else []))
    for flow in GENERIC_FLOWS:
        for p, c, r, cr in GENERIC_RELATIONS:
            if not (_le(p, c) and _le(cr, r)):
                cells.append(pytest.param(
                    "generic", (flow, p, c, r, cr), c,
                    id="-".join(("generic", flow, p, c, r, cr))))
    for form in BINDING_FORMS:
        for generic in (False, True):
            for kind, p, c in BINDING_RELATIONS:
                if not (_le(p, c) if kind == "parameter" else _le(c, p)):
                    cells.append(pytest.param(
                        "binding", (form, kind, p, c, generic), c,
                        id="-".join(("binding", form,
                                     "generic" if generic else "plain",
                                     kind, p, c))))
    return cells


def _source_of(matrix: str, cell: tuple[object, ...]) -> str:
    if matrix == "flows":
        return program(*cell)  # type: ignore[arg-type]
    if matrix == "generic":
        return generic_program(*cell)  # type: ignore[arg-type]
    return binding_form_program(*cell)  # type: ignore[arg-type]


def _span_at(source: str, start: int) -> tuple[int, int]:
    """The span of the value at *start*: a closure, to the brace that
    closes its body, or a slot reference."""
    if source.startswith("fn(", start):
        depth = 0
        for at in range(source.index("{", start), len(source)):
            depth += {"{": 1, "}": -1}.get(source[at], 0)
            if depth == 0:
                return start, at + 1
    found = re.match(r"@[\w<>, ]+\.\d+", source[start:])
    assert found is not None, source[start:start + 40]
    return start, start + found.end()


def _closure_of(source: str, value: str) -> str:
    """The closure *value* is: itself, or the one its slot is bound to."""
    if value.startswith("fn("):
        return value
    bound = source.index(f"let {value[:value.rindex('.')]} = ") + len(
        f"let {value[:value.rindex('.')]} = ")
    start, end = _span_at(source, bound)
    return source[start:end]


@pytest.mark.parametrize(("matrix", "cell", "declared"), _refused_cells())
def test_every_rewrite_a_refused_cell_prints_checks_pasted(
        matrix: str, cell: tuple[object, ...], declared: str) -> None:
    """Every rewrite written as code in the fix of every refused cell of
    the matrices above (a closure header with its narrowing or its result,
    and a wrapper), pasted in place of the value E190 is placed at, checks
    with no error but the form's own and the other sites' E190.  The
    `...` of a header is the
    closure's own body, its narrowed parameter read by the narrowing's
    slot.  A cell whose fix prints no code is prose, which pastes
    nothing."""
    source = _source_of(matrix, cell)
    own = (_FORM_OWN_CODES.get(str(cell[0]), set()) if matrix == "binding"
           else set())
    errors = pipeline.check(source).errors
    refused = [d for d in errors if d.error_code == "E190"]
    # Every refused cell is E190 before anything is replayed, a clause
    # parameter's among them (#1896).
    if matrix == "flows" and _order_cell(*cell):  # type: ignore[arg-type]
        # The whole verdict, not the E190s alone: an unrelated error
        # is no xfail.
        _known([d.error_code for d in errors], known=[],
               fixed=lambda g: g == ["E190"])
    assert refused, (matrix, cell)
    for diagnostic in refused:
        rewrites = re.findall(r"`(fn\([^`]*\})`", diagnostic.fix)
        if not rewrites:
            continue
        line, column = diagnostic.location.line, diagnostic.location.column
        assert line is not None and column is not None
        start, end = _span_at(source, sum(
            len(text) + 1 for text in source.split("\n")[:line - 1])
            + column - 1)
        closure = _closure_of(source, source[start:end])
        for rewrite in rewrites:
            if " ... }" in rewrite:
                body = closure[closure.index("{ ") + 2:closure.rindex(" }")]
                narrowing = re.search(
                    r"let @(\{ @(\w+) \|[^}]*\}|[\w<>]+) = ", rewrite)
                if narrowing is not None:
                    body = body.replace(
                        f"@{declared}.0",
                        f"@{narrowing.group(2) or narrowing.group(1)}.0")
                rewrite = rewrite.replace(" ... }", f" {body} }}")
            pasted = source[:start] + rewrite + source[end:]
            # The value's E190 is gone, and nothing else is reported: a
            # form that meets the value at two sites keeps the other's.
            left = [code for code in _codes(pasted) if code not in own]
            assert left == ["E190"] * (len(refused) - 1), (rewrite, pasted)


#: The three shapes whose rewrite no generator pastes, each given its fix
#: in prose: a component of a destructured value, a function-typed part,
#: and a pair below the root of the value's type.
_DESTRUCTURED = (
    "type F = fn(Int -> Nat) effects(pure);\n"
    "type G = fn(Int -> Int) effects(pure);\n\n"
    + _fn("main(@Int -> @Int)",
          "let @G = fn(@Int -> @Int) effects(pure) { @Int.0 };\n"
          "  let @Tuple<G, Bool> = Tuple(@G.0, true);\n"
          "  let Tuple<@F, @Bool> = @Tuple<G, Bool>.0;\n"
          "  nat_to_int(apply_fn(@F.0, @Int.0))", visibility="public"))

_FUNCTION_TYPED_PART = (
    "type Strict = fn(Int -> Nat) effects(pure);\n"
    "type Loose = fn(Int -> Int) effects(pure);\n"
    "type F = fn(Loose -> Int) effects(pure);\n\n"
    + _fn("main(@Int -> @Int)",
          "let @F = fn(@Strict -> @Int) effects(pure) "
          "{ nat_to_int(apply_fn(@Strict.0, 1)) };\n"
          "  apply_fn(@F.0, fn(@Int -> @Int) effects(pure) { @Int.0 })",
          visibility="public"))

_NESTED_IN_A_GENERIC = (
    "type In = fn(Int -> Int) effects(pure);\n"
    "type NIn = fn(Nat -> Int) effects(pure);\n"
    "type Cb<T> = fn(T -> In) effects(pure);\n\n"
    + _fn("use(@Cb<T>, @T -> @Int)",
          "apply_fn(apply_fn(@Cb<T>.0, @T.0), -5)").replace(
              "private fn use", "private forall<T> fn use")
    + _fn("main(@Int -> @Int)",
          "use(fn(@Int -> @NIn) effects(pure) "
          "{ fn(@Nat -> @Int) effects(pure) { @Nat.0 } }, @Int.0)",
          visibility="public"))


def test_repro_a_destructured_component_is_given_no_wrapper_1885() -> None:
    """The wrapper was written around the destructured tuple's slot,
    `apply_fn(@Tuple<G, Bool>.0, @Int.0)`, which pasted is E202: the
    value E190 is placed at holds the function, and is not it."""
    fix = str(_only_diagnostic(_DESTRUCTURED)["fix"])
    assert "apply_fn" not in fix and "`fn(" not in fix, fix
    assert fix == (
        "Declare the closure's result as `@Nat`, the type the position "
        "states; the closure's own return is then proved or checked, where "
        "the value is.  Or write binding 1 at a function type whose result "
        "is `Int`.")


def test_repro_a_function_typed_part_is_adapted_in_prose_1885() -> None:
    """The header spliced the position's function type in place of the
    closure's `@Strict` and narrowed it by `let @Strict = ...`, which is
    the narrowing of a function value E190 refuses: the fix says to apply
    the function value inside and narrow what it returns."""
    fix = str(_only_diagnostic(_FUNCTION_TYPED_PART)["fix"])
    assert "`fn(" not in fix.replace("`fn(Int -> Int) effects(pure)`", "")
    assert "let @" not in fix, fix
    assert fix == (
        "Declare the closure's parameter 0 at `fn(Int -> Int) effects(pure)`"
        ", the type the position hands it.  A function value is narrowed "
        "nowhere: where the closure needs more of it than that type states, "
        "apply it inside and narrow what it returns, where there is a value "
        "to check.  Or declare the binding at a function type whose "
        "parameter 0 is `Strict`.")


def test_repro_a_nested_pair_names_no_outer_variable_1885() -> None:
    """The nested pair's parameter index named the outer generic's `T`
    (`pass argument 1 as Nat`, which pasted is E190 again), and its header
    replaced the outer closure (E202).  The description names the value
    the pair sits in, and the fix is prose."""
    diagnostic = _only_diagnostic(_NESTED_IN_A_GENERIC)
    description, fix = str(diagnostic["description"]), str(diagnostic["fix"])
    assert description.startswith(
        "A function value of type fn(Nat -> Int) effects(pure), inside a "
        "value of type fn(Int -> fn(Nat -> Int) effects(pure)) effects(pure), "
        "is used where parameter 0 of 'use' gives it the type fn(Int -> Int) "
        "effects(pure)"), description
    assert "instantiated" not in description, description
    assert fix == (
        "Declare the closure's parameter 0 as `@Int`, the type the position "
        "hands it, and narrow inside with a `let`, where there is a value to "
        "check.  " + _RENUMBER + "  Or declare parameter 0 of 'use' at a "
        "type holding, where this one sits, a function type whose parameter "
        "0 is `Nat`.")


def test_repro_each_element_of_an_array_is_reported_once_1885() -> None:
    """Two stored callbacks of two refinements at `Array<F>`: the join of
    the elements was E190 at element 0, then each element E162 against
    the join, three reports for two elements.  Each element is now held
    to the join once, and is E190."""
    source = _ALIASES + (
        "type FP = fn(Pos -> Int) effects(pure);\n"
        "type FB = fn(Big -> Int) effects(pure);\n"
        "type F = fn(Int -> Int) effects(pure);\n\n") + _fn(
        "main(@Int -> @Int)",
        "let @FP = fn(@Pos -> @Int) effects(pure) { @Pos.0 };\n"
        "  let @FB = fn(@Big -> @Int) effects(pure) { @Big.0 };\n"
        "  let @Array<F> = [@FP.0, @FB.0];\n"
        "  apply_fn(@Array<F>.0[0], @Int.0)", visibility="public")
    diagnostics = pipeline.check(source).errors
    assert [(d.error_code, d.location.column) for d in diagnostics] == [
        ("E190", 20), ("E190", 27)], [d.description for d in diagnostics]
    assert all("where the literal's element type, the join of its "
               "elements, gives it the type fn(Int -> Int) effects(pure)"
               in d.description for d in diagnostics)


# =====================================================================
# A built-in's lost variable beside a function pair (`_fits`, #1688)
# =====================================================================

#: `first([])` types nothing, so `array_map`'s `B` is lost (#1688): the
#: fit the join cannot give keeps the verdict `_compatible_modulo_typevars`
#: gives, whose leaves compare either way.
_LOST = "array_map([1], first([]))[0]"

#: (the position's function type, the value's function, refused).
_LOST_PAIRS = (
    ("fn(Int -> Int)", "fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }",
     True),
    ("fn(Int -> Nat)", "fn(@Int -> @Int) effects(pure) { @Int.0 }", True),
    ("fn(Nat -> Int)", "fn(@Int -> @Int) effects(pure) { @Int.0 }", False),
    ("fn(Int -> Int)", "fn(@Int -> @Nat) effects(pure) { 7 }", False),
)

_LOST_SITES = {
    "argument": "take(Tuple({lost}, {value}))",
    "array-element": ("let @Array<Tuple<Int, F>> = [Tuple(0, {exact}), "
                      "Tuple({lost}, {value})];\n  0"),
    "array-join": ("array_length([Tuple(0, {exact}), "
                   "Tuple({lost}, {value})])"),
    # A generic call's result adopted at the type its `let` expects
    # (`_synth_fn_call`).
    "adopted-generic": ("let @Tuple<Int, F> = first([Tuple({lost}, "
                        "{value})]);\n  0"),
    "adopted-identity": "let @Tuple<Int, F> = idt(Tuple({lost}, {value}));\n  0",
}


def _lost_program(site: str, position: str, value: str) -> str:
    params = position.removeprefix("fn(").split(" -> ")
    exact = (f"fn(@{params[0]} -> @{params[1].rstrip(')')}) effects(pure) "
             + ("{ 7 }" if params[1].startswith("Nat") else
                f"{{ {'nat_to_int(@Nat.0)' if params[0] == 'Nat' else '@Int.0'} }}"))
    return (f"type F = {position} effects(pure);\n\n"
            "private forall<T> fn first(@Array<T> -> @T)\n"
            "  requires(array_length(@Array<T>.0) > 0)\n  ensures(true)\n"
            "  effects(pure)\n{\n  @Array<T>.0[0]\n}\n\n"
            + _fn("idt(@A -> @A)", "@A.0").replace(
                "private fn", "private forall<A> fn")
            + _fn("take(@Tuple<Int, F> -> @Int)", "0")
            + _fn("main(@Int -> @Int)", _LOST_SITES[site].format(
                lost=_LOST, value=value, exact=exact), visibility="public"))


@pytest.mark.parametrize(("site", "position", "value", "refused"), [
    pytest.param(site, position, value, refused,
                 id=f"{site}-{position}-{value.split(' {')[0]}")
    for site in _LOST_SITES for position, value, refused in _LOST_PAIRS])
def test_a_lost_builtin_variable_beside_a_function_pair_is_held_to_rule_9(
        site: str, position: str, value: str, refused: bool) -> None:
    """`_fits`' built-in branch held a pair whose join failed at a lost
    variable to `_compatible_modulo_typevars` alone, so a
    `Tuple<B, fn(Nat -> Int)>` fitted a `Tuple<Int, fn(Int -> Int)>`
    parameter, and a generic call's result was adopted at that expected
    type, which the `let` then compared with itself; both are held to rule
    9 as the join's fit is."""
    codes = _codes(_lost_program(site, position, value))
    assert codes == (["E190"] if refused else []), codes


# =====================================================================
# A module's function, called qualified and bare
# =====================================================================

_MODULE = (
    "module w85lib;\n\n"
    "type F = fn(Int -> Int) effects(pure);\n"
    "type FN = fn(Int -> Nat) effects(pure);\n"
    "type GP<T> = fn(T -> Int) effects(pure);\n\n"
    + _fn("run_f(@F, @Int -> @Int)", "apply_fn(@F.0, @Int.0)",
          visibility="public")
    + _fn("run_n(@FN, @Int -> @Nat)", "apply_fn(@FN.0, @Int.0)",
          visibility="public")
    + _fn("app(@GP<T>, @T -> @Int)", "apply_fn(@GP<T>.0, @T.0)",
          visibility="public").replace("public fn", "public forall<T> fn"))

#: (the call `main` makes, refused).
_MODULE_CALLS = (
    ("w85lib::run_f(fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }, "
     "@Int.0)", True),
    ("run_f(fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }, @Int.0)",
     True),
    ("nat_to_int(w85lib::run_n(fn(@Int -> @Int) effects(pure) { @Int.0 }, "
     "@Int.0))", True),
    ("w85lib::app(fn(@Pos -> @Int) effects(pure) { @Pos.0 }, @Int.0)", True),
    ("w85lib::run_f(fn(@Int -> @Int) effects(pure) { @Int.0 }, @Int.0)",
     False),
    ("nat_to_int(w85lib::run_n(fn(@Int -> @Nat) effects(pure) { 7 }, "
     "@Int.0))", False),
)


@pytest.mark.parametrize(("call", "refused"), [
    pytest.param(call, refused, id=f"call{i}")
    for i, (call, refused) in enumerate(_MODULE_CALLS)])
def test_a_module_s_function_meets_a_closure(
        tmp_path: pathlib.Path, call: str, refused: bool) -> None:
    """A closure passed to an imported module's function, by its qualified
    name and by its bare one, a generic one among them: the call's own
    judge, E190 where it fits only by a narrowing."""
    (tmp_path / "w85lib.vera").write_text(_MODULE, encoding="utf-8")
    main = tmp_path / "main.vera"
    main.write_text("import w85lib;\n\n" + _ALIASES + "\n" + _fn(
        "main(@Int -> @Int)", call, visibility="public"), encoding="utf-8")
    codes = [d.error_code for d in pipeline.check(main).errors]
    assert codes == (["E190"] if refused else []), codes


# =====================================================================
# The rest of the pair: E190 only where the narrowing is the one misfit
# =====================================================================

_OTHER_COMPONENT_TAKE = (
    "type F = fn(Int -> Int) effects(pure);\n\n"
    + _fn("take(@Tuple<Bool, F> -> @Int)", "0")
    + _fn("main(@Int -> @Int)",
          "take(Tuple(FIRST, fn(@Nat -> @Int) effects(pure) "
          "{ nat_to_int(@Nat.0) }))", visibility="public"))

_OTHER_COMPONENT_LET = (
    "type F = fn(Int -> Int) effects(pure);\n\n"
    + _fn("main(@Int -> @Int)",
          "let @Tuple<Bool, F> = Tuple(FIRST, fn(@Nat -> @Int) "
          "effects(pure) { nat_to_int(@Nat.0) });\n  0",
          visibility="public"))


def test_repro_another_component_keeps_the_flow_s_own_code_1885() -> None:
    """A `String` beside a narrower closure where a `Tuple<Bool, F>` is
    expected: the pair does not fit with the narrowing set aside, so the
    flow's own mismatch is reported (E202 at a call's argument, E170 at a
    `let`), as at main.  With the `String` mended, the narrowing is the
    one misfit, and E190."""
    for template, own in ((_OTHER_COMPONENT_TAKE, "E202"),
                          (_OTHER_COMPONENT_LET, "E170")):
        assert _codes(template.replace("FIRST", '"s"')) == [own], own
        assert _codes(template.replace("FIRST", "true")) == ["E190"], own


def test_repro_a_binder_beside_another_misfit_is_its_own_e314_1885(
        ) -> None:
    """A `match` binder holds its value to `is_subtype` (#1896), so a
    `Tuple<IOF, G>` scrutinee at `@Tuple<W, F>`, whose first component
    misfits by its effect row, is the binder's own E314, as a `let` of it
    is its own E170: E190 stands where the narrowing is the one misfit."""
    source = (
        "type IOF = fn(Int -> Int) effects(<IO>);\n"
        "type W = fn(Int -> Int) effects(pure);\n"
        "type G = fn(Nat -> Int) effects(pure);\n"
        "type F = fn(Int -> Int) effects(pure);\n\n"
        + _fn("main(@Tuple<IOF, G> -> @Int)",
              "match @Tuple<IOF, G>.0 {\n    @Tuple<W, F> -> 0\n  }",
              visibility="public"))
    assert _codes(source) == ["E314"]


# =====================================================================
# A closure written in place: its rewrites are prose, its body kept
# =====================================================================

#: (the position, the closure as the program writes it, the parameters the
#: fix must name).  Each kept body reads a slot a rewritten header would
#: renumber: another parameter of the type the changed one takes, a
#: capture, a later parameter of the narrowed type itself (`@Pos.1`, the
#: second `Pos`, which a `let @Pos` would make the third), a `Nat` the
#: narrowing's `let @Nat` would shadow, and a second unfit parameter and a
#: result a first rewrite left unfit.
_IN_PLACE = {
    "joined-namespace": (
        "fn(Int, Int -> Int)",
        "fn(@Int, @Nat -> @Int) effects(pure) { @Int.0 - nat_to_int(@Nat.0) }",
        ["parameter 1 as `@Int`"]),
    "capture": (
        "fn(Int -> Int)",
        "fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) + @Int.0 }",
        ["parameter 0 as `@Int`"]),
    "narrowed-namespace": (
        "fn(Int, Pos -> Int)",
        "fn(@Pos, @Pos -> @Int) effects(pure) { 1000 + @Pos.1 - 2 * @Pos.0 }",
        ["parameter 0 as `@Int`"]),
    "shadowed-nat": (
        "fn(Int, Nat -> Int)",
        "fn(@Nat, @Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) }",
        ["parameter 0 as `@Int`"]),
    "every-unfit-part": (
        "fn(Int, Int -> Nat)",
        "fn(@Nat, @Nat -> @Int) effects(pure) { 0 }",
        ["parameter 0 as `@Int`", "parameter 1 as `@Int`",
         "its result as `@Nat`"]),
}


@pytest.mark.parametrize("shape", list(_IN_PLACE))
def test_repro_a_closure_written_in_place_is_given_prose_1885(
        shape: str) -> None:
    """The header rewritten in place misled three ways once the reader
    kept the body: the namespace the changed parameter joins, the narrowed
    type's own namespace (`fn(@Pos, @Pos -> @Int)`: 100 and 7 gave 807,
    not 1086), the narrowing's `let @Nat` read by the kept `@Nat.0` (7 and
    2 gave 7, not 2), and a second unfit part left unfit.  The fix prints
    no code for a closure written in place: it names every part to
    declare, and says how the references move."""
    position, closure, named = _IN_PLACE[shape]
    source = (_ALIASES + f"type F = {position} effects(pure);\n\n" + _fn(
        "main(@Int, @Int -> @Int)",
        f"let @F = {closure};\n  apply_fn(@F.0, "
        + ("@Int.1, @Int.0" if "," in position else "@Int.0") + ")",
        visibility="public"))
    fix = str(_only_diagnostic(source)["fix"])
    assert not re.search(r"`fn\(", fix), fix
    assert _RENUMBER in fix, fix
    for part in named:
        assert part in fix, (part, fix)


# =====================================================================
# Outside the narrowing: every binding position is held to `is_subtype`
# =====================================================================

def test_repro_a_binder_over_an_io_function_s_option_is_refused() -> None:
    """`@Option<W>` over an `Option<IOF>`: the either-direction test held
    (`Option<W>` fits `Option<IOF>`), so the binder took an `<IO>` function
    at a pure type, and the run printed from a function declared
    `effects(pure)`.  The binder is held to `is_subtype` (#1896): E314."""
    source = (
        "type W = fn(Int -> Int) effects(pure);\n"
        "type IOF = fn(Int -> Int) effects(<IO>);\n\n"
        + _fn("run(@Option<IOF> -> @Int)",
              "match @Option<IOF>.0 {\n    @Option<W> -> match @Option<W>.0 "
              "{\n      Some(@W) -> apply_fn(@W.0, 5),\n      None -> 0\n    }"
              "\n  }")
        + "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)\n{\n  run(Some(fn(@Int -> @Int) effects(<IO>) "
        "{ IO.print(\"leak\\n\"); @Int.0 }))\n}\n")
    assert _codes(source) == ["E314"], source


def test_repro_a_binder_over_a_type_variable_s_option_is_refused() -> None:
    """`@Option<Int>` over an `Option<T>` inside `forall<T>`: the binder
    took a concrete type no instantiation is held to, and `Some("abc")`
    returned 4.  The `T` stays rigid (#1896): E314, as the `let` of it is
    E170."""
    source = (
        _fn("run(@Option<T> -> @Int)",
            "match @Option<T>.0 {\n    @Option<Int> -> "
            "option_unwrap_or(@Option<Int>.0, 0) + 1\n  }").replace(
                "private fn", "private forall<T> fn")
        + _fn("main(@Unit -> @Int)", 'run(Some("abc"))', visibility="public"))
    assert _codes(source) == ["E314"], source


def test_repro_the_join_passes_a_pure_callback_at_an_io_one_is_refused(
        ) -> None:
    """Inside a generic function, a `fn(@P, @T -> @Int)` closure, `P` a
    pure callback, passed where `fn(I, T -> Int)` is expected, `I` the same
    callback under `<IO>`: was accepted, and the run printed from functions
    declared `effects(pure)`.  The join's fit is held to `is_subtype`
    (#1896): E202, as with no type variable."""
    source = (
        "type P = fn(Int -> Int) effects(pure);\n"
        "type I = fn(Int -> Int) effects(<IO>);\n"
        "type H<U> = fn(I, U -> Int) effects(pure);\n\n"
        + _fn("helper(@H<U>, @I, @U -> @Int)",
              "apply_fn(@H<U>.0, @I.0, @U.0)").replace(
                  "private fn", "private forall<U> fn")
        + _fn("outer(@I, @T -> @Int)",
              "helper(fn(@P, @T -> @Int) effects(pure) { apply_fn(@P.0, 1) }"
              ", @I.0, @T.0)").replace("private fn", "private forall<T> fn")
        + "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)\n{\n  outer(fn(@Int -> @Int) effects(<IO>) {\n"
        "      IO.print(\"leak\\n\");\n      @Int.0\n    }, 7)\n}\n")
# A join's arms in either order (a `match` joins as an `if` does)
# =====================================================================

#: Two pure functions whose second parameters are a pure callback and the
#: same callback under `<IO>`: the join is `fn(Nat, P -> Int)` in every
#: order, the arm that takes `P` read at its first parameter's narrowing.
_ARM_A = "fn(@Int, @P -> @Int) effects(pure) { apply_fn(@P.0, @Int.0) }"
_ARM_B = "fn(@Nat, @I -> @Int) effects(pure) { nat_to_int(@Nat.0) }"
_ARM_TYPES = ("type P = fn(Int -> Int) effects(pure);\n"
              "type I = fn(Int -> Int) effects(<IO>);\n"
              "type J = fn(Nat, P -> Int) effects(pure);\n"
              "type JI = fn(Nat, I -> Int) effects(pure);\n\n")


def _joined(form: str, arms: Sequence[str]) -> str:
    """*arms* joined by an `if` (two) or a `match` on an `Int` (any
    number), the arm that takes `P` chosen where it stands."""
    if form == "if":
        return f"if @Int.0 == 0 then {{ {arms[0]} }} else {{ {arms[1]} }}"
    cases = [f"    {i} -> {arm}," for i, arm in enumerate(arms[:-1])]
    return ("match @Int.0 {\n" + "\n".join(cases)
            + f"\n    _ -> {arms[-1]}\n  }}")


def _arm_program(form: str, arms: Sequence[str], callback: str,
                 bind: str | None = None) -> str:
    """A pure `pick(@Int, @CB -> @Int)` applies the join of *arms* to `5`
    and its callback; `main` picks the arm that takes `P`.  *callback* is
    `pure` or `io`; *bind* is the type a `let` binds the join at."""
    cb = "P" if callback == "pure" else "I"
    joined = _joined(form, arms)
    body = (f"let @{bind} = {joined};\n  apply_fn(@{bind}.0, 5, @{cb}.0)"
            if bind else f"apply_fn({joined}, 5, @{cb}.0)")
    value = ("fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }" if cb == "P"
             else 'fn(@Int -> @Int) effects(<IO>) { IO.print("leak\\n"); '
                  "@Int.0 }")
    return (_ARM_TYPES
            + _fn(f"pick(@Int, @{cb} -> @Int)", body)
            + "public fn main(@Unit -> @Int)\n  requires(true)\n"
            "  ensures(true)\n  effects(<IO>)\n{\n"
            f"  pick({arms.index(_ARM_A)}, {value})\n}}\n")


_ARM_ORDERS = {"A-first": (_ARM_A, _ARM_B), "B-first": (_ARM_B, _ARM_A)}


@pytest.mark.parametrize("form", ["if", "match"])
@pytest.mark.parametrize("order", list(_ARM_ORDERS))
def test_repro_a_join_s_arms_join_in_either_order_1885(
        form: str, order: str) -> None:
    """A `match` folded its arms left to right and asked the join in one
    walk order, which compares a callback's effect row the failing way
    round when the `P` arm comes first: E302, where an `if`, which asks
    both orders, and `main` accepted it.  Now every order is accepted, at
    `fn(Nat, P -> Int)`, and runs; with an `<IO>` callback the
    application is refused against that pure parameter (E202)."""
    arms = _ARM_ORDERS[order]
    pure = _arm_program(form, arms, "pure")
    verified = pipeline.verify(pure, reconcile=True)
    assert verified.ok, [(d.error_code, d.description[:160])
                         for d in verified.errors]
    assert pipeline.run(pure, fn="main", args=[]).execution.value == 6
    io = pipeline.check(_arm_program(form, arms, "io")).errors
    assert [d.error_code for d in io] == ["E202"], [d.description for d in io]
    assert "expected fn(Int -> Int) effects(pure)" in io[0].description


@pytest.mark.parametrize("odd", [0, 1, 2])
def test_repro_three_arms_join_whichever_arm_is_odd_1885(odd: int) -> None:
    """Three `match` arms, the `P` arm first, second or third."""
    arms = [_ARM_B, _ARM_B, _ARM_B]
    arms[odd] = _ARM_A
    source = _arm_program("match", arms, "pure")
    assert _codes(source) == [], source
    assert pipeline.run(source, fn="main", args=[]).execution.value == 6


@pytest.mark.parametrize("form", ["if", "match"])
@pytest.mark.parametrize("order", list(_ARM_ORDERS))
def test_repro_the_join_is_bound_at_its_pure_type_and_no_other_1885(
        form: str, order: str) -> None:
    """The joined type is `fn(Nat, P -> Int)`: a `let` binds it there, and
    at `fn(Nat, I -> Int)` it is refused (E170) in every order, so the
    `<IO>` callback reaches the `P` arm in none."""
    arms = _ARM_ORDERS[order]
    pinned = _arm_program(form, arms, "pure", bind="J")
    assert _codes(pinned) == [], pinned
    assert pipeline.run(pinned, fn="main", args=[]).execution.value == 6
    assert _codes(_arm_program(form, arms, "io", bind="JI")) == ["E170"]


# =====================================================================
# A variable an argument writes one refinement at, at every position
# =====================================================================

_ENDO_TYPES = (_ALIASES
               + "type G<T> = fn(T -> T) effects(pure);\n"
               "type G3<T> = fn(T, T -> T) effects(pure);\n\n")
_ENDO_HELPERS = "".join(
    _fn(sig, body).replace("private fn", "private forall<T> fn")
    for sig, body in (
        ("app(@G<T>, @T -> @T)", "apply_fn(@G<T>.0, @T.0)"),
        ("ppa(@T, @G<T> -> @T)", "apply_fn(@G<T>.0, @T.0)"),
        ("app3(@G3<T>, @T -> @T)", "apply_fn(@G3<T>.0, @T.0, @T.0)")))

#: (the parameter `main` takes, the call, whether it is accepted).  An
#: argument that writes `Pos` at every position its function type gives
#: `T` pins nothing, so `T` is `Pos` where no other argument says
#: otherwise: the polarity pin chooses between `Int` and `Nat` only where
#: the positions differ (spec §4.2).  Two refinements leave no instance
#: the closure fits: refused in either order.  A value at the base beside
#: the closure makes the instance the value's, `Int`, which the closure
#: does not fit: refused in either order, as today, though `Pos` would fit
#: it and narrow the value; that choice is #1891's, recorded there.
_ENDO_CELLS = {
    "one-refinement-closure-first": (
        "@Pos", "app(fn(@Pos -> @Pos) effects(pure) { @Pos.0 }, @Pos.0)",
        True),
    "one-refinement-value-first": (
        "@Pos", "ppa(@Pos.0, fn(@Pos -> @Pos) effects(pure) { @Pos.0 })",
        True),
    "three-positions": (
        "@Pos", "app3(fn(@Pos, @Pos -> @Pos) effects(pure) { @Pos.1 }, "
        "@Pos.0)", True),
    "two-refinements-closure-first": (
        "@Big", "app(fn(@Pos -> @Big) effects(pure) { 11 }, @Big.0)", False),
    "two-refinements-value-first": (
        "@Big", "ppa(@Big.0, fn(@Pos -> @Big) effects(pure) { 11 })", False),
    "base-value-closure-first": (
        "@Int", "app(fn(@Pos -> @Pos) effects(pure) { @Pos.0 }, @Int.0)",
        False),
    "base-value-value-first": (
        "@Int", "ppa(@Int.0, fn(@Pos -> @Pos) effects(pure) { @Pos.0 })",
        False),
    "int-endofunction": (
        "@Int", "app(fn(@Int -> @Int) effects(pure) { @Int.0 }, @Int.0)",
        True),
}


@pytest.mark.parametrize("cell", list(_ENDO_CELLS))
def test_a_variable_written_once_at_every_position_is_that_type(
        cell: str) -> None:
    param, call, accepted = _ENDO_CELLS[cell]
    source = _ENDO_TYPES + _ENDO_HELPERS + _fn(
        f"main({param} -> @Int)", call, visibility="public")
    if not accepted:
        assert _codes(source) == ["E190"], source
        return
    assert pipeline.verify(source, reconcile=True).ok, source
    assert pipeline.run(source, fn="main", args=[12]).execution.value == 12


def test_repro_an_endofunction_over_a_refinement_fills_its_data_type_1885(
        ) -> None:
    """`B(fn(@Pos -> @Pos) ...)` into `data Box<T> { B(fn(T -> T)) }`: the
    polarity pin took the result's `Pos` for an `Int` and fixed `T` at the
    base, so the closure was refused (E190) where every position wrote
    `Pos`; main accepted it by the relaxed rule this change removes."""
    source = _ALIASES + (
        "type F = fn(Pos -> Pos) effects(pure);\n\n"
        "private data Box<T> {\n  B(fn(T -> T) effects(pure))\n}\n\n"
        + _fn("go(@Pos -> @Int)",
              "let @Box<Pos> = B(fn(@Pos -> @Pos) effects(pure) { @Pos.0 });\n"
              "  match @Box<Pos>.0 {\n    B(@F) -> apply_fn(@F.0, @Pos.0)\n  }",
              visibility="public"))
    assert pipeline.verify(source, reconcile=True).ok
    assert pipeline.run(source, fn="go", args=[3]).execution.value == 3


def test_repro_a_generic_call_reports_each_argument_once_1885() -> None:
    """`choose<T>(T, T)` handed callbacks at two refinements of `Int`: the
    variable's join reported E190 at the first argument, and the argument
    check reported it there again.  The call holds each argument to the
    instance, so the join reports nothing: one E190 an argument."""
    source = _ALIASES + (
        "type FP = fn(Pos -> Int) effects(pure);\n"
        "type FB = fn(Big -> Int) effects(pure);\n\n") + _fn(
        "choose(@T, @T -> @T)", "@T.1").replace(
            "private fn", "private forall<T> fn") + _fn(
        "main(@Int -> @Int)",
        "let @FP = fn(@Pos -> @Int) effects(pure) { @Pos.0 };\n"
        "  let @FB = fn(@Big -> @Int) effects(pure) { @Big.0 };\n"
        "  apply_fn(choose(@FP.0, @FB.0), 50)", visibility="public")
    line = next(n for n, text in enumerate(source.splitlines(), 1)
                if "choose(@FP.0" in text)
    text = source.splitlines()[line - 1]
    found = [(d.error_code, d.location.line, d.location.column)
             for d in pipeline.check(source).errors]
    assert found == [("E190", line, text.index("@FP.0") + 1),
                     ("E190", line, text.index("@FB.0") + 1)], found


# =====================================================================
# `Nat` and its written form are one type inside a function type
# =====================================================================

_NAT_SPELLINGS = ("type NN = { @Int | @Int.0 >= 0 };\n"
                  "type LE = { @Int | 0 <= @Int.0 };\n"
                  "type GT = { @Int | @Int.0 > -1 };\n")

#: (the position, the closure's parameter, its result, accepted).  `Nat`
#: is `{ @Int | @Int.0 >= 0 }` (spec §2.2.1): written exactly so, the two
#: are one type both ways, at a parameter and at a result; any other
#: spelling is another refinement, and `Int` fits neither.
_NAT_CELLS = {
    "result-nat-at-written": ("fn(Int -> NN)", "Int", "Nat", True),
    "result-written-at-nat": ("fn(Int -> Nat)", "Int", "NN", True),
    "parameter-nat-at-written": ("fn(NN -> Int)", "Nat", "Int", True),
    "parameter-written-at-nat": ("fn(Nat -> Int)", "NN", "Int", True),
    "result-nat-at-inline": ("fn(Int -> { @Int | @Int.0 >= 0 })", "Int",
                             "Nat", True),
    "result-nat-at-le": ("fn(Int -> LE)", "Int", "Nat", False),
    "result-nat-at-gt": ("fn(Int -> GT)", "Int", "Nat", False),
    "parameter-le-at-nat": ("fn(Nat -> Int)", "LE", "Int", False),
    "result-int-at-written": ("fn(Int -> NN)", "Int", "Int", False),
    "parameter-written-at-int": ("fn(Int -> Int)", "NN", "Int", False),
}


@pytest.mark.parametrize("cell", list(_NAT_CELLS))
def test_nat_and_its_written_form_are_one_type_in_a_function_type(
        cell: str) -> None:
    position, param, result, accepted = _NAT_CELLS[cell]
    body = "7" if result != "Int" else "0"
    source = (_NAT_SPELLINGS + f"type F = {position} effects(pure);\n\n"
              + _fn("main(@Nat -> @Int)",
                    f"let @F = fn(@{param} -> @{result}) effects(pure) "
                    f"{{ {body} }};\n  0", visibility="public"))
    assert _codes(source) == ([] if accepted else ["E190"]), source


@pytest.mark.xfail(strict=True, raises=_KnownVerdict, reason=(
    "a data type's type arguments are compared covariantly whatever its "
    "fields do with the parameter: #1902"))
def test_repro_a_box_of_a_nat_callback_at_a_box_of_int_is_refused() -> None:
    """`Box<Nat>` at `Box<Int>`, `Box`'s field a `fn(T -> Int)`: the field
    is read as `fn(Int -> Int)`, and `go(-5)` returns -5 out of the
    closure's `@Nat` parameter after a clean verify, at main too."""
    source = (
        "private data Box<T> {\n  B(fn(T -> Int) effects(pure))\n}\n\n"
        "type IntToInt = fn(Int -> Int) effects(pure);\n\n"
        + _fn("use_box(@Box<Int>, @Int -> @Int)",
              "match @Box<Int>.0 {\n    B(@IntToInt) -> "
              "apply_fn(@IntToInt.0, @Int.0)\n  }")
        + _fn("make(@Unit -> @Box<Nat>)",
              "B(fn(@Nat -> @Int) effects(pure) { @Nat.0 })")
        + _fn("go(@Int -> @Int)", "use_box(make(()), @Int.0)",
              visibility="public"))
    _known(_codes(source), known=[], fixed=lambda g: g != [])
=======
    assert _codes(source) == ["E202"], source


# ==============================================================