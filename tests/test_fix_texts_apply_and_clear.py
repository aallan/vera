"""A diagnostic's fix, applied as written, clears it (#1778, #1763).

A fix is an instruction (DESIGN.md principle 1), so the text it gives the
reader to write has to be text the program can hold, and writing it where
the fix says has to clear the diagnostic.  Two mechanisms broke that:

- #1778: a fix that tells the reader to write a type rendered it in the
  message form, which elides a refinement's predicate (`{@Int | ...}` is
  not Vera).  A fix now writes a type as the program writes it
  (`vera.types.written_type`, through `ast.format_type`), and names no
  type where the type has a part no program writes (`fn(? -> ?)`).
- #1763: a fix written as a literal example named a slot or a shape the
  site may not have (`requires(@Int.0 >= 0)` in a function with no
  `@Int`).  The example is now computed from the site — the operand, the
  counterexample's binding, the function's own parameter, the site's type
  argument — and dropped where nothing can be computed.
- #1858: a `requires` computed from the site's operands was written at the
  entry, where an operand a `let`, a pattern or a destructure binds names a
  parameter or nothing (E526, E527, E505, E501).  The clause is offered
  only in the entry's terms, solver-confirmed; the guard is written at the
  site, where its operands are the site's own.

The instrument applies each fix from its text alone: the clause, type or
command between backticks is extracted and inserted where the fix says (a
per-code place, `_Case.apply`), and the result is checked again.  No
hand-written corrected program stands in for the fix.  Each cell asserts
the code fires at the program, that the text parses where it is inserted
(no E005, no E130), and that the code no longer fires.  Each code also has
a cell applying its base text the same way, which stays red, so the gate
is one that can fail.
"""

from __future__ import annotations

import ast as pyast
import json
import os
import re
import shlex
import subprocess
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

import vera
from tests import pipeline

# A class instrument (tests/matrix_sample.py): a pull request runs a sample
# of the parametrised cells, and all of them when it changes this file or a
# module that writes one of the fix texts it applies.
pytestmark = pytest.mark.matrix(decides=[
    "vera/types.py",
    "vera/checker/core.py",
    "vera/checker/calls.py",
    "vera/checker/control.py",
    "vera/checker/expressions.py",
    "vera/checker/resolution.py",
    "vera/typed.py",
    "vera/verifier.py",
    "vera/smt.py",
    "vera/errors.py",
])

ROOT = Path(__file__).resolve().parent.parent

POS = "type Pos = { @Int | @Int.0 > 0 };\n\n"
FN_TYPE = "type IntToInt = fn(Int -> Int) effects(pure);\n\n"
ENDO = """type Endo<T> = fn(T -> T) effects(pure);

private forall<T> fn mk(@Unit -> @Endo<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@T -> @T) effects(pure) { @T.0 }
}

"""


def _fn(params: str, ret: str, body: str, *, req: str = "true",
        ens: str = "true", eff: str = "pure", forall: str = "",
        dec: str = "") -> str:
    """The function `f` every case's site is in."""
    head = f"forall<{forall}> " if forall else ""
    measure = f"  decreases({dec})\n" if dec else ""
    return (f"public {head}fn f({params} -> {ret})\n  requires({req})\n"
            f"  ensures({ens})\n{measure}  effects({eff})\n{{\n  {body}\n}}\n")


def _helper(name: str, sig: str, body: str, forall: str = "") -> str:
    head = f"forall<{forall}> " if forall else ""
    return (f"private {head}fn {name}({sig})\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{\n  {body}\n}}\n\n")


# =====================================================================
# Applying a fix from its text
# =====================================================================

_SPAN = re.compile(r"`([^`]+)`")


def spans(fix: str) -> list[str]:
    """The text a fix gives the reader to write: each backticked span."""
    return _SPAN.findall(fix)


def _once(source: str, site: str, text: str) -> str:
    assert source.count(site) == 1, (site, source)
    return source.replace(site, text)


def replace(site: str, pattern: str = "{0}") -> Callable[[str, list[str]], str]:
    """Write the fix's spans, through *pattern*, in place of *site*."""
    def apply(source: str, given: list[str]) -> str:
        return _once(source, site, pattern.format(*given))
    return apply


def as_value(site: str, value: str | None = None, *,
             span: int = 0) -> Callable[[str, list[str]], str]:
    """"Pass a value of type T": `f` takes a parameter of the type the fix
    names, declared under an alias so its slot reference is that alias's
    alone, and *value* (all of *site* by default) is that parameter."""
    def apply(source: str, given: list[str]) -> str:
        source = _once(source, site,
                       site.replace(value or site, "@Probe.0", 1))
        head = re.search(r"public (?:forall<[^>]*> )?fn f\(([^)]*?) ->",
                         source)
        assert head is not None
        params = head.group(1)
        joined = f"{params}, @Probe" if params else "@Probe"
        source = (source[:head.start(1)] + joined + source[head.end(1):])
        return f"type Probe = {given[span]};\n\n" + source
    return apply


def prepend_then(site: str, pattern: str) -> Callable[[str, list[str]], str]:
    """A declaration the fix gives (its first span) written before the
    program, and its other spans, through *pattern*, in place of *site*."""
    def apply(source: str, given: list[str]) -> str:
        return given[0] + "\n\n" + _once(source, site,
                                         pattern.format(*given[1:]))
    return apply


@dataclass(frozen=True)
class _Case:
    code: str
    stage: str              # "check" or "verify"
    source: str
    apply: Callable[[str, list[str]], str]
    #: The span(s) the base text gave the reader, applied by `apply` in the
    #: honesty cell; `None` where the base text gave nothing to apply.
    base: tuple[str, ...] | None = None


def _run(stage: str, source: str) -> pipeline.Checked | pipeline.Verified:
    return (pipeline.verify(source) if stage == "verify"
            else pipeline.check(source))


def _codes(stage: str, source: str) -> set[str]:
    return {d.error_code for d in _run(stage, source).diagnostics}


def _errors(stage: str, source: str) -> set[str]:
    return {d.error_code for d in _run(stage, source).errors}


def _the(code: str, stage: str, source: str):  # type: ignore[no-untyped-def]
    found = [d for d in _run(stage, source).diagnostics
             if d.error_code == code]
    assert found, f"{code} does not fire: {sorted(_codes(stage, source))}"
    return found[0]


def _passed_codes(stage: str, source: str) -> set[str]:
    """The codes *source* draws at *stage*, once it has passed the stage's
    gate: the check clean at `check`, and at `verify` the verifier run,
    which it is not when the check refuses (PR 1859 review).  A verifier
    code read off a program the checker refused is absent by construction,
    so its absence proves nothing."""
    result = _run(stage, source)
    passed = (result.ran if isinstance(result, pipeline.Verified)
              else result.ok)
    codes = {d.error_code for d in result.diagnostics}
    assert passed, (stage, sorted(codes), source)
    return codes


def _applied_clears(case: _Case, given: list[str]) -> set[str]:
    """The codes the program draws with *given* applied, once it passes its
    stage's gate; asserts the text parsed where it went and names no slot
    the site lacks."""
    fixed = case.apply(case.source, given)
    codes = _passed_codes(case.stage, fixed)
    assert "E005" not in codes and "E006" not in codes, (given, fixed)
    assert "E130" not in codes, (given, fixed)
    return codes


# =====================================================================
# The cases: code x binding set x site form
# =====================================================================

CASES: dict[str, _Case] = {
    # --- #1763: an example computed from the site -----------------------
    # E503: the narrowed value at entry, or the counterexample's binding.
    "E503-issue-bool-nat": _Case(
        "E503", "verify", _fn("@Bool, @Nat", "@Int",
            "let @Nat = if @Bool.0 then { @Nat.0 } else { -1 };\n  0"),
        replace("requires(true)", "{0}"), base=("requires(@Int.0 >= 0)",)),
    "E503-one-int": _Case(
        "E503", "verify", _fn("@Int", "@Int", "let @Nat = @Int.0;\n  0"),
        replace("requires(true)", "{0}")),
    "E503-two-int": _Case(
        "E503", "verify", _fn("@Int, @Int", "@Int",
                              "let @Nat = @Int.1 - @Int.0;\n  0"),
        replace("requires(true)", "{0}"), base=("requires(@Int.0 >= 0)",)),
    "E503-refined": _Case(
        "E503", "verify", POS + _fn("@Pos, @Int", "@Int",
                                    "let @Nat = @Int.0;\n  0"),
        replace("requires(true)", "{0}")),
    "E503-generic": _Case(
        "E503", "verify",
        _helper("g", "@T, @Int -> @Int", "let @Nat = @Int.0;\n  0", "T")
        + _fn("@Int", "@Int", "g(true, @Int.0)"),
        replace("private forall<T> fn g(@T, @Int -> @Int)\n  requires(true)",
                "private forall<T> fn g(@T, @Int -> @Int)\n  {0}")),
    "E503-return": _Case(
        "E503", "verify", _fn("@Nat", "@Nat", "@Nat.0 - 1"),
        replace("requires(true)", "{0}"), base=("requires(@Int.0 >= 0)",)),
    # E502: the subtraction's own operands.
    "E502-two-nat": _Case(
        "E502", "verify", _fn("@Nat, @Nat", "@Nat", "@Nat.1 - @Nat.0"),
        replace("requires(true)", "{0}"),
        base=("requires(@Nat.0 >= @Nat.1)",)),
    "E502-nat-and-int": _Case(
        "E502", "verify", _fn("@Int, @Nat, @Nat", "@Nat", "@Nat.1 - @Nat.0"),
        replace("requires(true)", "{0}"),
        base=("requires(@Nat.0 >= @Nat.1)",)),
    # E123 / E124: the clause's own operand, compared with zero.
    "E123-int": _Case(
        "E123", "check", _fn("@Int", "@Int", "0", req="@Int.0"),
        replace("requires(@Int.0)")),
    "E123-two-int": _Case(
        "E123", "check", _fn("@Int, @Int", "@Int", "0", req="@Int.1"),
        replace("requires(@Int.1)")),
    "E123-nat-only": _Case(
        "E123", "check", _fn("@Nat", "@Int", "0", req="@Nat.0"),
        replace("requires(@Nat.0)"), base=("requires(@Int.0 > 0)",)),
    "E123-float": _Case(
        "E123", "check", _fn("@Float64", "@Int", "0", req="@Float64.0"),
        replace("requires(@Float64.0)"), base=("requires(@Int.0 > 0)",)),
    "E124-int": _Case(
        "E124", "check", _fn("@Int", "@Int", "0", ens="@Int.result"),
        replace("ensures(@Int.result)")),
    "E124-nat-result": _Case(
        "E124", "check", _fn("@Int", "@Nat", "0", ens="@Nat.result"),
        replace("ensures(@Nat.result)"), base=("ensures(@Int.result > 0)",)),
    # E126: the site's own refinement.
    "E126-int": _Case(
        "E126", "check", "type P = { @Int | @Int.0 };\n\n"
        + _fn("@P", "@Int", "0"),
        replace("{ @Int | @Int.0 }")),
    "E126-nat": _Case(
        "E126", "check", "type P = { @Nat | @Nat.0 };\n\n"
        + _fn("@P", "@Int", "0"),
        replace("{ @Nat | @Nat.0 }")),
    # E300: the condition's own operand.
    "E300-int": _Case(
        "E300", "check", _fn("@Int", "@Int",
                             "if @Int.0 then { 1 } else { 0 }"),
        replace("if @Int.0 then", "if {0} then")),
    "E300-nat-only": _Case(
        "E300", "check", _fn("@Nat", "@Int",
                             "if @Nat.0 then { 1 } else { 0 }"),
        replace("if @Nat.0 then", "if {0} then"), base=("@Int.0 > 0",)),
    # E127 / E137: the function's own parameter of a fitting type.
    "E127-nat": _Case(
        "E127", "check", _fn("@Nat, @Float64", "@Int", "0",
                             dec="@Float64.0"),
        replace("decreases(@Float64.0)")),
    "E127-int-only": _Case(
        "E127", "check", _fn("@Int, @Float64", "@Int", "0",
                             dec="@Float64.0"),
        replace("decreases(@Float64.0)"), base=("decreases(@List.0)",)),
    "E127-array-only": _Case(
        "E127", "check", _fn("@Array<Int>, @Float64", "@Int", "0",
                             dec="@Float64.0"),
        replace("decreases(@Float64.0)"), base=("decreases(@Nat.0)",)),
    "E137-nat": _Case(
        "E137", "check", _fn("@Nat", "@Int", "f(@Nat.0)"),
        replace("  effects(pure)\n{\n  f(",
                "  {0}\n  effects(pure)\n{{\n  f(")),
    "E137-int-only": _Case(
        "E137", "check", _fn("@Int", "@Int", "f(@Int.0)"),
        replace("  effects(pure)\n{\n  f(",
                "  {0}\n  effects(pure)\n{{\n  f("),
        base=("decreases(@Nat.1 - @Nat.0)",)),
    # E128: the array domain's own length.
    "E128-array": _Case(
        "E128", "check", _fn("@Array<Int>", "@Bool",
            "forall(@Int, @Array<Int>.0, fn(@Int -> @Bool) effects(pure) "
            "{ true })"),
        replace("forall(@Int, @Array<Int>.0,", "forall(@Int, {0},")),
    "E128-array-of-bool": _Case(
        "E128", "check", _fn("@Array<Bool>", "@Bool",
            "forall(@Int, @Array<Bool>.0, fn(@Int -> @Bool) effects(pure) "
            "{ true })"),
        replace("forall(@Int, @Array<Bool>.0,", "forall(@Int, {0},"),
        base=("array_length(@Array<T>.0)",)),
    # E201 / E202 (apply_fn): the function's own function value.
    "E201-apply-fn": _Case(
        "E201", "check", "type Twice = fn(Int -> Int) effects(pure);\n\n"
        + _fn("@Twice", "@Int", "apply_fn()"),
        replace("apply_fn()"), base=("apply_fn(@IntToInt.0, 5)",)),
    "E202-apply-fn-not-a-function": _Case(
        "E202", "check", FN_TYPE + "type Twice = fn(Int -> Int) "
        "effects(pure);\n\n" + _fn("@Twice", "@Int", "apply_fn(5, 1)"),
        replace("apply_fn(5, 1)", "apply_fn({0}, 1)"),
        base=("@IntToInt.0",)),
    # E216: the expected tuple's arity, or one element.
    "E216-expected": _Case(
        "E216", "check", _fn("@Int", "@Int",
                             "let @Tuple<Int, Bool> = Tuple();\n  0"),
        replace("Tuple();", "{0};"), base=("Tuple(@Int.0)",)),
    "E216-no-int": _Case(
        "E216", "check", _fn("@Bool", "@Int", "Tuple();\n  0"),
        replace("Tuple();", "{0};"), base=("Tuple(@Int.0)",)),
    # E321: one binding per field, at its type.
    "E321-pattern": _Case(
        "E321", "check", _fn("@Option<Bool>", "@Int",
            "match @Option<Bool>.0 {\n    Some(@Bool, @Bool) -> 1,\n"
            "    None -> 0\n  }"),
        replace("Some(@Bool, @Bool)"), base=("Some(@T)",)),
    # E340: the site's own type argument, aliased.
    "E340-fn-type": _Case(
        "E340", "check", FN_TYPE + _fn("@Unit", "@Int",
            "handle[Exn<fn(Int -> Int) effects(pure)>] {\n"
            "    throw(@IntToInt) -> { apply_fn(@IntToInt.0, 1) }\n"
            "  } in {\n    1\n  }"),
        prepend_then("handle[Exn<fn(Int -> Int) effects(pure)>]", "{0}"),
        base=("type Small = { @Nat | @Nat.0 < 10 };",
              "handle[Exn<Small>]")),
    "E340-refinement": _Case(
        "E340", "check", _fn("@Unit", "@Int",
            "handle[State<{ @Nat | @Nat.0 < 10 }>](@Nat = 1) {\n"
            "    get(@Unit) -> { resume(1) },\n"
            "    put(@Nat) -> { resume(()) }\n  } in {\n    1\n  }"),
        prepend_then("handle[State<{ @Nat | @Nat.0 < 10 }>](@Nat = 1)",
                     "{0}({1} = 1)")),
    # E337: the handler's own first type argument.
    "E337-two-arguments": _Case(
        "E337", "check", _fn("@Unit", "@Int",
            "handle[State<Bool, Int>](@Bool = true) {\n"
            "    get(@Unit) -> { resume(@Bool.0) },\n"
            "    put(@Bool) -> { resume(()) }\n  } in {\n    1\n  }"),
        replace("handle[State<Bool, Int>]"), base=("handle[State<Int>]",)),

    # --- #1778: a type written as the program writes it ----------------
    "E336-alias": _Case(
        "E336", "check", POS + _fn("@Unit", "@Int",
            "handle[State<Pos>](@Int = 1) {\n"
            "    get(@Unit) -> { resume(1) },\n"
            "    put(@Int) -> { resume(()) }\n  } in {\n    1\n  }"),
        replace("(@Int = 1)", "({0} = 1)"), base=("@{@Int | ...}",)),
    "E202-refined-param": _Case(
        "E202", "check", POS + _helper("take", "@Pos -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)"),
        as_value("take(@Bool.0)", "@Bool.0"), base=("{@Int | ...}",)),
    "E202-array-of-refined": _Case(
        "E202", "check", POS + _helper("take", "@Array<Pos> -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)"),
        as_value("take(@Bool.0)", "@Bool.0"),
        base=("Array<{@Int | ...}>",)),
    "E202-plain": _Case(
        "E202", "check", _helper("take", "@Int -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)"),
        as_value("take(@Bool.0)", "@Bool.0")),
    "E213-refined-field": _Case(
        "E213", "check", POS + "private data Box {\n  Box(Pos)\n}\n\n"
        + _fn("@Bool", "@Int", "let @Box = Box(@Bool.0);\n  0"),
        as_value("Box(@Bool.0)", "@Bool.0"), base=("{@Int | ...}",)),
    "E170-let-refined": _Case(
        "E170", "check", POS + _fn("@Bool", "@Int",
                                   "let @Pos = @Bool.0;\n  0"),
        as_value("= @Bool.0;", "@Bool.0"), base=("{@Int | ...}",)),
    "E171-closure-refined": _Case(
        "E171", "check", POS + _fn("@Bool", "@Int",
            "let @fn(Int -> Int) effects(pure) = fn(@Int -> @Pos) "
            "effects(pure) { @Bool.0 };\n  0"),
        as_value("{ @Bool.0 }", "@Bool.0"), base=("{@Int | ...}",)),
    "E162-element": _Case(
        "E162", "check", _fn("@Bool", "@Int",
                             "let @Array<Int> = [1, @Bool.0];\n  0"),
        as_value("[1, @Bool.0]", "@Bool.0")),
    "E162-open-variable": _Case(
        "E162", "check", ENDO + _fn("@Bool", "@Int",
            "let @Nat = array_length([fn(@Int -> @Int) effects(pure) "
            "{ @Int.0 }, mk(())]);\n  0"),
        as_value(" mk(())]", "mk(())")),
    "E301-branch": _Case(
        "E301", "check", POS + _helper("pos", "@Unit -> @Pos", "1")
        + _fn("@Bool", "@Int",
              "let @Pos = if @Bool.0 then { true } else { pos(()) };\n  0"),
        as_value("{ true }", "true"), base=("{@Int | ...}",)),
    "E301-open-variable": _Case(
        "E301", "check", ENDO + _fn("@Bool", "@Int",
            "let @Int = if @Bool.0 then { 1 } else { mk(()) };\n  0"),
        as_value("{ mk(()) }", "mk(())")),
    "E302-arm": _Case(
        "E302", "check", POS + _helper("pos", "@Unit -> @Pos", "1")
        + _fn("@Option<Int>", "@Int",
              "let @Pos = match @Option<Int>.0 {\n    Some(@Int) -> pos(()),"
              "\n    None -> true\n  };\n  0"),
        as_value("None -> true", "true"), base=("{@Int | ...}",)),
    "E331-state-init": _Case(
        "E331", "check", POS + _fn("@Unit", "@Int",
            "handle[State<Pos>](@Pos = true) {\n"
            "    get(@Unit) -> { resume(@Pos.0) },\n"
            "    put(@Pos) -> { resume(()) }\n  } in {\n    1\n  }"),
        as_value("(@Pos = true)", "true"), base=("{@Int | ...}",)),
    "E335-state-update": _Case(
        "E335", "check", POS + _fn("@Unit", "@Int",
            "handle[State<Pos>](@Pos = 1) {\n"
            "    get(@Unit) -> { resume(@Pos.0) },\n"
            "    put(@Pos) -> { resume(()) } with @Pos = true\n"
            "  } in {\n    1\n  }"),
        as_value("with @Pos = true", "true"), base=("{@Int | ...}",)),
    "E334-state-update-type": _Case(
        "E334", "check", POS + _fn("@Unit", "@Int",
            "handle[State<Pos>](@Pos = 1) {\n"
            "    get(@Unit) -> { resume(@Pos.0) },\n"
            "    put(@Pos) -> { resume(()) } with @Int = 2\n"
            "  } in {\n    1\n  }"),
        replace("with @Int = 2", "with {0} = 2")),
    "E170-destructure-refined": _Case(
        "E170", "check", POS + _helper("pair", "@Unit -> @Tuple<Pos, Int>",
                                       "Tuple(1, 2)")
        + _fn("@Unit", "@Int", "let Tuple<@Bool, @Int> = pair(());\n  0"),
        replace("Tuple<@Bool, @Int>", "Tuple<{0}, @Int>"),
        base=("@{@Int | ...}",)),
    "E321-destructure-refined": _Case(
        "E321", "check", POS + "private data Box {\n  Box(Pos)\n}\n\n"
        + _helper("box", "@Unit -> @Box", "Box(1)")
        + _fn("@Unit", "@Int", "let Box<@Int, @Int> = box(());\n  0"),
        replace("Box<@Int, @Int>"), base=("Box<@{@Int | ...}>",)),
    "E125-row-with-refined-cell": _Case(
        "E125", "check", POS + _fn("@Unit", "@Unit", 'IO.print("x")',
                                   eff="<State<Pos>>"),
        replace("effects(<State<Pos>>)"),
        base=("effects(<IO, State<{@Int | ...}>>)",)),
}


#: Refinements over an alias (R121 review): the predicate names its binder
#: by the alias, so the written type's base is that name.
_ALIASED = {
    "count": ("type Count = Nat;\n\ntype Pos = { @Count | @Count.0 > 0 };\n\n",
              "Pos", "{ @Count | @Count.0 > 0 }"),
    "chain": ("type Pos = { @Int | @Int.0 > 0 };\n\n"
              "type Small = { @Pos | @Pos.0 < 10 };\n\n",
              "Small", "{ @Pos | @Pos.0 < 10 }"),
    "alias-of-alias": ("type C1 = Int;\n\ntype C2 = C1;\n\n"
                       "type Pos = { @C2 | @C2.0 > 0 };\n\n",
                       "Pos", "{ @C2 | @C2.0 > 0 }"),
}

#: The exact span each renderer path writes, which a predicate replaced or
#: dropped would change (a refinement keeps its predicate).
EXACT: dict[str, str] = {
    "E202-refined-param": "{ @Int | @Int.0 > 0 }",
    "E202-array-of-refined": "Array<{ @Int | @Int.0 > 0 }>",
    "E213-refined-field": "{ @Int | @Int.0 > 0 }",
    "E170-let-refined": "{ @Int | @Int.0 > 0 }",
    "E171-closure-refined": "{ @Int | @Int.0 > 0 }",
    "E162-element": "Int",
    "E301-branch": "{ @Int | @Int.0 > 0 }",
    "E302-arm": "{ @Int | @Int.0 > 0 }",
    "E331-state-init": "Pos",
    "E335-state-update": "Pos",
    "E334-state-update-type": "@Pos",
    "E336-alias": "@Pos",
    "E170-destructure-refined": "@{ @Int | @Int.0 > 0 }",
    "E321-destructure-refined": "Box<@{ @Int | @Int.0 > 0 }>",
    "E125-row-with-refined-cell":
        "effects(<IO, State<{ @Int | @Int.0 > 0 }>>)",
    "E503-numeric-before-flag": "requires(@Int.0 >= 0)",
    "E503-flag-after-numeric": "requires(@Int.0 >= 0)",
    "E123-grouped-operand": "requires(@Int.2 - (@Int.1 - @Int.0) > 0)",
}

for _shape, (_pre, _name, _written) in _ALIASED.items():
    CASES[f"E202-{_shape}"] = _Case(
        "E202", "check", _pre + _helper("take", f"@{_name} -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)"),
        as_value("take(@Bool.0)", "@Bool.0"))
    CASES[f"E170-{_shape}"] = _Case(
        "E170", "check", _pre + _fn("@Bool", "@Int",
                                    f"let @{_name} = @Bool.0;\n  0"),
        as_value("= @Bool.0;", "@Bool.0"))
    EXACT[f"E202-{_shape}"] = _written
    EXACT[f"E170-{_shape}"] = _written

CASES.update({
    # A Bool counterexample's clause can make the narrowing branch dead:
    # the numeric clause is offered first, in either parameter order.
    "E503-numeric-before-flag": _Case(
        "E503", "verify", _fn("@Bool, @Int", "@Int",
            "let @Nat = if @Bool.0 then { @Int.0 } else { 0 };\n  0"),
        replace("requires(true)", "{0}")),
    "E503-flag-after-numeric": _Case(
        "E503", "verify", _fn("@Int, @Bool", "@Int",
            "let @Nat = if @Bool.0 then { @Int.0 } else { 0 };\n  0"),
        replace("requires(true)", "{0}")),
    "E503-literal-divisor": _Case(
        "E503", "verify", _fn("@Int", "@Int", "let @Nat = @Int.0 / 2;\n  0"),
        replace("requires(true)", "{0}")),
    # The operand keeps its grouping where the example compares it.
    "E123-grouped-operand": _Case(
        "E123", "check", _fn("@Int, @Int, @Int", "@Int", "0",
                             req="@Int.2 - (@Int.1 - @Int.0)"),
        replace("requires(@Int.2 - (@Int.1 - @Int.0))")),
})

#: The cases whose applied program verifies with no error: the type the fix
#: wrote is the one the site needs, predicate and all.
VERIFIES = frozenset({
    "E202-refined-param", "E202-array-of-refined", "E213-refined-field",
    "E170-let-refined", "E301-branch", "E302-arm", "E331-state-init",
    "E335-state-update", *(f"{code}-{shape}" for shape in _ALIASED
                           for code in ("E202", "E170")),
})


@pytest.mark.parametrize("name", sorted(EXACT))
def test_the_fix_writes_the_exact_span(name: str) -> None:
    case = CASES[name]
    fix = _the(case.code, case.stage, case.source).fix
    assert spans(fix)[0] == EXACT[name], fix


@pytest.mark.parametrize("name", sorted(VERIFIES))
def test_the_applied_program_verifies_clean(name: str) -> None:
    """The refined cells stop at no check: the program the fix makes
    verifies, so a refinement written with another predicate (or none)
    would be refuted where the declared one is needed."""
    case = CASES[name]
    given = spans(_the(case.code, case.stage, case.source).fix)
    verified = pipeline.verify(case.apply(case.source, given))
    assert verified.ok, (name, verified.errors)


@pytest.mark.parametrize("name", sorted(CASES))
def test_the_fix_applied_as_written_clears_the_code(name: str) -> None:
    case = CASES[name]
    fix = _the(case.code, case.stage, case.source).fix
    given = spans(fix)
    assert given, f"{name}: the fix gives nothing to write: {fix!r}"
    codes = _applied_clears(case, given)
    assert case.code not in codes, (name, fix, sorted(codes))


@pytest.mark.parametrize(
    "name", sorted(n for n, c in CASES.items() if c.base is not None))
def test_the_base_text_applied_as_written_does_not_clear(name: str) -> None:
    """The gate can fail: the text the code gave at base, applied the same
    way, leaves the code firing, or draws an error the fix applied now does
    not (it does not parse, or names a slot or a type the site lacks)."""
    case = CASES[name]
    assert case.base is not None
    before = _errors(case.stage, case.apply(case.source, list(case.base)))
    given = spans(_the(case.code, case.stage, case.source).fix)
    after = _errors(case.stage, case.apply(case.source, given))
    assert case.code in before or before - after, (name, sorted(before))


# =====================================================================
# Where no example can be computed, the fix names none
# =====================================================================

DROPPED: dict[str, tuple[str, str, str]] = {
    # code, stage, program: nothing the site holds makes an example.
    "E503-variable-divisor": ("E503", "verify", _fn("@Int, @Int", "@Int",
        "let @Nat = @Int.1 / @Int.0;\n  0")),
    "E340-generic-type-argument": ("E340", "check", _fn(
        "@Unit", "@Int",
        "handle[Exn<fn(T -> T) effects(pure)>] {\n"
        "    throw(@Int) -> { 0 }\n  } in {\n    1\n  }", forall="T")),
    "E503-constant": ("E503", "verify", _fn("@Bool", "@Int",
                                            "let @Nat = 0 - 1;\n  0")),
    "E503-shadowed-operand": ("E503", "verify", _fn("@Int", "@Int",
        "let @Int = 0 - @Int.0;\n  let @Nat = @Int.0;\n  0")),
    "E502-let-operand": ("E502", "verify", _fn("@Nat", "@Nat",
        "let @Nat = 1;\n  @Nat.1 - @Nat.0")),
    "E123-string": ("E123", "check", _fn("@String", "@Int", "0",
                                         req="@String.0")),
    "E300-string": ("E300", "check", _fn("@String", "@Int",
        "if @String.0 then { 1 } else { 0 }")),
    "E127-no-fitting-parameter": ("E127", "check", _fn(
        "@Float64", "@Int", "0", dec="@Float64.0")),
    "E137-no-fitting-parameter": ("E137", "check", _fn(
        "@Bool", "@Int", "f(@Bool.0)")),
    "E201-no-function-value": ("E201", "check", _fn("@Int", "@Int",
                                                    "apply_fn()")),
    # A type parameter named as a data type is the parameter, no measure
    # (PR 1859 review).
    "E137-type-parameter-named-as-data": ("E137", "check",
        "private data Box { Box(Int) }\n\n"
        + _fn("@Box", "@Int", "f(@Box.0)", forall="Box")),
}

#: E301 with an open else branch: the then branch's type is named instead.
# The `if` with no type expected of it: an expected `Endo<Int>` would fix
# `mk`'s variable (spec §5.9, #1684), and a sibling branch's type does not.
E301_OPEN_ELSE = ENDO + _fn("@Bool", "@Int",
    "apply_fn(if @Bool.0 then { fn(@Int -> @Int) effects(pure) "
    "{ @Int.0 } } else { mk(()) }, 1)")


@pytest.mark.parametrize("name", sorted(DROPPED))
def test_a_fix_with_nothing_to_compute_names_no_example(name: str) -> None:
    """The sentence stands without an example: nothing backticked to
    write, and no slot reference."""
    code, stage, source = DROPPED[name]
    fix = _the(code, stage, source).fix
    assert [s for s in spans(fix) if s != "if"] == [], (name, fix)
    assert not re.search(r"@[A-Z]\w*(<[^>]*>)?\.\d", fix), (name, fix)
    assert "e.g." not in fix, (name, fix)


def test_the_base_e503_example_leaves_a_shadowed_operand_firing() -> None:
    """The shadowed operand: the value at the site is a `let`, so the
    base's `requires(@Int.0 >= 0)` (the parameter) leaves E503 firing; the
    fix offers no clause there rather than that one."""
    _code, stage, source = DROPPED["E503-shadowed-operand"]
    fixed = _once(source, "requires(true)", "requires(@Int.0 >= 0)")
    assert "E503" in _codes(stage, fixed)


# =====================================================================
# The reported instances (red at base)
# =====================================================================

# =====================================================================
# Each new fix helper's branches, by its whole text
# =====================================================================

_PAIR = "private data Pair {\n  Pair(Int, Bool)\n}\n\n"
#: A `where` helper `g` inheriting `forall<Box>` where a data type is also
#: named `Box`: {0} g's parameters, {1} f's body, {2} g's decreases line,
#: {3} g's body.
_WHERE_BOX = (
    "private data Box {{ Box(Int) }}\n\n"
    "public forall<Box> fn f(@Box -> @Int)\n  requires(true)\n"
    "  ensures(true)\n  effects(pure)\n{{\n  {1}\n}}\n"
    "where {{\n  fn g({0} -> @Int)\n    requires(true)\n    ensures(true)\n"
    "{2}    effects(pure)\n  {{\n    {3}\n  }}\n}}\n")
#: A non-literal destructure, so its first component is a projected term
#: (`_check_*_binding_obligation_term`) the solver relates to `@Int.0`.
_DESTRUCTURE_IF = ("let Tuple<@{0}, @Bool> = if @Bool.0 then "
                   "{{ Tuple(@Int.0, true) }} else {{ Tuple(1, false) }};\n  0")
_STATE_CLAUSES = ("    get(@Unit) -> { resume(1) },\n"
                  "    put(@Int) -> { resume(()) }\n  } in {\n    1\n  }")

#: name -> (code, stage, program, the fix's whole text).
WHOLE: dict[str, tuple[str, str, str, str]] = {
    "E216-expected": ("E216", "check", CASES["E216-expected"].source,
        "Provide at least one element: `Tuple(?, ?)`, with each ? one of "
        "its components; or use the unit value () if no payload is needed."),
    "E216-nothing-expected": ("E216", "check", CASES["E216-no-int"].source,
        "Provide at least one element: `Tuple(0)`; or use the unit value () "
        "if no payload is needed."),
    "E337-an-argument": ("E337", "check", CASES["E337-two-arguments"].source,
        "Write the handler with a single concrete type argument: "
        "`handle[State<Bool>]`."),
    "E337-the-state-only": ("E337", "check", _fn("@Unit", "@Int",
        "handle[State](@Int = 1) {\n" + _STATE_CLAUSES),
        "Write the handler with a single concrete type argument: "
        "`handle[State<Int>]`."),
    "E337-neither": ("E337", "check", _fn("@Unit", "@Int",
        "handle[Exn] {\n    throw(@Int) -> { 0 }\n  } in {\n    1\n  }"),
        "Write handle[Exn<T>] with a single concrete type argument for T."),
    "E321-two-fields": ("E321", "check", _PAIR + _fn("@Pair", "@Int",
        "match @Pair.0 {\n    Pair(@Int) -> 1\n  }"),
        "Give 'Pair' exactly 2 sub-pattern(s), one per field: "
        "`Pair(@Int, @Bool)`."),
    "E321-no-field": ("E321", "check", _fn("@Option<Int>", "@Int",
        "match @Option<Int>.0 {\n    Some(@Int) -> 1,\n    None(@Int) -> 0\n"
        "  }"),
        "Give 'None' exactly 0 sub-pattern(s), one per field."),
    "E340-names-taken": ("E340", "check",
        "type Cell = Int;\n\nprivate data Cell2 {\n  C2\n}\n\n"
        + _fn("@Unit", "@Int",
              "handle[State<{ @Nat | @Nat.0 < 10 }>](@Nat = 1) {\n"
              + _STATE_CLAUSES),
        "Name the type with an alias and handle that: `type Cell3 = "
        "{ @Nat | @Nat.0 < 10 };`, then `handle[State<Cell3>]`, with the "
        "state declared `@Cell3`."),
    "E340-type-parameter-in-predicate": ("E340", "check", _fn(
        "@Unit", "@Int",
        "handle[State<{ @Int | forall(@T, 3, fn(@Nat -> @Bool) "
        "effects(pure) { true }) }>](@Int = 1) {\n" + _STATE_CLAUSES,
        forall="T"),
        "Name the type with a type alias and handle that; the alias is "
        "declared at the top of the file, so a type parameter of this "
        "function is not in scope there."),
    "E300-int": ("E300", "check", CASES["E300-int"].source,
        "Replace the condition with a Bool-typed expression, such as a "
        "comparison with zero: `@Int.0 > 0`."),
    "E300-float": ("E300", "check", _fn("@Float64", "@Int",
        "if @Float64.0 then { 1 } else { 0 }"),
        "Replace the condition with a Bool-typed expression, such as a "
        "comparison with zero: `@Float64.0 > 0.0`."),
    "E300-string": ("E300", "check", DROPPED["E300-string"][2],
        "Replace the condition with a Bool-typed expression, such as a "
        "comparison of the value with a bound."),
    "E301-else-type": ("E301", "check", CASES["E301-branch"].source,
        "Make both branches produce the same type: convert one branch to "
        "`{ @Int | @Int.0 > 0 }` (or both to a common type), so then and "
        "else agree."),
    "E301-then-type": ("E301", "check", CASES["E301-open-variable"].source,
        "Make both branches produce the same type: convert one branch to "
        "`Int` (or both to a common type), so then and else agree."),
    "E301-neither": ("E301", "check", ENDO + _fn("@Bool", "@Int",
        "let @Int = if @Bool.0 then { mk(()) } else { [] };\n  0"),
        "Make both branches produce the same type: convert one branch to "
        "the other branch's type (or both to a common type), so then and "
        "else agree."),
    "E302-written": ("E302", "check", CASES["E302-arm"].source,
        "Make this arm produce `{ @Int | @Int.0 > 0 }` to match the other "
        "arms (or change every arm to a common type)."),
    "E302-open": ("E302", "check", ENDO + _fn("@Option<Int>", "@Int",
        "let @Int = match @Option<Int>.0 {\n    Some(@Int) -> mk(()),\n"
        "    None -> 1\n  };\n  0"),
        "Make this arm produce the previous arms' type to match the other "
        "arms (or change every arm to a common type)."),
    "E128-array": ("E128", "check", CASES["E128-array"].source,
        "Pass an integer bound, the array's length: "
        "`array_length(@Array<Int>.0)`, and index the array inside the "
        "predicate."),
    "E128-not-an-array": ("E128", "check", _fn("@Bool", "@Bool",
        "forall(@Int, @Bool.0, fn(@Int -> @Bool) effects(pure) { true })"),
        "Pass an integer bound, such as an array's length, and index the "
        "collection inside the predicate."),
    "E162-both-written": ("E162", "check", CASES["E162-element"].source,
        "Give element 1 the type `Int`, or give every element the type "
        "`Bool` if that is what the array holds.  To keep values of "
        "different types in one array, wrap each in a constructor of one "
        "data type and make the array of that type."),
    "E162-element-type-open": ("E162", "check", ENDO + _fn("@Bool", "@Int",
        "let @Int = [mk(()), 1][0];\n  0"),
        "Give element 1 the literal's element type, or give every element "
        "the type `Int` if that is what the array holds.  To keep values of "
        "different types in one array, wrap each in a constructor of one "
        "data type and make the array of that type."),
    "E162-element-open": ("E162", "check", CASES["E162-open-variable"].source,
        "Give element 1 the type `fn(Int -> Int) effects(pure)`, or give "
        "every element element 1's type if that is what the array holds.  "
        "To keep values of different types in one array, wrap each in a "
        "constructor of one data type and make the array of that type."),
    "E503-projected": ("E503", "verify", _fn("@Option<Int>", "@Int",
        "match @Option<Int>.0 {\n    Some(@Nat) -> 1,\n    None -> 0\n  }"),
        "Add a precondition ruling out the inputs the counterexample "
        "shows.  Alternatively, guard the binding with an `if` whose "
        "condition holds the value non-negative — the path condition "
        "discharges the obligation in the then-branch."),
    "E502-path-safe-inner-subtraction": ("E502", "verify", _fn(
        "@Nat, @Nat, @Nat", "@Nat",
        "if @Nat.1 >= @Nat.0 then { @Nat.2 - (@Nat.1 - @Nat.0) } "
        "else { 0 }"),
        "Add a precondition that rules out the inputs the counterexample "
        "shows.  Alternatively, guard the subtraction with an `if` whose "
        "condition holds its left operand at least its right — the "
        "path condition discharges the obligation in the then-branch."),
    "E533-written-cell": ("E533", "check",
        "private forall<T> fn sneak(@T -> @T)\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n"
        "  handle[State<Option<T>>](@Nat = 3) {\n"
        "    put(@Option<T>) -> { resume(()) }\n  } in {\n    @T.0\n  }\n}\n\n"
        + _fn("@Int", "@Int", "sneak(@Int.0)"),
        "Declare the handler's state at its cell's type, `@Option<T>`, so "
        "every instantiation's state is its cell."),
    "E202-predicate-binds-its-own-slot": ("E202", "check",
        "type P = { @Int | { let @Bool = true; @Bool.0 } };\n\n"
        + _helper("take", "@P -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)"),
        "Pass a value of the type argument 0 takes, or convert the current "
        "value (e.g. int_to_nat(...), int_to_float(...)) to it."),
    "E337-exn-two-arguments": ("E337", "check", _fn("@Unit", "@Int",
        "handle[Exn<Int, Bool>] {\n    throw(@Int) -> { 0 }\n  } in {\n"
        "    1\n  }"),
        "Write the handler with a single concrete type argument: "
        "`handle[Exn<Int>]`."),
    "E321-field-not-written": ("E321", "check", _fn("@Int", "@Int",
        "match None {\n    Some(@Int, @Int) -> 1,\n    None -> 0\n  }"),
        "Give 'Some' exactly 1 sub-pattern(s), one per field."),
    "E341-body-type-not-written": ("E341", "check", _fn("@Unit", "@Int",
        "let @Array<Int> = handle[Exn<Int>] {\n    throw(@Int) -> { 0 }\n"
        "  } in {\n    []\n  };\n  0"),
        "Make the clause's value the handled body's type: replace '0' with "
        "'[]', or give the handled body the clause's type."),
    "E126-int": ("E126", "check", CASES["E126-int"].source,
        "Turn the predicate into a Bool-valued expression over the binder, "
        "such as a comparison with zero: `{ @Int | @Int.0 > 0 }`."),
    "E126-not-numeric": ("E126", "check",
        "type P = { @String | @String.0 };\n\n" + _fn("@P", "@Int", "0"),
        "Turn the predicate into a Bool-valued expression over the binder, "
        "such as a comparison of it with a bound."),
    "E128-function-bound": ("E128", "check", _fn("@Bool", "@Bool",
        "forall(@Int, fn(@Int -> @Int) effects(pure) { @Int.0 }, "
        "fn(@Int -> @Bool) effects(pure) { true })"),
        "Pass an integer bound, such as an array's length, and index the "
        "collection inside the predicate."),
    "E503-projected-clause": ("E503", "verify", _fn("@Int, @Bool", "@Int",
        _DESTRUCTURE_IF.format("Nat")),
        "Add a precondition ruling out the bad inputs: "
        "`requires(@Int.0 >= 0)`.  Alternatively, guard the binding with an "
        "`if` whose condition holds the value non-negative — the path "
        "condition discharges the obligation in the then-branch."),
    "E505-projected-clause": ("E505", "verify", POS + _fn(
        "@Int, @Bool", "@Int", _DESTRUCTURE_IF.format("Pos")),
        "Add a precondition under which the narrowed value satisfies the "
        "predicate: `requires(!@Bool.0)`.  Alternatively, guard the binding "
        "with an `if` whose condition is the predicate — the path condition "
        "discharges the obligation in the then-branch."),
    "E125-generic-state": ("E125", "check", _fn(
        "@T", "@Unit", "put(@T.0)", forall="T", eff="<IO>"),
        "Add State<T> to the effects clause of 'f': `effects(<IO, State<T>>)`."
        "  Or perform it inside a handle[State<T>] block, whose body permits "
        "it."),
    "E125-two-type-arguments": ("E125", "check",
        "effect Two<A, B> {\n  op two(A -> B);\n}\n\n" + _fn("@Int", "@Bool",
            "forall(@Int, 3, fn(@Int -> @Bool) effects(<Two<Int, Bool>>) "
            "{ true })", eff="<IO>"),
        "Add Two<Int, Bool> to the effects clause of 'f': "
        "`effects(<IO, Two<Int, Bool>>)`.  Or write a predicate whose "
        "effects the call site permits."),
    # PR 1859 review, round 4.
    # E337: an argument E340 does not lower as written gets no handler.
    "E337-inline-refinement": ("E337", "check", _fn("@Unit", "@Int",
        "handle[State<{ @Int | @Int.0 > 0 }, Int>](@Int = 1) {\n"
        + _STATE_CLAUSES),
        "Write handle[State<T>] with a single concrete type argument for T, "
        "a type name: a type written inline is named by a type alias "
        "first."),
    "E337-inline-type-parameter": ("E337", "check", _fn("@T", "@Int",
        "handle[State<fn(T -> T) effects(pure), Int>](@Int = 1) {\n"
        + _STATE_CLAUSES, forall="T"),
        "Write handle[State<T>] with a single concrete type argument for T, "
        "a type name."),
    # E341: no base value for a refined type, at any depth.
    "E341-refined-body": ("E341", "check", POS + _fn("@Pos", "@Int",
        "let @Pos = handle[Exn<Int>] {\n    throw(@Int) -> { true }\n"
        "  } in {\n    @Pos.0\n  };\n  0"),
        "Make the clause's value the handled body's type, "
        "`{ @Int | @Int.0 > 0 }`, or give the handled body the clause's "
        "type."),
    "E341-result-of-refined": ("E341", "check", POS + _fn(
        "@Result<Pos, Int>", "@Int",
        "let @Result<Pos, Int> = handle[Exn<Int>] {\n    throw(@Int) -> "
        "{ true }\n  } in {\n    @Result<Pos, Int>.0\n  };\n  0"),
        "Make the clause's value the handled body's type, "
        "`Result<{ @Int | @Int.0 > 0 }, Int>`, or give the handled body the "
        "clause's type."),
    # E137 / E127: a `where` helper's inherited type parameter is no
    # measure, though a data type shares its name.
    "E137-inherited-type-parameter": ("E137", "check", _WHERE_BOX.format(
        "@Box", "g(@Box.0)", "", "g(@Box.0)"),
        "Give 'g' a measure that strictly decreases on every recursive call "
        "and stays non-negative: a decreases() clause over a parameter that "
        "shrinks on every call. Every function on the cycle needs its own "
        "measure unless it declares Diverge. If the recursion is not meant "
        "to end, as in a server or read-eval loop, declare it: "
        "effects(<Diverge>), or effects(<Diverge, IO>) with IO; every "
        "function that calls it must declare Diverge too."),
    "E127-inherited-type-parameter": ("E127", "check", _WHERE_BOX.format(
        "@Box, @Float64", "g(@Box.0, 1.0)",
        "    decreases(@Float64.0)\n", "g(@Box.0, @Float64.0)"),
        "Measure something that shrinks toward a floor: a Nat or Int "
        "counter, a value of a data type, or an array's length."),
    # written_type: inside `forall<Count>` the name is the parameter, so
    # `{ @Count | … }` over the alias `Count = Nat` is no spelling there.
    "E202-alias-shadowed-by-a-type-parameter": ("E202", "check",
        "type Count = Nat;\n\ntype Positive = { @Count | @Count.0 > 0 };"
        "\n\n" + _helper("take", "@Positive -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)", forall="Count"),
        "Pass a value of the type argument 0 takes, or convert the current "
        "value (e.g. int_to_nat(...), int_to_float(...)) to it."),
}


@pytest.mark.parametrize("name", sorted(WHOLE))
def test_the_fix_is_the_whole_text(name: str) -> None:
    code, stage, source, text = WHOLE[name]
    assert _the(code, stage, source).fix == text


#: The WHOLE cells that pin a branch no other cell every pull request runs
#: reaches.  The parametrised cells above run as a weekly sample, and the
#: Mutation (diff) lane runs the sample: at PR 1859's f81d70b3 it reported
#: survivors in branches whose cells the sample left out.  These run
#: unsampled, in the one test below.
UNSAMPLED = (
    "E125-generic-state", "E125-two-type-arguments", "E126-int",
    "E126-not-numeric", "E128-function-bound", "E162-element-open",
    "E216-nothing-expected", "E321-field-not-written", "E321-two-fields",
    "E337-exn-two-arguments", "E337-the-state-only",
    "E341-body-type-not-written", "E503-projected-clause",
    "E505-projected-clause",
    # PR 1859 review, round 4: each red at 3558db6d.
    "E337-inline-refinement", "E337-inline-type-parameter",
    "E341-refined-body", "E341-result-of-refined",
    "E137-inherited-type-parameter", "E127-inherited-type-parameter",
    "E202-alias-shadowed-by-a-type-parameter",
)


def test_every_unsampled_branch_text_is_whole() -> None:
    moved: dict[str, str] = {}
    for name in UNSAMPLED:
        code, stage, source, text = WHOLE[name]
        fix = _the(code, stage, source).fix
        if fix != text:
            moved[name] = fix
    assert moved == {}, moved


def test_a_projected_refinement_binding_shows_its_counterexample() -> None:
    """E505 at a projected value (a non-literal destructure's component)
    names the counterexample the solver gave, the input its clause rules
    out."""
    code, stage, source, _ = WHOLE["E505-projected-clause"]
    description = _the(code, stage, source).description
    assert "\n  Counterexample:\n      @Bool.0 = True\n" in description, (
        description)


def test_a_nested_refinement_keeps_its_inner_layer() -> None:
    """A refinement of a refinement whose predicate names the inner base
    keeps both predicates (CodeRabbit on PR #1857)."""
    from vera import ast as a
    from vera.types import INT, RefinedType, written_type
    inner = a.BinaryExpr(a.BinOp.GT, a.SlotRef("Int", None, 0), a.IntLit(0))
    outer = a.BinaryExpr(a.BinOp.LT, a.SlotRef("Int", None, 0), a.IntLit(10))
    text = written_type(RefinedType(RefinedType(INT, inner), outer))
    assert text == "{ @{ @Int | @Int.0 > 0 } | @Int.0 < 10 }", text


@pytest.mark.parametrize("where", ["parameter", "result", "row", "predicate",
                                   "none"])
def test_a_type_parameter_is_found_anywhere_in_the_type(where: str) -> None:
    """`_names_any` reads every part of a type expression (E340's alias
    guard): a parameter, the result, the effect row, a predicate."""
    from vera import ast as a
    from vera.checker.control import _names_any
    t, i = a.NamedType("T", None), a.NamedType("Int", None)
    pure = a.PureEffect()
    shapes = {
        "parameter": a.FnType((t,), i, pure),
        "result": a.FnType((i,), t, pure),
        "row": a.FnType((i,), i, a.EffectSet((a.EffectRef("State", (t,)),))),
        "predicate": a.RefinementType(i, a.BinaryExpr(
            a.BinOp.GT, a.SlotRef("T", None, 0), a.IntLit(0))),
        "none": a.FnType((i,), i, a.EffectSet((a.EffectRef("IO", None),))),
    }
    assert _names_any(shapes[where], {"T"}) is (where != "none")


@pytest.mark.parametrize(("marked", "file", "command"), [
    (True, "x.vera", "`tail -c +4 x.vera | iconv -f ISO-8859-1 -t UTF-8 > "
                     "x.utf8.vera`"),
    (False, "x.vera", "`iconv -f ISO-8859-1 -t UTF-8 x.vera > x.utf8.vera`"),
    (True, "-", "`tail -c +4 | iconv -f ISO-8859-1 -t UTF-8`"),
    (False, "-", "`iconv -f ISO-8859-1 -t UTF-8`"),
])
def test_the_e024_command_for_each_source(marked: bool, file: str,
                                          command: str) -> None:
    """The lines this PR changes in `source_not_utf8`: the mark dropped
    first for a marked file, for a named file and for stdin."""
    from vera.errors import source_not_utf8
    raw = (b"\xef\xbb\xbf" if marked else b"") + b"x \xe9"
    fix = source_not_utf8(raw, raw.index(b"\xe9"), file).fix
    assert command in fix, fix
    assert ("drops the file's UTF-8 byte-order mark" in fix) is (
        marked and file != "-"), fix


_E024_NOTE = (" That command reads the source as Latin-1 (ISO-8859-1); a "
              "source in another encoding names its own after `-f`. In a "
              "string literal, a character can also be written as an escape "
              "of its code point, such as `\\u{E9}` for é.")


def test_the_e024_fix_for_a_named_file_is_whole() -> None:
    """The named file's whole fix, with and without a UTF-8 byte-order
    mark: the sentence the mark adds, and nothing in its place without
    one."""
    from vera.errors import source_not_utf8
    fixes: dict[bool, str] = {}
    for marked in (True, False):
        raw = (b"\xef\xbb\xbf" if marked else b"") + b"x \xe9"
        fixes[marked] = source_not_utf8(raw, raw.index(b"\xe9"), "x.vera").fix
    assert fixes == {
        True: "Save the file as UTF-8: in its directory, `tail -c +4 x.vera "
              "| iconv -f ISO-8859-1 -t UTF-8 > x.utf8.vera` writes a UTF-8 "
              "copy, which then replaces x.vera. The command drops the "
              "file's UTF-8 byte-order mark before converting the rest."
              + _E024_NOTE,
        False: "Save the file as UTF-8: in its directory, `iconv -f "
               "ISO-8859-1 -t UTF-8 x.vera > x.utf8.vera` writes a UTF-8 "
               "copy, which then replaces x.vera." + _E024_NOTE,
    }, fixes


def test_repro_1778_e336_names_the_cell_type_as_written() -> None:
    source = CASES["E336-alias"].source
    fix = _the("E336", "check", source).fix
    assert "`@Pos`" in fix and "..." not in fix, fix


def test_repro_1763_e503_sentinel_takes_the_counterexample_binding() -> None:
    source = CASES["E503-issue-bool-nat"].source
    fix = _the("E503", "verify", source).fix
    assert "`requires(@Bool.0)`" in fix, fix
    assert "@Int" not in fix, fix


def test_repro_1763_e340_aliases_a_function_type_argument() -> None:
    diag = _the("E340", "check", CASES["E340-fn-type"].source)
    assert "inline function type" in diag.description, diag.description
    assert "`type Thrown = fn(Int -> Int) effects(pure);`" in diag.fix


def test_repro_1763_open_variable_types_are_not_named() -> None:
    for name in ("E162-open-variable", "E301-open-variable"):
        case = CASES[name]
        fix = _the(case.code, case.stage, case.source).fix
        assert "?" not in fix, (name, fix)
    fix = _the("E301", "check", E301_OPEN_ELSE).fix
    assert "?" not in fix, fix
    assert spans(fix) == ["fn(Int -> Int) effects(pure)"], fix


# =====================================================================
# #1858: a clause in the entry's terms, a guard in the site's
# =====================================================================
#
# E526, E527, E505 and E501 wrote `requires(<the operand at the site>)`.
# A slot reference names the nearest binding of its type, so an operand a
# `let`, a pattern or a destructure binds names a parameter (or nothing)
# at the entry.  The `requires` is now offered only where it reads at the
# entry as at the site and the solver confirms it discharges the
# obligation; the guard each fix names is written around the site, where
# its operands are the site's own.  Each cell is a code x the operand's
# binding: a parameter, a `let` of a parameter's type, a `let` of another
# type, a pattern binder, a destructured component.

NEED = ("private fn need(@Int -> @Int)\n  requires(@Int.0 != 0)\n"
        "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n\n")
SMALL_NAT = "type Small = { @Nat | @Nat.0 < 10 };\n\n"
SMALL_POS = POS + "type Small = { @Pos | @Pos.0 < 10 };\n\n"
_ARM = ("match @Option<Int>.0 {{\n    Some(@Int) -> {0},\n"
        "    None -> 0\n  }}")
_DESTRUCTURE = "let Tuple<@Int, @Int> = Tuple(@Int.0 - 1, 1);\n  "


@dataclass(frozen=True)
class _Entry:
    code: str
    source: str
    #: The expression the guard is written around, as the source has it.
    site: str
    #: The `requires` the fix offers, or `None` where it offers none.
    clause: str | None
    #: The `requires` the base text offered, applied in the honesty cell.
    base: str | None = None


ENTRY: dict[str, _Entry] = {
    # --- E526: the divisor ---------------------------------------------
    "E526-param": _Entry(
        "E526", _fn("@Int", "@Int", "10 / @Int.0"), "10 / @Int.0",
        "requires(@Int.0 != 0)"),
    "E526-two-params": _Entry(
        "E526", _fn("@Int, @Int", "@Int", "@Int.0 / @Int.1"),
        "@Int.0 / @Int.1", "requires(@Int.1 != 0)"),
    "E526-grouped": _Entry(
        "E526", _fn("@Int, @Int", "@Int", "10 / (@Int.0 - @Int.1)"),
        "10 / (@Int.0 - @Int.1)", "requires(@Int.0 - @Int.1 != 0)"),
    "E526-let-same-type": _Entry(
        "E526", _fn("@Int", "@Int", "let @Int = @Int.0 - 1;\n  10 / @Int.0"),
        "10 / @Int.0", None, base="requires(@Int.0 != 0)"),
    "E526-let-other-type": _Entry(
        "E526", _fn("@Nat", "@Int", "let @Int = 0 - @Nat.0;\n  10 / @Int.0"),
        "10 / @Int.0", None, base="requires(@Int.0 != 0)"),
    "E526-let-other-type-flag": _Entry(
        "E526", _fn("@Bool", "@Int",
                    "let @Int = if @Bool.0 then { 1 } else { 0 };\n"
                    "  10 / @Int.0"),
        "10 / @Int.0", "requires(@Bool.0)", base="requires(@Int.0 != 0)"),
    "E526-pattern": _Entry(
        "E526", _fn("@Int, @Option<Int>", "@Int", _ARM.format("10 / @Int.0")),
        "10 / @Int.0", None, base="requires(@Int.0 != 0)"),
    # A `@Nat` subtraction in the clause is safe only under the site's
    # path: at the entry it is an obligation of its own (E502), so no
    # clause is offered (PR 1857's rule, applied to this code).
    # An addition the site's path keeps in range, which at the entry
    # overflows at the largest `@Int`: `requires(@Int.0 + 1 != 0)` would
    # add a trap the program does not have, so it is not offered, and the
    # counterexample's clause, which holds no arithmetic, is (PR 1859
    # review).
    "E526-overflow-under-path": _Entry(
        "E526", _fn("@Int", "@Int",
                    "if @Int.0 < 9223372036854775807 then {\n"
                    "    10 / (@Int.0 + 1)\n  } else {\n    0\n  }"),
        "10 / (@Int.0 + 1)", "requires(@Int.0 >= 0)"),
    "E526-nat-sub-under-path": _Entry(
        "E526", _fn("@Nat, @Nat", "@Int",
                    "if @Nat.1 >= @Nat.0 then {\n    10 / (@Nat.1 - @Nat.0)\n"
                    "  } else {\n    0\n  }"),
        "10 / (@Nat.1 - @Nat.0)", None,
        base="requires(@Nat.1 - @Nat.0 != 0)"),
    "E526-destructure": _Entry(
        "E526", _fn("@Int, @Int", "@Int", _DESTRUCTURE + "10 / @Int.1"),
        "10 / @Int.1", None, base="requires(@Int.1 != 0)"),
    # --- E527: never a `requires`; the guard around the access ----------
    "E527-param": _Entry(
        "E527", _fn("@Array<Int>, @Int", "@Int", "@Array<Int>.0[@Int.0]",
                    req="@Int.0 < 0"),
        "@Array<Int>.0[@Int.0]", None),
    "E527-let-same-type": _Entry(
        "E527", _fn("@Array<Int>, @Int", "@Int",
                    "let @Int = 0 - 1;\n  @Array<Int>.0[@Int.0]"),
        "@Array<Int>.0[@Int.0]", None,
        base="requires(0 <= @Int.0 && @Int.0 < array_length(@Array<Int>.0))"),
    "E527-let-other-type": _Entry(
        "E527", _fn("@Array<Int>, @Nat", "@Int",
                    "let @Int = 0 - 1 - @Nat.0;\n  @Array<Int>.0[@Int.0]"),
        "@Array<Int>.0[@Int.0]", None,
        base="requires(0 <= @Int.0 && @Int.0 < array_length(@Array<Int>.0))"),
    "E527-pattern": _Entry(
        "E527", _fn("@Array<Int>, @Int", "@Int",
                    "match Some(0 - 1) {\n    Some(@Int) -> "
                    "@Array<Int>.0[@Int.0],\n    None -> 0\n  }"),
        "@Array<Int>.0[@Int.0]", None,
        base="requires(0 <= @Int.0 && @Int.0 < array_length(@Array<Int>.0))"),
    "E527-destructure": _Entry(
        "E527", _fn("@Array<Int>, @Int", "@Int",
                    "let Tuple<@Int, @Int> = Tuple(0 - 1, 1);\n"
                    "  @Array<Int>.0[@Int.1]"),
        "@Array<Int>.0[@Int.1]", None,
        base="requires(0 <= @Int.1 && @Int.1 < array_length(@Array<Int>.0))"),
    # --- E505: the predicate at the narrowed value ----------------------
    "E505-param": _Entry(
        "E505", POS + _fn("@Int", "@Int", "let @Pos = @Int.0;\n  0"),
        "@Int.0", "requires(@Int.0 > 0)"),
    "E505-param-expression": _Entry(
        "E505", POS + _fn("@Int", "@Int", "let @Pos = @Int.0 - 1;\n  0"),
        "@Int.0 - 1", "requires(@Int.0 - 1 > 0)",
        base="requires(@Int.0 > 0)"),
    "E505-return": _Entry(
        "E505", POS + _fn("@Int", "@Pos", "@Int.0 - 1"),
        "@Int.0 - 1", "requires(@Int.0 - 1 > 0)",
        base="requires(@Int.0 > 0)"),
    "E505-nat-base": _Entry(
        "E505", SMALL_NAT + _fn("@Int", "@Int", "let @Small = @Int.0;\n  0"),
        "@Int.0", "requires(@Int.0 >= 0 && @Int.0 < 10)",
        base="requires(@Nat.0 >= 0 && @Nat.0 < 10)"),
    "E505-chain": _Entry(
        "E505", SMALL_POS + _fn("@Int", "@Int", "let @Small = @Int.0;\n  0"),
        "@Int.0", "requires(@Int.0 > 0 && @Int.0 < 10)",
        base="requires((@Int.0 > 0) && (@Pos.0 < 10))"),
    "E505-nat-chain": _Entry(
        "E505", "type NZ = { @Nat | @Nat.0 > 0 };\n\n"
        "type NSmall = { @NZ | @NZ.0 < 10 };\n\n"
        + _fn("@Int", "@Int", "let @NSmall = @Int.0;\n  0"),
        "@Int.0", "requires(@Int.0 >= 0 && @Int.0 > 0 && @Int.0 < 10)",
        base="requires(@Nat.0 >= 0 && (@Nat.0 > 0) && (@NZ.0 < 10))"),
    "E505-let-same-type": _Entry(
        "E505", POS + _fn("@Int", "@Int",
                          "let @Int = @Int.0 - 1;\n  let @Pos = @Int.0;\n  0"),
        "@Int.0", None, base="requires(@Int.0 > 0)"),
    "E505-let-other-type": _Entry(
        "E505", POS + _fn("@Nat", "@Int",
                          "let @Int = 0 - @Nat.0;\n  let @Pos = @Int.0;\n  0"),
        "@Int.0", None, base="requires(@Int.0 > 0)"),
    "E505-pattern": _Entry(
        "E505", POS + _fn("@Int, @Option<Int>", "@Int", _ARM.format(
            "{\n      let @Pos = @Int.0;\n      0\n    }")),
        "@Int.0", None, base="requires(@Int.0 > 0)"),
    "E505-destructure": _Entry(
        "E505", POS + _fn("@Int, @Int", "@Int",
                          _DESTRUCTURE + "let @Pos = @Int.1;\n  0"),
        "@Int.1", None, base="requires(@Int.0 > 0)"),
    "E505-sub-pattern": _Entry(
        "E505", POS + _fn("@Int, @Option<Int>", "@Int",
                          "match @Option<Int>.0 {\n    Some(@Pos) -> 0,\n"
                          "    None -> 0\n  }"),
        "Some(@Pos)", None, base="requires(@Int.0 > 0)"),
    # --- E501: the callee's precondition at the arguments ---------------
    "E501-param": _Entry(
        "E501", NEED + _fn("@Int", "@Int", "need(@Int.0)"), "need(@Int.0)",
        "requires(@Int.0 != 0)"),
    "E501-param-expression": _Entry(
        "E501", NEED + _fn("@Int", "@Int", "need(@Int.0 - 1)"),
        "need(@Int.0 - 1)", "requires(@Int.0 - 1 != 0)"),
    "E501-let-same-type": _Entry(
        "E501", NEED + _fn("@Int", "@Int",
                           "let @Int = @Int.0 - 1;\n  need(@Int.0)"),
        "need(@Int.0)", None, base="requires(@Int.0 != 0)"),
    "E501-let-other-type": _Entry(
        "E501", NEED + _fn("@Nat", "@Int",
                           "let @Int = 0 - @Nat.0;\n  need(@Int.0)"),
        "need(@Int.0)", None, base="requires(@Int.0 != 0)"),
    "E501-pattern": _Entry(
        "E501", NEED + _fn("@Int, @Option<Int>", "@Int",
                           _ARM.format("need(@Int.0)")),
        "need(@Int.0)", None, base="requires(@Int.0 != 0)"),
    "E501-destructure": _Entry(
        "E501", NEED + _fn("@Int, @Int", "@Int",
                           _DESTRUCTURE + "need(@Int.1)"),
        "need(@Int.1)", None, base="requires(@Int.1 != 0)"),
    "E501-builtin-domain": _Entry(
        "E501", _fn("@Int", "@Int", 'string_char_code("abc", @Int.0)'),
        'string_char_code("abc", @Int.0)', None),
    # A `where` helper, which the flat registry does not hold: the report
    # resolves it through the caller's scope, as the call was (PR 1859
    # review), so the guard and the clause are both written.
    "E501-where-helper": _Entry(
        "E501", _fn("@Int", "@Int", "need(@Int.0)")
        + "where {\n  fn need(@Int -> @Int)\n    requires(@Int.0 != 0)\n"
        "    ensures(true)\n    effects(pure)\n  {\n    @Int.0\n  }\n}\n",
        "need(@Int.0)", "requires(@Int.0 != 0)"),
}

#: The codes whose fix writes a guard as code: E505's names its condition
#: in prose.
_GUARDED = frozenset({"E526", "E527", "E501"})


def _entry_fix(name: str) -> str:
    cell = ENTRY[name]
    return _the(cell.code, "verify", cell.source).fix


def _requires_spans(fix: str) -> list[str]:
    return [s for s in spans(fix) if s.startswith("requires(")]


@pytest.mark.parametrize("name", sorted(ENTRY))
def test_a_requires_is_offered_only_in_the_entrys_terms(name: str) -> None:
    """The clause offered is exactly the cell's, and none where the
    operand is not the entry's: a `let`, a pattern binder or a destructured
    component names a parameter, or nothing, at the entry."""
    cell = ENTRY[name]
    fix = _entry_fix(name)
    assert _requires_spans(fix) == (
        [cell.clause] if cell.clause is not None else []), (name, fix)
    if cell.clause is None:
        assert "e.g." not in fix, (name, fix)


@pytest.mark.parametrize(
    "name", sorted(n for n, c in ENTRY.items() if c.clause is not None))
def test_the_entry_clause_applied_clears_the_code(name: str) -> None:
    cell = ENTRY[name]
    [clause] = _requires_spans(_entry_fix(name))
    fixed = _once(cell.source, "requires(true)", clause)
    codes = _passed_codes("verify", fixed)
    assert not codes & {"E005", "E006", "E130"}, (name, fixed, codes)
    assert cell.code not in codes, (name, fixed, sorted(codes))


@pytest.mark.parametrize(
    "name", sorted(n for n, c in ENTRY.items() if c.code in _GUARDED))
def test_the_site_guard_applied_clears_the_code(name: str) -> None:
    """The guard, from the fix's text with `<default>` given a value,
    written around the site: its operands are the site's, so it clears
    whatever binds them."""
    cell = ENTRY[name]
    fix = _entry_fix(name)
    guards = [s for s in spans(fix) if s.startswith("if ")]
    assert len(guards) == 1, (name, fix)
    fixed = _once(cell.source, cell.site,
                  guards[0].replace("<default>", "0"))
    codes = _passed_codes("verify", fixed)
    assert not codes & {"E005", "E006", "E130"}, (name, fixed, codes)
    assert cell.code not in codes, (name, fixed, sorted(codes))


@pytest.mark.parametrize(
    "name", sorted(n for n, c in ENTRY.items() if c.base is not None))
def test_the_base_entry_clause_does_not_clear(name: str) -> None:
    """The gate can fail: the base text's `requires`, written at the entry
    the same way, leaves the code firing or names a slot the entry lacks."""
    cell = ENTRY[name]
    assert cell.base is not None
    codes = _codes("verify", _once(cell.source, "requires(true)", cell.base))
    # E130: a slot the entry lacks; E502: a `@Nat` subtraction the site's
    # path made safe and the entry does not.
    assert cell.code in codes or codes & {"E130", "E502"}, (
        name, sorted(codes))


def test_a_refinement_binding_an_alias_parameter_is_not_written() -> None:
    """`type NonEmpty<T>`'s predicate binds `@Array<T>.0`, the alias's own
    parameter: at `NonEmpty<Int>` no fix outside the alias can write it
    (E136), so the fix names no type (PR 1859 review)."""
    source = (
        "type NonEmpty<T> = { @Array<T> | array_length(@Array<T>.0) > 0 };"
        "\n\n" + _helper("take", "@NonEmpty<Int> -> @Int", "0")
        + _fn("@Bool", "@Int", "take(@Bool.0)"))
    fix = _the("E202", "check", source).fix
    assert "<T>" not in fix and "{ @" not in fix, fix


def test_e533_names_no_cell_it_cannot_write() -> None:
    """A cell over a type parameter the template does not declare (a
    `where` helper's, over its parent's) is written in no scope the fix
    names: the sentence stands without it, never `@None` (PR 1859
    review)."""
    from types import SimpleNamespace

    from vera.typed import _state_fix
    from vera.types import TypeVar
    fix = _state_fix(
        SimpleNamespace(state=None),  # type: ignore[arg-type]
        SimpleNamespace(cell=TypeVar("U")),  # type: ignore[arg-type]
        SimpleNamespace(decl=SimpleNamespace(  # type: ignore[arg-type]
            forall_vars=("T",), params=())), "")
    assert fix == ("Declare the handler's state at its cell's type, so every "
                   "instantiation's state is its cell."), fix


_INLINE = "fn(Int -> Int) effects(pure)"


def test_e340_names_an_alias_no_type_parameter_shadows() -> None:
    """Inside `forall<Cell>` the name `Cell` is the type parameter, so an
    alias the fix calls `Cell` would not be the type `handle[State<Cell>]`
    reads there (PR 1859 review): the fix takes the next free name, and the
    program it makes checks clean."""
    source = _fn("@Cell", "@Int",
                 f"handle[State<{_INLINE}>](@{_INLINE} = "
                 f"fn(@Int -> @Int) effects(pure) {{ @Int.0 }}) {{\n"
                 f"    get(@Unit) -> {{ resume(fn(@Int -> @Int) "
                 f"effects(pure) {{ @Int.0 }}) }},\n"
                 f"    put(@{_INLINE}) -> {{ resume(()) }}\n"
                 f"  }} in {{\n    0\n  }}", forall="Cell")
    decl, handler, state = spans(_the("E340", "check", source).fix)
    # The first free name: only `Cell` is taken, so `Cell2`.
    assert decl == f"type Cell2 = {_INLINE};", decl
    fixed = decl + "\n\n" + source.replace(
        f"handle[State<{_INLINE}>]", handler).replace(f"@{_INLINE}", state)
    assert _codes("check", fixed) == set(), (decl, fixed)


_ONE_INT = _fn("@Int", "@Int", "@Int.0")


def test_repro_1858_a_reset_context_reads_no_entry_scope() -> None:
    """A context's entry scope ends with the function it was recorded for
    (corrects PR 1857's table, keyed by `id(smt)` and never cleared).  On
    the warm context a verifier shares, the next declaration's context is
    the same object, reset: a clause asked there must find no entry, where
    the table still held the last function's and offered a `requires` in
    its terms."""
    import z3

    from vera.smt import SlotEnv, SmtContext
    from vera.verifier import ContractVerifier

    checked = pipeline.check(_ONE_INT)
    smt = SmtContext()
    verifier = ContractVerifier(checked.typed, source=checked.source,
                                shared_smt=smt)
    verifier.verify_program(checked.typed.program)
    smt.reset()
    var = smt.declare_int("@Int.0")
    site = SlotEnv().push("Int", var)
    pred = vera.ast.BinaryExpr(
        vera.ast.BinOp.NEQ, vera.ast.SlotRef("Int", None, 0),
        vera.ast.IntLit(0))
    assert verifier._discharging_clause(
        smt, var != z3.IntVal(0), [], None, site_env=site,
        exprs=(pred,)) is None


def test_a_warm_sessions_entry_scope_is_its_own_and_one() -> None:
    """Two verifications through one warm session: each reads its own
    function's entry, held on the one context the session keeps, so
    nothing accumulates across the documents a language server verifies."""
    from vera.obligations.session import VerificationSession
    from vera.verifier import ContractVerifier

    session = VerificationSession()
    session.verify_source(_ONE_INT)
    assert session._smt is not None
    scope = session._smt.entry_scope
    assert scope is not None and [n for n, _ in scope[1]] == ["@Int.0"]
    session.verify_source(_fn("@Bool, @Nat", "@Int", "0"))
    scope = session._smt.entry_scope
    assert scope is not None
    assert [n for n, _ in scope[1]] == ["@Bool.0", "@Nat.0"], scope
    # A cold run keeps no table of entry scopes beside the contexts, one
    # entry per function verified.
    from vera.smt import SlotEnv
    checked = pipeline.check(_ONE_INT + "\n" + _fn(
        "@Bool", "@Int", "0").replace("fn f(", "fn g("))
    verifier = ContractVerifier(checked.typed, source=checked.source)
    verifier.verify_program(checked.typed.program)
    held = [name for name, value in vars(verifier).items()
            if isinstance(value, dict) and any(
                isinstance(v, tuple) and v and isinstance(v[0], SlotEnv)
                for v in value.values())]
    assert held == [], held


def test_repro_1858_e526_shadowed_divisor() -> None:
    """The issue's program: the divisor is the `let`, so base's
    `requires(@Int.0 != 0)` (the parameter) left E526 firing.  No clause
    is offered, and the guard, written at the division, clears it."""
    source = _fn("@Int", "@Int", "let @Int = @Int.0 - 1;\n  10 / @Int.0")
    fix = _the("E526", "verify", source).fix
    assert "requires(@Int.0 != 0)" not in fix, fix
    assert "E526" in _codes(
        "verify", _once(source, "requires(true)", "requires(@Int.0 != 0)"))
    guard = next(s for s in spans(fix) if s.startswith("if "))
    assert "E526" not in _codes("verify", _once(
        source, "10 / @Int.0", guard.replace("<default>", "0")))


# =====================================================================
# E024: the conversion command, run for real
# =====================================================================

def _run_pipeline(command: str, cwd: Path) -> None:
    """Run a fix's shell pipeline, `a | b > out`, without a shell."""
    body, _, out = command.partition(" > ")
    stages = [shlex.split(stage) for stage in body.split(" | ")]
    data = b""
    for i, argv in enumerate(stages):
        done = subprocess.run(argv, cwd=cwd, input=data if i else None,
                              capture_output=True, check=True)
        data = done.stdout
    (cwd / out.strip()).write_bytes(data)


@pytest.mark.skipif(os.name != "posix",
                    reason="the fix's command is a POSIX pipeline "
                           "(tail and iconv)")
@pytest.mark.parametrize("marked", [True, False], ids=["marked", "unmarked"])
def test_repro_1763_e024_command_converts_a_latin1_file(
        tmp_path: Path, marked: bool) -> None:
    """A Latin-1 file, with and without a UTF-8 byte-order mark: the copy
    the fix's command writes passes `vera check`."""
    program = _fn("@Unit", "@String", '"caf\xe9"').encode("latin-1")
    path = tmp_path / "latin.vera"
    path.write_bytes((b"\xef\xbb\xbf" if marked else b"") + program)
    done = pipeline.cli("check", "--json", path)
    (diag,) = json.loads(done.stdout)["diagnostics"]
    assert diag["error_code"] == "E024", diag
    (command,) = [s for s in spans(diag["fix"]) if "iconv" in s]
    assert ("tail -c +4" in command) is marked, command
    _run_pipeline(command, tmp_path)
    copy = tmp_path / "latin.utf8.vera"
    assert copy.read_bytes().startswith(b"public fn f(")
    assert pipeline.check(copy).ok, pipeline.check(copy).diagnostics


# =====================================================================
# No fix reaches a message renderer
# =====================================================================

_RENDERERS = frozenset({"pretty_type", "pretty_inferred_type",
                        "pretty_effect", "canonical_type_name"})


def _reaches_a_renderer(path: Path, root: Path) -> list[str]:
    """Each `fix=` in *path* whose expression, the locals it reads, or a
    `*_fix` / `*_form` / `*_text` helper it calls, renders a type in the
    message form."""
    source = path.read_text(encoding="utf-8")
    tree = pyast.parse(source)
    funcs = {n.name: n for n in pyast.walk(tree)
             if isinstance(n, pyast.FunctionDef)}

    def called(node: pyast.AST) -> set[str]:
        out = set()
        for sub in pyast.walk(node):
            if isinstance(sub, pyast.Call):
                f = sub.func
                if isinstance(f, pyast.Name):
                    out.add(f.id)
                elif isinstance(f, pyast.Attribute):
                    out.add(f.attr)
        return out

    def reaches(expr: pyast.AST, fn: pyast.FunctionDef | None,
                seen: set[str]) -> bool:
        names = called(expr)
        if names & _RENDERERS:
            return True
        for name in names:
            if (name in funcs and name not in seen
                    and name.endswith(("_fix", "_form", "_text"))):
                seen.add(name)
                body = funcs[name]
                for stmt in pyast.walk(body):
                    if (isinstance(stmt, (pyast.Return, pyast.Assign))
                            and stmt.value is not None
                            and reaches(stmt.value, body, seen)):
                        return True
        if fn is not None:
            local = {n.id for n in pyast.walk(expr)
                     if isinstance(n, pyast.Name)}
            for stmt in pyast.walk(fn):
                if isinstance(stmt, pyast.Assign):
                    targets = {t.id for t in stmt.targets
                               if isinstance(t, pyast.Name)}
                    if targets & local and not targets & seen:
                        seen |= targets
                        if reaches(stmt.value, fn, seen):
                            return True
        return False

    found = []
    for fn in funcs.values():
        for node in pyast.walk(fn):
            if not isinstance(node, pyast.Call):
                continue
            for kw in node.keywords:
                if kw.arg == "fix" and reaches(kw.value, fn, set()):
                    found.append(f"{path.relative_to(root).as_posix()}:"
                                 f"{kw.value.lineno}")
    return found


def test_no_fix_renders_a_type_in_the_message_form() -> None:
    """#1778's class gate: a type a fix names is the program's spelling.
    At base it listed 31 sites."""
    package = Path(vera.__file__).resolve().parent
    found = [site for path in sorted(package.rglob("*.py"))
             for site in _reaches_a_renderer(path, package.parent)]
    assert found == [], found


# =====================================================================
# #1684's fix sites (PR 1855), under #1778's rule
# =====================================================================

_DUP = _helper("dup", "@T -> @Tuple<T, T>", "Tuple(@T.0, @T.0)", forall="T")
_REFINED = "{ @Int | @Int.0 > 0 }"
_E170_REFINED = _DUP + _fn(
    "@Unit", "@Int",
    f"let Tuple<@Option<{_REFINED}>, @Option<String>> = dup(None);\n  5")


def test_e170_writes_a_refined_binding_as_the_program_writes_it() -> None:
    """E170's binding is code the reader pastes: at a refinement it is
    written with its predicate, and applied it clears the code."""
    fix = _the("E170", "check", _E170_REFINED).fix
    (binding,) = spans(fix)
    assert binding == f"@Option<{_REFINED}>", fix
    fixed = _E170_REFINED.replace("@Option<String>", binding)
    assert _codes("check", fixed) == set(), fixed


def test_the_e170_message_form_binding_does_not_clear() -> None:
    """The honesty cell: the binding as the merge of PR 1855 wrote it, in
    the message form, does not clear the code when applied."""
    fixed = _E170_REFINED.replace("@Option<String>", "@Option<{@Int | ...}>")
    assert _codes("check", fixed) != set(), fixed


def test_e170_at_a_type_parameter_writes_no_binding() -> None:
    """A binding the type parameter `U` stands in is not one the fix can
    write whole; the sentence names `U` as written, and no `?`."""
    source = _DUP + _fn(
        "@U", "@Int",
        "let Tuple<@Option<U>, @Option<String>> = dup(None);\n  5",
        forall="U")
    assert _the("E170", "check", source).fix == (
        "Write binding 2 so that it gives T `U`, the type binding 1 gives "
        "it, at the type argument of Option in component 2.")


def test_e170_at_an_empty_literal_names_its_element_type_in_words() -> None:
    """An empty literal's element type is no type variable a reader can
    name (`?`): the fix says what it is, and the binding it writes,
    applied, clears the code."""
    source = _DUP + _fn(
        "@Unit", "@Int",
        "let Tuple<@Array<Int>, @Array<String>> = dup([]);\n  0")
    fix = _the("E170", "check", source).fix
    assert fix == ("Write binding 2 as `@Array<Int>`, the type binding 1 "
                   "gives the empty literal's element type."), fix
    (binding,) = spans(fix)
    fixed = source.replace("@Array<String>", binding)
    assert _codes("check", fixed) == set(), fixed


def test_the_applied_value_fix_applied_clears_e202() -> None:
    """`apply_fn` of a value whose type is the enclosing function's own
    `T`: the alias, the binding's type and the application, each pasted
    from the fix, clear the code."""
    source = _fn("@T", "@T", "apply_fn(@T.0, @T.0)", forall="T")
    fix = _the("E202", "check", source).fix
    signature, decl, binding, value = spans(fix)
    assert (signature, decl, binding, value) == (
        "fn(T -> T) effects(pure)",
        "type Applied<T> = fn(T -> T) effects(pure);", "@Applied<T>",
        "@T.0"), fix
    fixed = decl + "\n\n" + source.replace(
        "fn f(@T -> @T)", f"fn f(@T, {binding} -> @T)").replace(
        "apply_fn(@T.0, @T.0)", f"apply_fn({binding}.0, @T.0)")
    assert _codes("check", fixed) == set(), fixed


_STATE_T = ("handle[State<T>](@T = @T.0) {{\n    get(@Unit) -> {{ resume({0}) "
            "}},\n    put(@T) -> {{ resume(()) }}\n  }} in {{\n    {1}0\n  }}")

#: A rigid `T` with a value of it in scope: name -> (code, program, the
#: argument the fix's `@T.0` replaces).
_RIGID_IN_SCOPE: dict[str, tuple[str, str, str]] = {
    "E202-resume": ("E202", _fn("@T", "@Int", _STATE_T.format("9", ""),
                                forall="T"), "resume(9)"),
    "E204-operation": ("E204", _fn("@T", "@Int", _STATE_T.format(
        "@T.0", "put(9);\n    "), forall="T"), "put(9)"),
    "E241-ability": ("E241", _fn("@T", "@Bool", "eq(@T.0, 9)",
                                 forall="T where Eq<T>"), "eq(@T.0, 9)"),
}


def test_each_rigid_fix_with_a_value_in_scope_clears() -> None:
    """`_rigid_fix` names `@T.0` only where a `T` is bound at the site, so
    the slot it writes exists there: pasted in place of the argument, it
    clears each code.  The value's own type is written as the program
    writes it (`Int`), never the message form."""
    moved: dict[str, tuple[str, list[str]]] = {}
    for name, (code, source, argument) in _RIGID_IN_SCOPE.items():
        fix = _the(code, "check", source).fix
        slot, given = spans(fix)
        fixed = source.replace(argument, argument.replace("9", slot))
        if (slot, given) != ("@T.0", "Int") or _codes("check", fixed):
            moved[name] = (fix, sorted(_codes("check", fixed)))
    assert moved == {}, moved


def test_a_rigid_fix_with_no_value_in_scope_names_no_slot() -> None:
    """With no `T` bound at the site, the fix names a parameter to take,
    `@T`, and no slot reference."""
    source = ("type Fn<T> = fn(T -> Nat) effects(pure);\n\n"
              + _fn("@Fn<T>", "@Nat", "apply_fn(@Fn<T>.0, 9)", forall="T"))
    fix = _the("E202", "check", source).fix
    assert spans(fix) == ["@T", "Int"], fix


def test_an_unfixed_application_names_the_site_and_no_open_type() -> None:
    """E202 at an argument applied to a function a call left open: the
    span is the call as the site writes it, and the type to take is
    written, never `?`."""
    source = ENDO + _fn("@Unit", "@Nat", "abs(apply_fn(mk(()), 40))")
    fix = _the("E202", "check", source).fix
    assert spans(fix) == ["mk(())", "Int"] and "?" not in fix, fix


# =====================================================================
# PR 1859 review, round 4: a fix applied passes its stage
# =====================================================================

_HANDLER_HEAD = re.compile(r"handle\[[^\]]*\]")


def test_every_e337_handler_example_applied_passes_the_check() -> None:
    """Each E337 example, pasted over the handler's head, is a handler the
    check accepts: E340 lowers its argument as written.  An inline type
    (E337-inline-*) gets no example, which applied drew E340."""
    moved: dict[str, tuple[str, list[str]]] = {}
    for name, (code, stage, source, _) in WHOLE.items():
        if code != "E337":
            continue
        fix = _the(code, stage, source).fix
        heads = [s for s in spans(fix) if s.startswith("handle[")]
        # No example: an inline type, or no type at the site at all.
        if name.startswith("E337-inline-") or name == "E337-neither":
            if heads:
                moved[name] = (fix, [])
            continue
        (head,) = heads
        fixed = _HANDLER_HEAD.sub(lambda _: head, source, count=1)
        result = _run("check", fixed)
        if not result.ok:
            moved[name] = (fixed, sorted(d.error_code for d in result.errors))
    assert moved == {}, moved


def test_every_e341_example_applied_passes_the_check() -> None:
    """Each E341 replacement, applied, is a clause value the check accepts;
    a refined handled body (E341-refined-*, E341-result-of-refined) gets
    none, whose base value need not satisfy the predicate."""
    moved: dict[str, tuple[str, list[str]]] = {}
    for name, (code, stage, source, _) in WHOLE.items():
        if code != "E341":
            continue
        fix = _the(code, stage, source).fix
        found = re.search(r"replace '([^']*)' with '([^']*)'", fix)
        if name in ("E341-refined-body", "E341-result-of-refined"):
            if found:
                moved[name] = (fix, [])
            continue
        assert found, (name, fix)
        old, new = found.groups()
        fixed = _once(source, f"-> {{ {old} }}", f"-> {{ {new} }}")
        result = _run("check", fixed)
        if not result.ok:
            moved[name] = (fixed, sorted(d.error_code for d in result.errors))
    assert moved == {}, moved


_NEED_NATS = ("private fn need(@Nat, @Nat -> @Int)\n"
              "  requires(@Nat.1 >= @Nat.0)\n"
              "  requires(@Nat.1 - @Nat.0 > 0)\n"
              "  ensures(true)\n  effects(pure)\n{\n  0\n}\n\n")


def test_repro_an_e501_clause_adds_no_trap_at_the_entry() -> None:
    """A clause copied from the callee's precondition holds a `@Nat`
    subtraction its caller's path made safe (`if @Nat.1 >= @Nat.0`): at
    the caller's entry it can underflow, so offered it drew E502 there.
    The clause offered, applied, verifies; or none is offered."""
    source = _NEED_NATS + _fn(
        "@Nat, @Nat", "@Int",
        "if @Nat.1 >= @Nat.0 then { need(@Nat.1, @Nat.0) } else { 0 }")
    fix = _the("E501", "verify", source).fix
    for clause in _requires_spans(fix):
        fixed = _once(source, "requires(true)", clause)
        codes = _passed_codes("verify", fixed)
        assert not codes & {"E501", "E502"}, (clause, sorted(codes))


# =====================================================================
# #1684: E613's fix names binding the result at a type
# =====================================================================

_NONE_ORD = """\
private forall<T where Ord<T>> fn none_ord(@Unit -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  None
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match none_ord(()) {
    None -> 7,
    Some(@Int) -> @Int.0
  }
}
"""


def test_e613_s_binding_fix_applied_clears_the_code() -> None:
    """E613 at a variable no argument fixes and nothing gives a type (a
    `match` scrutinee) offers binding the result at a type, which fixes
    the variable (spec §5.9): the scrutinee bound by a `let` of such a
    type, as the fix says, passes the check with no E613."""
    fix = _the("E613", "check", _NONE_ORD).fix
    assert "bind its result at a type" in fix, fix
    fixed = _NONE_ORD.replace(
        "  match none_ord(()) {",
        "  let @Option<Int> = none_ord(());\n  match @Option<Int>.0 {")
    assert "E613" not in _passed_codes("check", fixed)


_WHERE_ONLY = """\
private forall<T where Ord<T>> fn where_only(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  7
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Int = where_only(());
  @Int.0
}
"""


def test_e613_offers_no_binding_where_the_result_holds_no_variable() -> None:
    """A variable only a `where` constraint names (`forall<T where Ord<T>>
    fn where_only(@Unit -> @Int)`): the result's type holds no `T`, so no
    binding of it fixes `T` (the program already binds it at `Int`, and
    E613 stands).  The fix offers only the parameter that carries `T`,
    and that remedy, applied as written, passes the check (PR 1864
    review: the binding remedy was offered here too, and could not
    clear)."""
    fix = _the("E613", "check", _WHERE_ONLY).fix
    assert "bind its result" not in fix, fix
    assert "give 'where_only' a parameter that carries T" in fix, fix
    fixed = (_WHERE_ONLY
             .replace("fn where_only(@Unit -> @Int)",
                      "fn where_only(@Unit, @T -> @Int)")
             .replace("where_only(())", "where_only((), 1)"))
    assert "E613" not in _passed_codes("check", fixed)
