"""#1503 — every guard and every obligation reads ONE classifier.

Two sources can disagree about an integer expression's type.  The checker
types an arithmetic expression bottom-up, synthesizing its operands with no
expected type, so a non-negative literal is `@Nat` and `0 - 3` is
`Nat - Nat`, i.e. `@Nat`.  The classifier the verifier and code generation
share (`vera.narrowing`) does not: a pure-literal subtraction is the #520
idiom for a negative `@Int` (spec §11.2.1 exempts it from the underflow guard
for exactly that reason), and in an `@Int` context spec §4.2 types an integer
literal from its context and §4.4 types the subtraction as the join of its
operands — `@Int`.  The checker's `@Nat` there is a claim about a value that
is -3.

The defect is a DECISION reading the checker's answer where the two
disagree.  Three readers did, all new on the release branch:

* the tuple-destructure widening guard (#1416's arm) OR-ed the checker's
  component type into its literal-source test, so
  `let Tuple<@Int, @Int> = Tuple(1, 0 - 3)` trapped on a valid -3;
* the verifier's destructure widening leg read the same table and PROVED
  the widening at Tier 1 for an `if`-produced tuple while the guard beside
  it trapped — an unsound verdict;
* a generic constructor field's target was the checker's instantiation
  INFERRED from the argument itself (`W(0 - 3)` is a `Wrap<Nat>` because
  `0 - 3` is), which the #757 construction guard and the verifier's
  `nat_bind` leg both treated as a narrowing target.

Older readers of the same kind are here too: an operation's width (`(0 - 4)
+ 1` refused as a u64 add), a literal above `i64.MAX` reaching an `@Int`
unobligated, and a constructor pattern's widening guard, which read a third
source — codegen's own rendering of the scrutinee — and left a `tier3`
claim unbacked.

This file holds the instrument.  The composite-construction MATRIX runs every
position a literal-arithmetic value can reach a binding through — {tuple,
ADT constructor, `if`-produced, `match`-produced, block-produced,
`let`-destructure, nested} — against both expected numeric types, and says
what each must do: an `@Int` binding returns the value, an `@Nat` binding is
refused on the record and at run time, and the literal is classified exactly
as an `@Int` parameter holding its value.  The TYPE-SOURCE DIFFERENTIAL then
replaces the checker's answer with the classifier's at every node where they
disagree and re-runs the verifier and code generation: a guard, an
obligation or a byte of the module that moves is a decision that read the
checker's table where it is wrong.  The READER ROSTER pins where either of
the checker's tables is read at all, so a new guard reading one turns this
file red.
"""

from __future__ import annotations

import tempfile
from dataclasses import dataclass, fields
from pathlib import Path

import pytest

from vera import ast, narrowing
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.environment import TypeEnv
from vera.types import INT, NAT, AdtType, RefinedType, Type, TypeVar
from vera.verifier import verify

_U64_MAX = 18446744073709551615

#: What a tripped `@Int` -> `@Nat` narrowing guard reports (#754).
_NAT_GUARD = "Negative value bound into a @Nat slot"
#: What a tripped `@Nat` -> `@Int` widening guard reports (#1438).
_WIDEN_GUARD = "@Nat value above i64.MAX widened into an @Int slot"


# =====================================================================
# The pipeline, as `vera verify` and `vera run` drive it
# =====================================================================

@dataclass(frozen=True)
class Observed:
    """What one program does under both halves."""

    errors: tuple[str, ...]
    """Error codes `vera verify` reports."""

    obligations: tuple[tuple[str, str, int, int], ...]
    """``(kind, status, line, column)`` for every obligation, sorted."""

    run: str
    """``"ran:<value>"`` when the function returns, else the trap text."""

    checks: tuple[tuple[str, int, int], ...]
    """``(emitter, line, column)`` for every check the module carries."""


def _artifacts(source: str, path: str) -> tuple[object, object]:
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source, file=path)
    errors = [d for d in diags if d.severity == "error"]
    assert not errors, (
        "fixture must type-check: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )
    return program, arts


def _observe(
    source: str,
    fn: str,
    args: list[object],
    *,
    semantic_types: dict | None = None,
) -> Observed:
    """Check, verify, compile and run *source* through the checker's tables.

    *semantic_types* replaces the checker's semantic table for BOTH the
    verifier and code generation — the type-source differential's lever.
    The target table is always the checker's own.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as handle:
        handle.write(source)
        path = handle.name
    try:
        program, arts = _artifacts(source, path)
        sem = (arts.expr_semantic_types if semantic_types is None
               else semantic_types)
        result = verify(
            program, source, file=path,
            expr_types=sem,
            expr_target_types=arts.expr_target_types,
        )
        compiled = codegen_compile(
            program, source=source, file=path,
            expr_semantic_types=sem,
            expr_target_types=arts.expr_target_types,
        )
    finally:
        Path(path).unlink(missing_ok=True)
    cg_errors = [d for d in compiled.diagnostics if d.severity == "error"]
    assert not cg_errors, (
        f"fixture must compile: {[d.description[:80] for d in cg_errors]}"
    )
    try:
        run = f"ran:{execute(compiled, fn_name=fn, args=args).value}"
    except Exception as exc:  # noqa: BLE001 — the trap IS the observation
        run = str(exc)
    return Observed(
        errors=tuple(sorted(
            d.error_code for d in result.diagnostics
            if d.severity == "error"
        )),
        obligations=tuple(sorted(
            (o.kind, o.status, o.line, o.column)
            for o in result.obligations
        )),
        run=run,
        checks=tuple(sorted(
            (c.emitter, c.line, c.column) for c in compiled.emitted_checks
        )),
    )


# =====================================================================
# The composite-construction matrix
# =====================================================================

_PRELUDE = (
    "private data Wrap<A> { W(A) }\n\n"
    "private data P<A, B> { MkP(B, A) }\n\n"
    "private data Box<T> { MkBox(Int, T) }\n\n"
)

#: position -> the function body, over ``{V}`` (the value) and ``{T}`` (the
#: numeric type the value is bound at).  The function is
#: ``f(@Int, @Nat, @Bool -> @{T})``: ``@Int.0`` and ``@Nat.0`` supply a
#: genuine value of each type, and ``@Bool.0`` picks a branch.
_POSITIONS: dict[str, str] = {
    "tuple destructure":
        "let Tuple<@Int, @{T}> = Tuple(1, {V});\n  @{T}.0",
    "tuple destructure, if-produced":
        "let Tuple<@Int, @{T}> = if @Bool.0 then {{ Tuple(1, {V}) }} "
        "else {{ Tuple(2, {V}) }};\n  @{T}.0",
    "tuple destructure, match-produced":
        "let Tuple<@Int, @{T}> = match @Bool.0 {{ true -> Tuple(1, {V}), "
        "false -> Tuple(2, {V}) }};\n  @{T}.0",
    "tuple destructure, block-produced":
        "let Tuple<@Int, @{T}> = {{ Tuple(1, {V}) }};\n  @{T}.0",
    "tuple match":
        "match Tuple(1, {V}) {{ Tuple(@Int, @{T}) -> @{T}.0 }}",
    "tuple match, if-produced":
        "match if @Bool.0 then {{ Tuple(1, {V}) }} else {{ Tuple(2, {V}) }} "
        "{{ Tuple(@Int, @{T}) -> @{T}.0 }}",
    "ADT destructure":
        "let Wrap<@{T}> = W({V});\n  @{T}.0",
    "ADT destructure, if-produced":
        "let Wrap<@{T}> = if @Bool.0 then {{ W({V}) }} "
        "else {{ W({V}) }};\n  @{T}.0",
    "ADT match":
        "match W({V}) {{ W(@{T}) -> @{T}.0 }}",
    "ADT match, match-produced":
        "match {{ match @Bool.0 {{ true -> W({V}), false -> W({V}) }} }} "
        "{{ W(@{T}) -> @{T}.0 }}",
    "Option match":
        "match Some({V}) {{ Some(@{T}) -> @{T}.0, None -> 7 }}",
    "nested, tuple in ADT":
        "match W(Tuple(1, {V})) {{ W(@Tuple<Int, {T}>) -> "
        "match @Tuple<Int, {T}>.0 {{ Tuple(@Int, @{T}) -> @{T}.0 }} }}",
    "nested, ADT in array":
        "let @Array<Wrap<{T}>> = [W({V})];\n  "
        "match @Array<Wrap<{T}>>.0[0] {{ W(@{T}) -> @{T}.0 }}",
    "nested, array in ADT":
        "match W([{V}]) {{ W(@Array<{T}>) -> @Array<{T}>.0[0] }}",
}

#: How each form `vera.narrowing` reads as a JOIN builds a value from two
#: alternatives ``{X}`` / ``{Y}`` — keyed by the forms themselves, so the
#: matrix's source axis is the code's own list of value-flow forms
#: (`RESULT_IS_NAT_READING`'s ``"flow"``), and a new one without a template
#: fails `TestTheSourceAxisIsTheCodes`.  `@Bool.0` is true in every run, so
#: each form yields ``{X}``.
_FLOW_TEMPLATES: dict[type, tuple[str, str]] = {
    ast.Block: ("block", "{{ {X} }}"),
    ast.IfExpr: ("if", "if @Bool.0 then {{ {X} }} else {{ {Y} }}"),
    ast.MatchExpr: ("match",
                    "match @Bool.0 {{ true -> {X}, false -> {Y} }}"),
    ast.HandleExpr: ("handle",
                     "handle[Exn<Int>] {{ throw(@Int) -> {Y} }} in {{ {X} }}"),
}

#: shape -> (the body over ``{S}``, the source; ``{X}``; ``{Y}``).
_FLOW_SHAPES: dict[str, tuple[str, str, str]] = {
    "tuple destructure": ("let Tuple<@Int, @{T}> = {S};\n  @{T}.0",
                          "Tuple(1, {V})", "Tuple(2, {V})"),
    "ADT destructure": ("let Wrap<@{T}> = {S};\n  @{T}.0",
                        "W({V})", "W({V})"),
    "tuple match": ("match {S} {{ Tuple(@Int, @{T}) -> @{T}.0 }}",
                    "Tuple(1, {V})", "Tuple(2, {V})"),
    "ADT match": ("match {S} {{ W(@{T}) -> @{T}.0 }}", "W({V})", "W({V})"),
}


def _flow_position(shape: str, form: type) -> tuple[str, str]:
    label, template = _FLOW_TEMPLATES[form]
    body, x, y = _FLOW_SHAPES[shape]
    source = template.replace("{X}", x).replace("{Y}", y)
    return f"{shape}, {label}-produced", body.replace("{S}", source)


for _shape in _FLOW_SHAPES:
    for _form in _FLOW_TEMPLATES:
        _name, _body = _flow_position(_shape, _form)
        _POSITIONS.setdefault(_name, _body)

_POSITIONS.update({
    # A nested constructor PATTERN reads the argument inside the argument.
    "tuple pattern in ADT pattern":
        "match W(Tuple(1, {V})) {{ W(Tuple(@Int, @{T})) -> @{T}.0 }}",
    "Option pattern in Option pattern":
        "match Some(Some({V})) {{ Some(Some(@{T})) -> @{T}.0, "
        "Some(None) -> 7, None -> 7 }}",
    # ... and over a scrutinee the SMT layer projects rather than reads as
    # a constructor application, which takes the nested walk's term path.
    "tuple pattern in ADT pattern, block-produced":
        "match {{ W(Tuple(1, {V})) }} {{ W(Tuple(@Int, @{T})) -> @{T}.0 }}",
    "tuple pattern in ADT pattern, if-produced":
        "match if @Bool.0 then {{ W(Tuple(1, {V})) }} "
        "else {{ W(Tuple(2, {V})) }} {{ W(Tuple(@Int, @{T})) -> @{T}.0 }}",
    # A generic constructor's field i is not type argument i: `MkP(B, A)`.
    "generic field 0 of MkP(B, A)":
        "let P<@{T}, @Bool> = MkP({V}, true);\n  @{T}.0",
    "generic field 1 of MkP(B, A)":
        "let P<@Bool, @{T}> = MkP(true, {V});\n  @{T}.0",
    "generic field 0 of MkP(B, A), matched":
        "match MkP({V}, true) {{ MkP(@{T}, @Bool) -> @{T}.0 }}",
    "generic field after a concrete one, MkBox(Int, T)":
        "let Box<@Int, @{T}> = MkBox(1, {V});\n  @{T}.0",
})

#: The positions where the value reaches the binding through a composite
#: pattern bind or a container's element — the NESTED ones.  No reader
#: there obligates a component's sign, for a literal or a genuine value
#: alike (a pre-existing gap, not this issue's), so they take part in every
#: cell that compares a literal with a genuine value and in every run, and
#: not in the cells that assert `vera verify` itself refuses.
_NESTED = frozenset(p for p in _POSITIONS if p.startswith("nested"))
_DIRECT = sorted(set(_POSITIONS) - _NESTED)

#: Literal arithmetic whose value is -3 — `@Nat` to the checker, which
#: types each literal `Nat` and `Nat - Nat` as `Nat`.
_LITERAL_ARITHMETIC = ("0 - 3", "2 - 5 * 1")

#: The genuine twin: an `@Int` parameter carrying the same -3.
_GENUINE_INT = "@Int.0"
_ARGS_MINUS_3 = [-3, 5, 1]


def _program(position: str, value: str, target: str) -> str:
    body = _POSITIONS[position].format(V=value, T=target)
    return (
        _PRELUDE
        + f"public fn f(@Int, @Nat, @Bool -> @{target})\n"
        + "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  "
        + body + "\n}\n"
    )


_MATRIX = [(p, v) for p in _POSITIONS for v in _LITERAL_ARITHMETIC]
_MATRIX_IDS = [f"{p} / {v}" for p, v in _MATRIX]
_DIRECT_MATRIX = [(p, v) for p, v in _MATRIX if p not in _NESTED]
_DIRECT_IDS = [f"{p} / {v}" for p, v in _DIRECT_MATRIX]

#: The sign-boundary half of each side: the obligation kinds and the guard
#: emitters a value's sign decides.
_SIGN_KINDS = frozenset({"nat_bind", "nat_to_int_coerce"})
_SIGN_EMITTERS = frozenset({
    "wasm/operators.py:_emit_nat_bind_guard",
    "wasm/operators.py:_emit_int_widen_guard",
})


def _sign_profile(observed: Observed) -> tuple:
    """What a value's sign decided in *observed*: which sign obligations
    exist (not their status — a literal is decidable where a parameter is
    not) and which sign guards were emitted, each as a sorted multiset."""
    return (
        tuple(sorted(o[0] for o in observed.obligations
                     if o[0] in _SIGN_KINDS)),
        tuple(sorted(c[0] for c in observed.checks
                     if c[0] in _SIGN_EMITTERS)),
    )


class TestALiteralIsClassifiedAsAnIntOfItsValue:
    """The type-source principle, position by position.

    `0 - 3` is an `@Int` whose value is -3 (spec §4.2, §4.4, §11.2.1), so
    every guard and every obligation must treat it exactly as they treat an
    `@Int` parameter holding -3: the same sign obligations at the same
    kinds, the same sign guards.  On the release branch the two parted
    wherever a decision read the checker's `@Nat` — a widening claimed and
    guarded for the literal only, a narrowing obligated at the construction
    for the literal only.  Statuses are not compared: a literal is decided
    at compile time where a parameter is not.
    """

    @pytest.mark.parametrize("target", ["Int", "Nat"])
    @pytest.mark.parametrize(("position", "value"), _MATRIX, ids=_MATRIX_IDS)
    def test_the_same_obligations_and_guards(
        self, position: str, value: str, target: str,
    ) -> None:
        literal = _observe(_program(position, value, target), "f",
                           _ARGS_MINUS_3)
        genuine = _observe(_program(position, _GENUINE_INT, target), "f",
                           _ARGS_MINUS_3)
        assert _sign_profile(literal) == _sign_profile(genuine), (
            f"`{value}` is classified differently from an `@Int` holding "
            f"its value — literal {_sign_profile(literal)}, "
            f"genuine {_sign_profile(genuine)}"
        )


class TestNegativeLiteralArithmeticRunsIntoAnIntBinding:
    """An `@Int` binding of a literal-arithmetic -3 returns -3.

    At `main` 6dc41d40 every cell here returned -3.  On the release branch
    the tuple destructures trapped on the widening guard, the ADT and
    `Option` positions failed `vera verify` with E503 and trapped on the
    narrowing guard, and the `if`-, `match`- and block-produced tuples
    trapped while `vera verify` PROVED the widening at Tier 1.  No `@Nat`
    value is involved anywhere: the only `@Nat` is the checker's type for
    `0 - 3`.
    """

    @pytest.mark.parametrize(("position", "value"), _MATRIX, ids=_MATRIX_IDS)
    def test_the_value_comes_back(self, position: str, value: str) -> None:
        observed = _observe(_program(position, value, "Int"), "f",
                            _ARGS_MINUS_3)
        assert observed.errors == (), (
            f"`vera verify` refuses a valid program: {observed.errors}"
        )
        assert observed.run == "ran:-3", (
            f"a literal-arithmetic -3 bound at `@Int` did not come back: "
            f"{observed.run}"
        )

    @pytest.mark.parametrize(("position", "value"), _MATRIX, ids=_MATRIX_IDS)
    def test_no_widening_is_claimed_for_it(
        self, position: str, value: str,
    ) -> None:
        """No `nat_to_int_coerce` obligation for a value that is no `@Nat`.

        The obligation claims a `@Nat` reaches an `@Int` slot.  Recorded for
        -3 it is proved vacuously at Tier 1 (`-3 <= i64.MAX`) while the
        guard it describes traps — how the release branch reported a
        verified program that aborts.
        """
        observed = _observe(_program(position, value, "Int"), "f",
                            _ARGS_MINUS_3)
        widenings = [o for o in observed.obligations
                     if o[0] == "nat_to_int_coerce"]
        assert widenings == [], widenings


class TestNegativeLiteralArithmeticIsRefusedByANatBinding:
    """The same -3 bound at `@Nat` is refused.

    Taking the checker's `@Nat` away from a decision must not take the
    narrowing away with it: the run trips the narrowing guard at every
    position, and wherever a reader obligates the bind at all, `vera
    verify` reports it VIOLATED.
    """

    @pytest.mark.parametrize(("position", "value"), _MATRIX, ids=_MATRIX_IDS)
    def test_the_run_is_refused(self, position: str, value: str) -> None:
        observed = _observe(_program(position, value, "Nat"), "f",
                            _ARGS_MINUS_3)
        assert _NAT_GUARD in observed.run, (
            f"`vera run` bound -3 at `@Nat`: {observed.run}"
        )

    @pytest.mark.parametrize(("position", "value"), _DIRECT_MATRIX,
                             ids=_DIRECT_IDS)
    def test_the_narrowing_is_on_the_record(
        self, position: str, value: str,
    ) -> None:
        """A `nat_bind` record, and never a proof.

        `violated` where the SMT layer can form the component, `tier3`
        (runtime-guarded, which the run above shows it is) where it cannot
        — a destructure of a user constructor whose name is not its type's,
        or a scrutinee the layer does not translate.  Either is a refusal
        on the record; `verified` would be a proof of a false claim, and
        `tier3_unguarded` a disclosure of a guard that is in fact emitted.
        """
        observed = _observe(_program(position, value, "Nat"), "f",
                            _ARGS_MINUS_3)
        binds = [o[1] for o in observed.obligations if o[0] == "nat_bind"]
        assert binds, (
            f"-3 bound at `@Nat` with nothing on the record: "
            f"{observed.obligations}"
        )
        assert set(binds) <= {"violated", "tier3"}, binds


class TestAGenuineNatStillWidensThroughTheGuard:
    """The #1416 control: the guard the fix narrows still fires where it must.

    `@Nat.0` above `i64.MAX` read out at `@Int` is a real widening, and
    u64.MAX is the only input that tells a guard that fires from one that
    is absent.  At the `match` positions this is also a fix: codegen read the
    scrutinee's type from its own rendering of the constructor application,
    which carries no component types, so u64.MAX came back as -1 while the
    verifier recorded the guard it expected (`tier3`).
    """

    @pytest.mark.parametrize("position", _DIRECT)
    def test_u64_max_traps_and_an_in_range_value_passes(
        self, position: str,
    ) -> None:
        source = _program(position, "@Nat.0", "Int")
        high = _observe(source, "f", [0, _U64_MAX, 1])
        assert _WIDEN_GUARD in high.run, (
            f"u64.MAX widened into `@Int` unguarded: {high.run}"
        )
        low = _observe(source, "f", [0, 42, 1])
        assert low.run == "ran:42", low.run


_SLOT_SOURCE = """public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Int, Nat> = Tuple(1, @Nat.0);
  let Tuple<@Int, @Int> = @Tuple<Int, Nat>.0;
  @Int.0
}
"""

_CALL_SOURCE = """private fn pair(@Nat -> @Tuple<Int, Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(1, @Nat.0)
}

public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let Tuple<@Int, @Int> = pair(@Nat.0);
  @Int.0
}
"""

_SLOT_SCRUTINEE = """public fn f(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Int, Nat> = Tuple(1, @Nat.0);
  match @Tuple<Int, Nat>.0 {
    Tuple(@Int, @Int) -> @Int.0
  }
}
"""


class TestAnOpaqueSourceAnswersFromItsDeclaration:
    """Where the source shows no construction — a slot, a call — the
    component classifier asks the declaration, and a `@Nat` component read
    out at `@Int` is guarded and obligated as #1416 made it.  The leaf is
    the one place the classifier consults the checker's table, and there
    the type is the declaration's, never a literal's.

    Both halves read the leaf the same way.  Code generation's reading of a
    `Tuple` scrutinee used to come from a constructor layout the built-in
    carrier does not have: `match @Tuple<Int, Nat>.0 { Tuple(@Int, @Int) ->
    … }` recorded a `tier3` widening, emitted no guard, and returned u64.MAX
    as -1 on `main` and on the release branch."""

    @pytest.mark.parametrize("source", [
        _SLOT_SOURCE, _CALL_SOURCE, _SLOT_SCRUTINEE,
    ], ids=["destructure a slot", "destructure a call", "match a slot"])
    def test_the_claim_and_the_guard_are_both_there(self, source: str) -> None:
        observed = _observe(source, "f", [42])
        assert ("nat_to_int_coerce", "tier3") in {
            (o[0], o[1]) for o in observed.obligations}, observed.obligations
        assert "wasm/operators.py:_emit_int_widen_guard" in {
            c[0] for c in observed.checks}, observed.checks
        assert observed.run == "ran:42", observed.run

    @pytest.mark.parametrize("source", [_SLOT_SOURCE, _SLOT_SCRUTINEE],
                             ids=["destructure a slot", "match a slot"])
    def test_u64_max_traps(self, source: str) -> None:
        """A call source cannot carry u64.MAX this far: the callee's own
        return-boundary component check refuses it first."""
        assert _WIDEN_GUARD in _observe(source, "f", [_U64_MAX]).run


class TestTheComponentReadsOfTheReview:
    """Four component readings PR #1537's review found, each a place where a
    decision still took a component's type from the wrong source."""

    def test_a_folded_literal_arm_does_not_hide_a_genuine_nat(self) -> None:
        """`2 + 3` is a non-negative literal-only value, as `5` is: an arm
        built from it is `@Nat`-compatible, or the join drops the guard its
        `@Nat.0` sibling needs and u64.MAX comes back as -1."""
        source = _program(
            "tuple destructure, if-produced", "@Nat.0", "Int").replace(
            "Tuple(2, @Nat.0)", "Tuple(2, 2 + 3)")
        assert "Tuple(2, 2 + 3)" in source
        assert _WIDEN_GUARD in _observe(source, "f", [0, _U64_MAX, 1]).run
        assert _observe(source, "f", [0, _U64_MAX, 0]).run == "ran:5"
        assert _observe(source, "f", [0, 42, 1]).run == "ran:42"

    @pytest.mark.parametrize("body", [
        "let Tuple<@PosInt, @Int> = if @Bool.0 then {{ Tuple(0 - 5, 1) }} "
        "else {{ Tuple(3, 1) }};\n  @PosInt.0",
        "match if @Bool.0 then {{ Tuple(0 - 5, 1) }} else {{ Tuple(3, 1) }} "
        "{{ Tuple(@PosInt, @Int) -> @PosInt.0 }}",
    ], ids=["destructure", "sub-pattern"])
    def test_a_refined_bind_is_not_proved_from_a_literal_s_type(
        self, body: str,
    ) -> None:
        """The refined legs took the component's SOURCE fact from the
        checker's type: `Tuple<Nat, Nat>`'s `>= 0` over `ite(b, -5, 3)` forced
        `b` false and PROVED the `@PosInt` bind the guard then refused.  Only
        an opaque source seeds its declaration's fact now."""
        source = ("type PosInt = { @Int | @Int.0 > 0 };\n\n"
                  + _shape_program(body.format()))
        observed = _observe(source, "f", [0, 0, 1])
        binds = [o[1] for o in observed.obligations if o[0] == "refine_bind"]
        assert binds and "verified" not in binds, observed.obligations
        assert "Refinement violation" in observed.run, observed.run

    _BOX = """private data Box<T> { MkBox(Int, T) }

private fn mk(@Int, @Nat -> @Box<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  MkBox(@Int.0, @Nat.0)
}

public fn f(@Int, @Nat -> @T0)
  requires(true)
  ensures(true)
  effects(pure)
{
  BODY
}
"""

    def _box(self, target: str, body: str) -> str:
        return self._BOX.replace("@T0", f"@{target}").replace("BODY", body)

    def test_a_field_is_read_as_its_constructor_declares_it(self) -> None:
        """Binding i is field i, whose type is the constructor's — `Int`,
        then `T` — and not type argument i.  Read by index, the `Int` field
        was guarded as a `@Nat` and a valid -5 trapped as "above i64.MAX"."""
        source = self._box("Int", "let Box<@Int, @Int> = mk(@Int.0, @Nat.0);"
                                  "\n  @Int.1")
        assert _observe(source, "f", [-5, 7]).run == "ran:-5"
        high = _observe(source, "f", [3, _U64_MAX])
        assert _WIDEN_GUARD in high.run, high.run

    def test_a_type_name_is_not_read_as_another_type_s_constructor(
        self,
    ) -> None:
        """`let Box<…>` names the TYPE of its source.  A constructor `Box`
        of another type does not describe that source: read by the name,
        both fields took `Other.Box`'s `Nat` flags and a valid -5 trapped."""
        source = "private data Other { Box(Nat, Nat) }\n\n" + self._box(
            "Int", "let Box<@Int, @Int> = mk(@Int.0, @Nat.0);\n  @Int.1")
        observed = _observe(source, "f", [-5, 7])
        assert observed.run == "ran:-5", observed.run
        widenings = [o for o in observed.obligations
                     if o[0] == "nat_to_int_coerce"]
        assert len(widenings) == 1, observed.obligations
        high = _observe(source, "f", [3, _U64_MAX])
        assert _WIDEN_GUARD in high.run, high.run

    def test_the_int_field_narrowed_into_nat_is_on_the_record(self) -> None:
        source = self._box("Nat", "let Box<@Nat, @Nat> = mk(@Int.0, @Nat.0);"
                                  "\n  @Nat.1")
        observed = _observe(source, "f", [-5, 7])
        assert ("nat_bind", "tier3") in {
            (o[0], o[1]) for o in observed.obligations}, observed.obligations
        assert _NAT_GUARD in observed.run, observed.run

    def test_the_int_field_seeds_no_nat_fact(self) -> None:
        """The destructure seeds each bound component with its source's
        type; seeded with type argument 0 (`Nat`), the `Int` field's
        `>= 0` PROVED a later `let @Nat = @Int.0` that the guard refuses."""
        source = self._box(
            "Nat", "let Box<@Int, @Nat> = mk(@Int.0, @Nat.0);\n"
                   "  let @Nat = @Int.0;\n  @Nat.0")
        observed = _observe(source, "f", [-5, 7])
        binds = [(o[1], o[2]) for o in observed.obligations
                 if o[0] == "nat_bind"]
        assert binds and all(status != "verified" for status, _ in binds), (
            observed.obligations)
        assert _NAT_GUARD in observed.run, observed.run


class TestTheSourceAxisIsTheCodes:
    """The matrix's axes come from the code, not from a list kept beside it
    (PR #1537 review): a form the classifier reads that the matrix does not
    exercise fails here."""

    def test_every_expression_form_has_a_reading(self) -> None:
        forms = {cls for cls in vars(ast).values()
                 if isinstance(cls, type) and issubclass(cls, ast.Expr)
                 and cls is not ast.Expr}
        assert set(narrowing.RESULT_IS_NAT_READING) == forms, (
            sorted(c.__name__ for c in
                   forms ^ set(narrowing.RESULT_IS_NAT_READING)))

    def test_every_flow_form_builds_a_source(self) -> None:
        flows = {form for form, reading
                 in narrowing.RESULT_IS_NAT_READING.items()
                 if reading == "flow"}
        assert set(_FLOW_TEMPLATES) == flows
        for shape in _FLOW_SHAPES:
            for form in flows:
                name, _body = _flow_position(shape, form)
                assert name in _POSITIONS, name


#: A genuine `@Nat` in every form the classifier answers from a declaration
#: or reads through: name -> (the value, a statement put before the body,
#: a wrapper around it).  `@Nat.0` is u64.MAX in the trapping runs.
_GENUINE_NAT_SOURCES: dict[str, tuple[str, str, str]] = {
    "slot": ("@Nat.0", "", "{BODY}"),
    "index": ("@Array<Nat>.0[0]", "let @Array<Nat> = [@Nat.0];\n  ",
              "{BODY}"),
    "call": ("nat_id(@Nat.0)", "", "{BODY}"),
    "effect operation": (
        "State.get(())", "",
        "handle[State<Nat>](@Nat = @Nat.0) {\n"
        "    get(@Unit) -> { resume(@Nat.0) },\n"
        "    put(@Nat) -> { resume(()) }\n"
        "  } in {\n  {BODY}\n  }"),
    "join with a folded literal": (
        "if @Bool.0 then { @Nat.0 } else { 2 + 3 }", "", "{BODY}"),
    "handle": ("handle[Exn<Int>] { throw(@Int) -> 5 } in { @Nat.0 }",
               "", "{BODY}"),
}

_NAT_ID = """private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

"""


def _genuine_program(position: str, source: str) -> str:
    value, before, wrapper = _GENUINE_NAT_SOURCES[source]
    body = before + _POSITIONS[position].format(
        V=value.replace("{", "{{").replace("}", "}}"), T="Int")
    body = body.replace("{{", "{").replace("}}", "}")
    return (
        _PRELUDE + _NAT_ID
        + "public fn f(@Int, @Nat, @Bool -> @Int)\n"
        + "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  "
        + wrapper.replace("{BODY}", body) + "\n}\n"
    )


_GENUINE_CELLS = [(p, g) for p in _DIRECT for g in _GENUINE_NAT_SOURCES]


class TestEveryGenuineNatFormWidensThroughTheGuard:
    """A genuine `@Nat` read into an `@Int` is claimed and guarded whatever
    form supplies it — a slot, an index, a call, an effect operation, a join
    with a folded literal, a `handle` — at every direct position (PR #1537
    review).  The classifier answers each from its declaration or reads
    through it; answering "not a `@Nat`" for any of them dropped the guard
    the release branch emitted, and u64.MAX came back as -1."""

    @pytest.mark.parametrize(("position", "source"), _GENUINE_CELLS,
                             ids=[f"{p} / {g}" for p, g in _GENUINE_CELLS])
    def test_claimed_guarded_and_42_comes_back(
        self, position: str, source: str,
    ) -> None:
        """Claimed and guarded at the binding, and never a false refusal
        of an in-range value.  At u64.MAX the run is refused — by the
        widening guard, or first by a generic constructor's narrowing guard
        on the way in, whose signed compare reads a `@Nat` above
        `i64.MAX` as negative (#1504); neither returns -1."""
        program = _genuine_program(position, source)
        high = _observe(program, "f", [0, _U64_MAX, 1])
        assert _WIDEN_GUARD in high.run or _NAT_GUARD in high.run, (
            f"u64.MAX came back from an `@Int` binding: {high.run}")
        assert "nat_to_int_coerce" in {o[0] for o in high.obligations}, (
            high.obligations)
        assert "wasm/operators.py:_emit_int_widen_guard" in {
            c[0] for c in high.checks}, high.checks
        assert _observe(program, "f", [0, 42, 1]).run == "ran:42"

    @pytest.mark.parametrize("position", [
        p for p in _DIRECT
        if p.startswith(("tuple destructure", "tuple match"))])
    @pytest.mark.parametrize("source", list(_GENUINE_NAT_SOURCES))
    def test_at_a_tuple_the_widening_guard_is_what_refuses(
        self, position: str, source: str,
    ) -> None:
        """A `Tuple` is built with no narrowing guard of its own, so there
        the refusal of u64.MAX is the widening guard's."""
        high = _observe(_genuine_program(position, source), "f",
                        [0, _U64_MAX, 1])
        assert _WIDEN_GUARD in high.run, high.run


def _nat_results() -> list[tuple[str, tuple[str, ...]]]:
    """Every built-in function whose declared result is a `@Nat`, with its
    parameter types' names — read from the checker's own registry."""
    out = []
    for name, info in sorted(TypeEnv().functions.items()):
        ret = info.return_type
        ret = ret.base if isinstance(ret, RefinedType) else ret
        if getattr(ret, "name", None) == "Nat":
            out.append((name, tuple(getattr(p, "name", "?")
                                    for p in info.param_types)))
    return out


def _nat_ops() -> list[tuple[str, str]]:
    """Every effect operation whose result is a `@Nat`, or its effect's type
    parameter (a `@Nat` when the effect is instantiated at one)."""
    out = []
    for effect, info in sorted(TypeEnv().effects.items()):
        for op_name, op in sorted(info.operations.items()):
            ret = op.return_type
            if isinstance(ret, TypeVar) or getattr(ret, "name", None) == "Nat":
                out.append((effect, op_name))
    return out


_ARGUMENT_FOR = {"String": '"ab"', "Int": "1", "Nat": "1", "Unit": "()"}

#: How a program reaches each effect operation with a `@Nat` result.
_OP_PROGRAMS: dict[tuple[str, str], tuple[str, str]] = {
    ("IO", "time"): ("effects(<IO>)", "let @Int = IO.time(());\n  @Int.0"),
    ("State", "get"): (
        "effects(pure)",
        "handle[State<Nat>](@Nat = 1) {\n"
        "    get(@Unit) -> { resume(@Nat.0) },\n"
        "    put(@Nat) -> { resume(()) }\n"
        "  } in {\n    let @Int = State.get(());\n    @Int.0\n  }"),
}


class TestEveryNatResultIsDeclared:
    """Every built-in function and effect operation whose result is a `@Nat`
    is a widening where an `@Int` binds it: claimed, and guarded.  The list
    is the checker's registry, so a new one is covered the day it lands."""

    def _assert_widens(self, body: str, effects: str = "effects(pure)"):
        program = ("public fn f(@Int -> @Int)\n  requires(true)\n"
                   f"  ensures(true)\n  {effects}\n{{\n  {body}\n}}\n")
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".vera", delete=False, encoding="utf-8",
        ) as handle:
            handle.write(program)
            path = handle.name
        try:
            parsed, arts = _artifacts(program, path)
            result = verify(parsed, program, file=path,
                            expr_types=arts.expr_semantic_types,
                            expr_target_types=arts.expr_target_types)
            compiled = codegen_compile(
                parsed, source=program, file=path,
                expr_semantic_types=arts.expr_semantic_types,
                expr_target_types=arts.expr_target_types)
        finally:
            Path(path).unlink(missing_ok=True)
        assert "nat_to_int_coerce" in {o.kind for o in result.obligations}, (
            body)
        assert "wasm/operators.py:_emit_int_widen_guard" in {
            c.emitter for c in compiled.emitted_checks}, body

    @pytest.mark.parametrize(("name", "params"), _nat_results(),
                             ids=[n for n, _ in _nat_results()])
    def test_a_builtin(self, name: str, params: tuple[str, ...]) -> None:
        missing = [p for p in params if p not in _ARGUMENT_FOR]
        assert not missing, f"no argument written for {name}'s {missing}"
        args = ", ".join(_ARGUMENT_FOR[p] for p in params)
        self._assert_widens(f"let @Int = {name}({args});\n  @Int.0")

    @pytest.mark.parametrize(("effect", "op"), _nat_ops(),
                             ids=[f"{e}.{o}" for e, o in _nat_ops()])
    def test_an_effect_operation(self, effect: str, op: str) -> None:
        assert (effect, op) in _OP_PROGRAMS, (
            f"no program written reaching {effect}.{op}")
        effects, body = _OP_PROGRAMS[(effect, op)]
        self._assert_widens(body, effects)


class TestAScalarReadsEveryNatForm:
    """#1538: at a scalar `let` and a return, an index into an `Array<Nat>`
    and `State.get` at `State<Nat>` are widenings too.  On `main`, the
    release branch and 16c25c9e alike neither was obligated or guarded:
    u64.MAX read as -1, and an `ensures(@Int.result >= 0)` proved at Tier 1
    failed at run time."""

    _INDEX = ("let @Array<Nat> = [@Nat.0];\n  let @Int = @Array<Nat>.0[0];"
              "\n  @Int.0")
    _RETURN = "let @Array<Nat> = [@Nat.0];\n  @Array<Nat>.0[0]"
    _STATE = ("handle[State<Nat>](@Nat = @Nat.0) {\n"
              "    get(@Unit) -> { resume(@Nat.0) },\n"
              "    put(@Nat) -> { resume(()) }\n"
              "  } in {\n    let @Int = State.get(());\n    @Int.0\n  }")

    _ALIAS = "let @Int = @Count.0;\n  @Int.0"
    _ALIAS_COMPONENT = ("let Tuple<@Int, @Int> = Tuple(1, @Count.0);\n"
                        "  @Int.0")

    @pytest.mark.parametrize("ensures", ["true", "@Int.result >= 0"])
    @pytest.mark.parametrize("body", [
        _INDEX, _RETURN, _STATE, _ALIAS, _ALIAS_COMPONENT,
    ], ids=["let an index", "return an index", "let State.get",
            "let a Nat alias's slot", "a Nat alias's slot as a component"])
    def test_u64_max_traps_on_the_widening(
        self, body: str, ensures: str,
    ) -> None:
        """An alias of `Nat` is a `@Nat` too: its slot's name is not
        `Nat`, and read by name it returned u64.MAX as -1 unobligated."""
        param = "@Count" if "@Count" in body else "@Nat"
        program = ("type Count = Nat;\n\n"
                   f"public fn f({param} -> @Int)\n  requires(true)\n"
                   f"  ensures({ensures})\n  effects(pure)\n{{\n  {body}\n}}\n")
        high = _observe(program, "f", [_U64_MAX])
        assert _WIDEN_GUARD in high.run, high.run
        assert ("nat_to_int_coerce", "tier3") in {
            (o[0], o[1]) for o in high.obligations}, high.obligations
        assert _observe(program, "f", [42]).run == "ran:42"


_GET_NAT = """private fn get_nat(@Wrap<Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Wrap<Nat>.0 { W(@Nat) -> @Nat.0 }
}

"""


class TestACompositeBindingIsTheConstructionsContext:
    """A pattern that binds a constructor argument at a COMPOSITE type —
    `W(@Array<Nat>)`, a `@Wrap<Nat>` component — obligates none of its
    components, and the constructor door records no type it inferred from
    a literal subtraction; so the binding's type is the construction's
    context, and the construction is obligated against it (PR #1537
    review).  Without it `match W([0 - 3]) { W(@Array<Nat>) -> … }` put -3
    in a `Nat` array with nothing on the record."""

    @pytest.mark.parametrize(("body", "target"), [
        ("match W([0 - 3]) { W(@Array<Nat>) -> @Array<Nat>.0[0] }", "Nat"),
        ("let Tuple<@Wrap<Nat>, @Int> = Tuple(W(0 - 3), 1);\n"
         "  get_nat(@Wrap<Nat>.0)", "Nat"),
        ("match W(0 - 3) { @Wrap<Nat> -> get_nat(@Wrap<Nat>.0) }", "Nat"),
    ], ids=["array in a pattern", "a destructured component",
            "the whole scrutinee"])
    def test_at_nat_the_construction_is_refused(
        self, body: str, target: str,
    ) -> None:
        program = (_PRELUDE + _GET_NAT
                   + f"public fn f(@Int -> @{target})\n  requires(true)\n"
                   "  ensures(true)\n  effects(pure)\n{\n  "
                   + body + "\n}\n")
        observed = _observe(program, "f", [0])
        assert "E503" in observed.errors, observed.obligations
        assert _NAT_GUARD in observed.run, observed.run

    @pytest.mark.parametrize("body", [
        "match W([0 - 3]) { W(@Array<Int>) -> @Array<Int>.0[0] }",
        "let Tuple<@Wrap<Int>, @Int> = Tuple(W(0 - 3), 1);\n"
        "  match @Wrap<Int>.0 { W(@Int) -> @Int.0 }",
        "match W(0 - 3) { @Wrap<Int> -> match @Wrap<Int>.0 "
        "{ W(@Int) -> @Int.0 } }",
    ], ids=["array in a pattern", "a destructured component",
            "the whole scrutinee"])
    def test_at_int_it_comes_back(self, body: str) -> None:
        program = (_PRELUDE + "public fn f(@Int -> @Int)\n  requires(true)\n"
                   "  ensures(true)\n  effects(pure)\n{\n  " + body + "\n}\n")
        observed = _observe(program, "f", [0])
        assert observed.errors == (), observed.obligations
        assert observed.run == "ran:-3", observed.run


_REFINED_SHAPES: dict[str, str] = {
    "destructure": "let Tuple<@PosInt, @Int> = {S};\n  @PosInt.0",
    "match": "match {S} {{ Tuple(@PosInt, @Int) -> @PosInt.0 }}",
}


class TestARefinedComponentAssumesOnlyADeclaration:
    """A refined binding of a component assumes its source's type only
    where every source is opaque, through every form a value flows by
    (PR #1537 review): the checker's `Tuple<Nat, Nat>` for a value built
    from `0 - 5` forced its own premise and proved a `@PosInt` bind at
    Tier 1 that the guard then refused."""


    @pytest.mark.parametrize("form", list(_FLOW_TEMPLATES),
                             ids=[_FLOW_TEMPLATES[f][0]
                                  for f in _FLOW_TEMPLATES])
    @pytest.mark.parametrize("shape", ["destructure", "match"])
    def test_not_proved_and_refused(self, shape: str, form: type) -> None:
        _label, template = _FLOW_TEMPLATES[form]
        source = (template.replace("{X}", "Tuple(0 - 5, 1)")
                  .replace("{Y}", "Tuple(3, 1)"))
        body = _REFINED_SHAPES[shape].replace("{S}", source).replace(
            "{{", "{").replace("}}", "}")
        program = ("type PosInt = { @Int | @Int.0 > 0 };\n\n"
                   + _shape_program(body))
        observed = _observe(program, "f", [0, 0, 1])
        binds = [o[1] for o in observed.obligations if o[0] == "refine_bind"]
        assert binds and "verified" not in binds, observed.obligations
        assert "Refinement violation" in observed.run, observed.run


def _verify_only(source: str) -> tuple[tuple[str, str], ...]:
    """``(kind, status)`` of every obligation `vera verify` records for
    *source* — for shapes code generation does not compile."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as handle:
        handle.write(source)
        path = handle.name
    try:
        program, arts = _artifacts(source, path)
        result = verify(program, source, file=path,
                        expr_types=arts.expr_semantic_types,
                        expr_target_types=arts.expr_target_types)
    finally:
        Path(path).unlink(missing_ok=True)
    return tuple(sorted((o.kind, o.status) for o in result.obligations))


class TestAnIndexReadsTheArrayItIndexes:
    """An index into an array built here is one of its elements: read by
    value where the elements are literal-only, by declaration where they
    are genuine — not by the checker's element type for the literal, which
    calls `[0 - 3]` an `Array<Nat>`."""

    @pytest.mark.parametrize("body", [
        "let @Int = [0 - 3][0];\n  @Int.0",
        "let Tuple<@Int, @Int> = [Tuple(1, 0 - 3)][0];\n  @Int.0",
        "match [W(0 - 3)][0] { W(@Int) -> @Int.0 }",
    ], ids=["scalar", "tuple component", "ADT field"])
    def test_a_literal_element_claims_no_widening(self, body: str) -> None:
        kinds = {k for k, _s in _verify_only(_PRELUDE + _shape_program(body))}
        assert "nat_to_int_coerce" not in kinds, kinds

    def test_a_genuine_element_is_claimed(self) -> None:
        kinds = {k for k, _s in _verify_only(_shape_program(
            "let @Int = [@Nat.0, 5][@Nat.0 % 2];\n  @Int.0"))}
        assert "nat_to_int_coerce" in kinds, kinds


_NESTED_OPAQUE = """private data Wrap<A> { W(A) }

public fn f(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Wrap<Tuple<Int, Nat>> = W(Tuple(@Int.0, @Nat.0));
  match @Wrap<Tuple<Int, Nat>>.0 { W(Tuple(@Int, @Int)) -> @Int.ARG }
}
"""


class TestANestedPatternReadsItsPath:
    """A nested pattern over an opaque scrutinee reads each component's
    declaration down the pattern's path — `Wrap<Tuple<Int, Nat>>`, then
    `W`'s field, then the tuple's component — on both sides, so the
    `@Nat` component is claimed and guarded and the `@Int` one is not."""

    def test_the_nat_component_is_claimed_and_guarded(self) -> None:
        source = _NESTED_OPAQUE.replace("ARG", "0")
        high = _observe(source, "f", [-5, _U64_MAX])
        assert _WIDEN_GUARD in high.run, high.run
        assert ("nat_to_int_coerce", "tier3") in {
            (o[0], o[1]) for o in high.obligations}, high.obligations
        assert _observe(source, "f", [-5, 42]).run == "ran:42"

    def test_the_int_component_is_neither(self) -> None:
        source = _NESTED_OPAQUE.replace("ARG", "1")
        low = _observe(source, "f", [-5, 42])
        assert low.run == "ran:-5", low.run
        widenings = [o for o in low.obligations
                     if o[0] == "nat_to_int_coerce"]
        assert len(widenings) == 1, low.obligations


class TestANatSubtractionIsGuardedWhereItIsObligated:
    """The `@Nat` subtraction's underflow guard reads the verifier's
    classification of its operands: an index into an `Array<Nat>` and a
    call returning `@Nat` are `@Nat` operands with `@Nat` provenance (PR
    #1537 review).  Code generation read neither — its static rule has no
    index arm and its call walker answers `Int` for an i64 return — so the
    verifier's `nat_sub` had no guard behind it: `nat_id(@Nat.1) - @Nat.0`
    returned -3 from a `@Nat` function on `main`, the release branch and
    16c25c9e, and the index form did once the widening rule read an
    index's declaration."""

    _PROGRAM = """private fn nat_id(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Nat.0
}

public fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  BODY
}
"""

    @pytest.mark.parametrize("body", [
        "let @Array<Nat> = [@Nat.1];\n  @Array<Nat>.0[0] - @Nat.0",
        "nat_id(@Nat.1) - @Nat.0",
        "let @Array<Nat> = [@Nat.1];\n  @Array<Nat>.0[0] - 5",
        "nat_id(@Nat.1) - 5",
    ], ids=["an index", "a call", "an index less a literal",
            "a call less a literal"])
    def test_the_underflow_is_refused_where_it_happens(self, body: str) -> None:
        """The last two keep a slot out of the subtraction's operands, so
        its `@Nat` provenance can come only from the index or the call."""
        source = self._PROGRAM.replace("BODY", body)
        low = _observe(source, "f", [2, 5])
        assert "would be negative" in low.run, low.run
        assert "nat_sub" in {o[0] for o in low.obligations}, low.obligations
        assert "wasm/operators.py:_emit_nat_sub_guard" in {
            c[0] for c in low.checks}, low.checks
        assert _observe(source, "f", [8, 5]).run == "ran:3"


class TestALiteralAboveI64MaxIsANat:
    """`18446744073709551615` is a value only a `@Nat` holds.

    In an `@Int` context the checker range-checks a literal against `@Int`
    (E149), so the classifier calls a literal no `@Nat`.  A component with
    no expected type is range-checked as `@Nat` instead, and reaches the
    `@Int` binding unchecked; the release branch caught it only through the
    checker's `@Nat` — the very reading this fix removes — and recorded no
    obligation.  It is now a widening like any other: refused by `vera
    verify` (E530, provably out of range) and by the guard.
    """

    @pytest.mark.parametrize("position", _DIRECT)
    def test_both_halves_refuse(self, position: str) -> None:
        """A `nat_to_int_coerce` record that is not a proof — `violated`
        (E530) where the component is formed, `tier3` where the layer cannot
        form it — and the widening guard trips."""
        observed = _observe(_program(position, str(_U64_MAX), "Int"), "f",
                            [0, 0, 1])
        widen = [o[1] for o in observed.obligations
                 if o[0] == "nat_to_int_coerce"]
        assert widen and set(widen) <= {"violated", "tier3"}, (
            observed.obligations)
        assert _WIDEN_GUARD in observed.run, observed.run


# =====================================================================
# Decisions other than a bind
# =====================================================================

#: (label, body over `f(@Int, @Nat, @Bool -> @Int)`, arguments, value).  A
#: negative literal-only value as an OPERAND of another literal-only one:
#: the width the operation runs at is a sign decision too.  Read from the
#: checker's `@Nat`, `(0 - 4) + 1` was a u64 add whose -3 lies outside the
#: unsigned range (E528, refused) and `(0 - 3) * 2` the same, trapping at
#: run time as well.  Neither ran on `main` or on the release branch.
_OPERAND_CELLS = [
    ("under an addition", "let @Int = (0 - 4) + 1;\n  @Int.0", [0, 0, 1], -3),
    ("under a multiplication", "let @Int = (0 - 3) * 2;\n  @Int.0",
     [0, 0, 1], -6),
    ("under a subtraction", "let @Int = (0 - 3) - 1;\n  @Int.0", [0, 0, 1],
     -4),
    ("under a division", "let @Int = (0 - 7) / 2;\n  @Int.0", [0, 0, 1],
     -3),
]

#: Which obligation kinds a check at an operation serves.
_OPERATION_KINDS = frozenset({"int_overflow", "nat_sub"})


def _shape_program(body: str) -> str:
    return (
        "public fn f(@Int, @Nat, @Bool -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n  "
        + body + "\n}\n"
    )


class TestAnOperandHoldingANegativeLiteralIsAnInt:
    """The width and the `@Nat`-subtraction test read the sign rule too."""

    @pytest.mark.parametrize(("label", "body", "args", "value"),
                             _OPERAND_CELLS, ids=[c[0] for c in _OPERAND_CELLS])
    def test_it_runs_to_its_value(
        self, label: str, body: str, args: list[int], value: int,
    ) -> None:
        observed = _observe(_shape_program(body), "f", args)
        assert observed.errors == (), observed.obligations
        assert observed.run == f"ran:{value}", observed.run

    @pytest.mark.parametrize(("label", "body", "args", "value"),
                             _OPERAND_CELLS, ids=[c[0] for c in _OPERAND_CELLS])
    def test_the_claims_and_the_checks_agree(
        self, label: str, body: str, args: list[int], value: int,
    ) -> None:
        """At every operation, the obligation kinds the verifier records are
        the kinds the checks code generation emits there serve — so neither
        half can read the sign one way while the other reads it the other."""
        from vera.trap_registry import TRAP_EMITTERS

        observed = _observe(_shape_program(body), "f", args)
        claimed: dict[tuple[int, int], set[str]] = {}
        for kind, _status, line, col in observed.obligations:
            if kind in _OPERATION_KINDS:
                claimed.setdefault((line, col), set()).add(kind)
        served: dict[tuple[int, int], set[str]] = {}
        for emitter, line, col in observed.checks:
            kinds = set(TRAP_EMITTERS[emitter].obligations) & _OPERATION_KINDS
            if kinds:
                served.setdefault((line, col), set()).update(kinds)
        assert claimed == served


class TestAnOperationWithAGenuineNatKeepsItsWidth:
    """Only an operation of two literal-only operands is classified by
    value.  One with a genuine `@Nat` operand keeps the checker's width,
    whatever its other operand folds to, because no machine width serves a
    `@Nat` that may exceed `i64.MAX` beside a negative value: signed, the
    `@Nat` is reinterpreted and a large one comes back wrong and silent.
    Kept unsigned, u64.MAX still refuses — the cells below pin that no
    classifier change moved such an operation onto the signed width.  The
    mixed-sign operation's own defect (it refuses values it should admit,
    `@Nat.0 + (0 - 1)` at 5, and `(0 - 3) - @Nat.0` is an E502) is an
    operand-widening question this classifier does not answer."""

    @pytest.mark.parametrize("body", [
        "@Nat.0 + (5 - 3)", "@Nat.0 + (0 - 1)", "(0 - 3) + @Nat.0",
    ])
    def test_u64_max_is_refused_not_reinterpreted(self, body: str) -> None:
        source = _shape_program(body).replace("-> @Int)", "-> @Nat)")
        assert "overflow" in _observe(source, "f", [0, _U64_MAX, 1]).run

    def test_a_non_negative_literal_part_changes_nothing(self) -> None:
        """`5 - 3` is 2: the fold, not the shape, decides."""
        source = _shape_program("@Nat.0 + (5 - 3)").replace(
            "-> @Int)", "-> @Nat)")
        assert _observe(source, "f", [0, 7, 1]).run == "ran:9"

    def test_a_literal_above_i64_max_beside_a_negative_one_too(self) -> None:
        """The mixed-sign case in literal form: `18446744073709551615` is a
        `@Nat`-only value, so `18446744073709551615 + (0 - 1)` keeps the
        unsigned width and refuses, where the signed one returned -2 with
        nothing on the record (PR #1537 review)."""
        source = _shape_program(f"{_U64_MAX} + (0 - 1)").replace(
            "-> @Int)", "-> @Nat)")
        assert "overflow" in _observe(source, "f", [0, 0, 1]).run


class TestTheFoldIsTheMachine:
    """`vera.narrowing.literal_range` folds over unbounded integers with the
    machine's own division — `i64.div_s` truncates toward zero, which
    Python's `//` does not — so a sign read off the fold is the sign the
    program computes."""

    @pytest.mark.parametrize("text", [
        "(0 - 7) / 2", "(0 - 7) % 2", "7 % (0 - 2)", "7 / (0 - 2)",
        "(0 - 3) * (0 - 4)", "2 - 5 * 1", "(0 - 4) + 1",
    ])
    def test_a_folded_value_is_the_run_value(self, text: str) -> None:
        from vera import narrowing

        body = f"let @Int = {text};\n  @Int.0"
        program = parse_to_ast(_shape_program(body))
        let = program.declarations[0].decl.body.statements[0]
        folded = narrowing.literal_range(let.value)
        assert folded is not None and folded[0] == folded[1], folded
        assert _observe(_shape_program(body), "f",
                        [0, 0, 1]).run == f"ran:{folded[0]}"


class TestAScalarLiteralAboveI64MaxIsANat:
    """The value rule at the scalar positions a component is not: a
    literal-only value above `i64.MAX` reaches an `@Int` slot through
    arithmetic or an array element with no `@Int` context to range-check
    it, and returned -1 on `main` and on the release branch.  Refused by
    both halves now, like its component twins."""

    @pytest.mark.parametrize("body", [
        f"let @Int = {_U64_MAX} + 0;\n  @Int.0",
        f"let @Array<Int> = [{_U64_MAX}];\n  @Array<Int>.0[0]",
    ])
    def test_both_halves_refuse(self, body: str) -> None:
        observed = _observe(_shape_program(body), "f", [0, 0, 1])
        assert "E530" in observed.errors, observed.obligations
        assert _WIDEN_GUARD in observed.run, observed.run


# =====================================================================
# The type-source differential
# =====================================================================
#
# The oracle below is the test's own, written from the spec rather than
# imported from the implementation, so the instrument cannot agree with the
# code by construction.  A checker type DISAGREES with the value when the
# checker says `@Nat` for an expression whose value can be negative: a
# literal-only part of its value-producing tree that evaluates below zero —
# the #520 idiom, whose value is whatever the literals make it.  A composite
# disagrees where one of its components does.

def _pure_literal(expr: ast.Expr) -> bool:
    """Every value-producing leaf of *expr* is an integer literal."""
    if isinstance(expr, ast.IntLit):
        return True
    if isinstance(expr, ast.BinaryExpr) and expr.op in _ARITH:
        return _pure_literal(expr.left) and _pure_literal(expr.right)
    if isinstance(expr, ast.UnaryExpr):
        return _pure_literal(expr.operand)
    if isinstance(expr, ast.Block):
        return expr.expr is not None and _pure_literal(expr.expr)
    if isinstance(expr, ast.IfExpr):
        return (expr.else_branch is not None
                and _pure_literal(expr.then_branch)
                and _pure_literal(expr.else_branch))
    if isinstance(expr, ast.MatchExpr):
        return bool(expr.arms) and all(_pure_literal(a.body)
                                       for a in expr.arms)
    return False


def _literal_values(expr: ast.Expr) -> set[int] | None:
    """Every value a literal-only *expr* can take — each arm of an `if` or a
    `match` separately — or None where it cannot be evaluated."""
    if isinstance(expr, ast.IntLit):
        return {expr.value}
    if isinstance(expr, ast.UnaryExpr):
        inner = _literal_values(expr.operand)
        return None if inner is None else {-v for v in inner}
    if isinstance(expr, ast.Block):
        return None if expr.expr is None else _literal_values(expr.expr)
    if isinstance(expr, (ast.IfExpr, ast.MatchExpr)):
        arms = ([expr.then_branch, expr.else_branch]
                if isinstance(expr, ast.IfExpr)
                else [a.body for a in expr.arms])
        out: set[int] = set()
        for arm in arms:
            vals = None if arm is None else _literal_values(arm)
            if vals is None:
                return None
            out |= vals
        return out
    if isinstance(expr, ast.BinaryExpr) and expr.op in _ARITH:
        left, right = _literal_values(expr.left), _literal_values(expr.right)
        if left is None or right is None:
            return None
        out = set()
        for a in left:
            for b in right:
                if expr.op == ast.BinOp.ADD:
                    out.add(a + b)
                elif expr.op == ast.BinOp.SUB:
                    out.add(a - b)
                elif expr.op == ast.BinOp.MUL:
                    out.add(a * b)
                elif b == 0:
                    return None
                else:
                    q = int(a / b) if abs(a) < 2 ** 52 else None
                    if q is None:
                        return None
                    out.add(q if expr.op == ast.BinOp.DIV else a - b * q)
        return out
    return None


def _literal_underflow(expr: ast.Expr) -> bool:
    """A literal-only part of *expr*'s value can be below zero."""
    if _pure_literal(expr):
        vals = _literal_values(expr)
        return vals is None or min(vals) < 0
    if isinstance(expr, ast.BinaryExpr) and expr.op in _ARITH:
        return (_literal_underflow(expr.left)
                or _literal_underflow(expr.right))
    if isinstance(expr, ast.UnaryExpr):
        return _literal_underflow(expr.operand)
    if isinstance(expr, ast.Block):
        return expr.expr is not None and _literal_underflow(expr.expr)
    if isinstance(expr, ast.IfExpr):
        return (expr.else_branch is not None
                and (_literal_underflow(expr.then_branch)
                     or _literal_underflow(expr.else_branch)))
    if isinstance(expr, ast.MatchExpr):
        return any(_literal_underflow(a.body) for a in expr.arms)
    if isinstance(expr, ast.HandleExpr):
        # A `handle`'s value is its body's, or a clause's that does not
        # resume (a `resume(...)` is a call, and no literal).
        return (_literal_underflow(expr.body)
                or any(_literal_underflow(c.body) for c in expr.clauses))
    if isinstance(expr, ast.IndexExpr):
        return any(_literal_underflow(e)
                   for e in _element_exprs(expr.collection))
    return False


def _element_exprs(expr: ast.Expr) -> list:
    """The elements an array value can come from, built here: through
    blocks, `if`s, `match`es and `handle`s to the array literals."""
    if isinstance(expr, ast.ArrayLit):
        return list(expr.elements)
    if isinstance(expr, ast.Block):
        return [] if expr.expr is None else _element_exprs(expr.expr)
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return []
        return (_element_exprs(expr.then_branch)
                + _element_exprs(expr.else_branch))
    if isinstance(expr, ast.MatchExpr):
        return [e for a in expr.arms for e in _element_exprs(a.body)]
    if isinstance(expr, ast.HandleExpr):
        return (_element_exprs(expr.body)
                + [e for c in expr.clauses for e in _element_exprs(c.body)])
    return []


_ARITH = frozenset({
    ast.BinOp.ADD, ast.BinOp.SUB, ast.BinOp.MUL, ast.BinOp.DIV,
    ast.BinOp.MOD,
})

#: constructor name -> (the ADT's type parameters, each field's declared
#: type name) for the built-in parameterised constructors.
_BUILTIN_CTORS: dict[str, tuple[tuple[str, ...], tuple[str | None, ...]]] = {
    "Some": (("T",), ("T",)),
    "Ok": (("T", "E"), ("T",)),
    "Err": (("T", "E"), ("E",)),
}


def _ctor_table(program: ast.Program) -> dict:
    table = dict(_BUILTIN_CTORS)
    for top in program.declarations:
        decl = top.decl
        if not isinstance(decl, ast.DataDecl):
            continue
        params = tuple(decl.type_params or ())
        for ctor in decl.constructors:
            table[ctor.name] = (params, tuple(
                f.name if isinstance(f, ast.NamedType) and not f.type_args
                else None
                for f in (ctor.fields or ())
            ))
    return table


def _component_exprs(expr: ast.Expr, position: int, ctors: dict) -> list:
    """The expressions that supply type argument *position* of *expr*'s
    value, reached through `if` / `match` / `handle` / block tails and an
    index into an array built here."""
    if isinstance(expr, ast.Block):
        return ([] if expr.expr is None
                else _component_exprs(expr.expr, position, ctors))
    if isinstance(expr, ast.IfExpr):
        if expr.else_branch is None:
            return []
        return (_component_exprs(expr.then_branch, position, ctors)
                + _component_exprs(expr.else_branch, position, ctors))
    if isinstance(expr, ast.MatchExpr):
        out: list = []
        for arm in expr.arms:
            out.extend(_component_exprs(arm.body, position, ctors))
        return out
    if isinstance(expr, ast.HandleExpr):
        out = _component_exprs(expr.body, position, ctors)
        for clause in expr.clauses:
            out.extend(_component_exprs(clause.body, position, ctors))
        return out
    if isinstance(expr, ast.IndexExpr):
        return [c for element in _element_exprs(expr.collection)
                for c in _component_exprs(element, position, ctors)]
    if isinstance(expr, ast.ArrayLit):
        return list(expr.elements) if position == 0 else []
    if isinstance(expr, ast.ConstructorCall):
        if expr.name == "Tuple":
            return ([expr.args[position]] if position < len(expr.args)
                    else [])
        info = ctors.get(expr.name)
        if info is None:
            return []
        params, fields = info
        if position >= len(params):
            return []
        return [arg for arg, field in zip(expr.args, fields)
                if field == params[position]]
    return []


def _classified(expr: ast.Expr, ty: Type, ctors: dict) -> Type:
    """*ty* with the classifier's answer wherever the checker's disagrees."""
    if ty == NAT and _literal_underflow(expr):
        return INT
    if isinstance(ty, AdtType) and ty.type_args:
        args = list(ty.type_args)
        for position, arg_ty in enumerate(ty.type_args):
            for source in _component_exprs(expr, position, ctors):
                fixed = _classified(source, arg_ty, ctors)
                if fixed != arg_ty:
                    args[position] = fixed
                    break
        if tuple(args) != ty.type_args:
            return AdtType(ty.name, tuple(args))
    return ty


def _exprs(node: object) -> list[ast.Expr]:
    """Every expression node under *node*."""
    out: list[ast.Expr] = []
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Expr):
            out.append(cur)
        if isinstance(cur, ast.Node):
            for f in fields(cur):
                stack.append(getattr(cur, f.name))
        elif isinstance(cur, (list, tuple)):
            stack.extend(cur)
    return out


def _disagreements(program: ast.Program, table: dict) -> dict:
    """span key -> (checker's type, the classifier's) where they differ."""
    ctors = _ctor_table(program)
    out = {}
    for expr in _exprs(program):
        key = ast.span_key(expr)
        ty = table.get(key) if key is not None else None
        if ty is None:
            continue
        fixed = _classified(expr, ty, ctors)
        if fixed != ty:
            out[key] = (ty, fixed)
    return out


def _pipeline(path: Path, semantic_override: bool) -> tuple:
    """(errors, obligations, checks) for *path* the way `vera verify` and
    `vera compile` see it — with, when *semantic_override*, the classifier's
    answer substituted into the entry module's semantic table wherever the
    checker's disagrees."""
    source = path.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    resolver = ModuleResolver(_root=path.parent)
    resolved = resolver.resolve_imports(program, path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    if resolver.errors or any(d.severity == "error" for d in diags):
        return None
    sem = dict(arts.expr_semantic_types)
    if semantic_override:
        for key, (_checker, fixed) in _disagreements(program, sem).items():
            sem[key] = fixed
    result = verify(
        program, source, file=str(path), resolved_modules=resolved,
        expr_types=sem, expr_target_types=arts.expr_target_types,
    )
    compiled = codegen_compile(
        program, source=source, file=str(path), resolved_modules=resolved,
        expr_semantic_types=sem, expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    return (
        tuple(sorted(d.error_code for d in result.diagnostics
                     if d.severity == "error")),
        tuple(sorted((o.kind, o.status, o.line, o.column)
                     for o in result.obligations)),
        tuple(sorted((c.emitter, c.line, c.column)
                     for c in compiled.emitted_checks)),
        tuple(sorted(d.error_code for d in compiled.diagnostics
                     if d.severity == "error")),
        # The module itself: a check's record names its emitter and its
        # node, not what it compares — an overflow guard over the signed
        # range and one over the unsigned range are one record.
        compiled.wat,
    )


_ROOT = Path(__file__).resolve().parents[1]
_CORPUS = sorted(
    list((_ROOT / "examples").glob("*.vera"))
    + list((_ROOT / "tests" / "conformance").glob("*.vera"))
)

_DIFFERENTIAL_PROGRAMS = {
    **{f"{p} / {v} / {t}": _program(p, v, t)
       for p, v in _MATRIX for t in ("Int", "Nat")},
    **{f"operand {label}": _shape_program(body)
       for label, body, _args, _value in _OPERAND_CELLS},
}


def _movers(path: Path) -> list[str]:
    """What moves when the checker's answer is replaced by the classifier's
    at every node where they disagree: one line per changed output."""
    plain = _pipeline(path, False)
    fixed = _pipeline(path, True)
    assert plain is not None and fixed is not None, (
        f"{path.name} did not reach verification and code generation, so "
        "the differential would compare nothing"
    )
    if plain == fixed:
        return []
    names = ("errors", "obligations", "checks", "codegen errors", "WAT")
    out = []
    for name, a, b in zip(names, plain, fixed):
        if a == b:
            continue
        if name == "WAT":
            out.append("WAT: the emitted module differs")
        else:
            out.append(f"{name}: -{sorted(set(a) - set(b))} "
                       f"+{sorted(set(b) - set(a))}")
    return out


class TestTypeSourceDifferential:
    """No guard and no obligation reads the checker's type where it is wrong.

    The lever is the semantic table itself.  Every node where the checker's
    type disagrees with the classifier (the oracle above) is overwritten
    with the classifier's answer, and the verifier and code generation are
    run on both tables.  A decision that reads the table at such a node —
    directly, or through a helper — changes an obligation or a guard, and
    shows here by name.  One that reads only the classifier cannot move.
    """

    @pytest.mark.parametrize("label", sorted(_DIFFERENTIAL_PROGRAMS))
    def test_the_matrix_does_not_move(
        self, label: str, tmp_path: Path,
    ) -> None:
        path = tmp_path / "p.vera"
        path.write_text(_DIFFERENTIAL_PROGRAMS[label], encoding="utf-8")
        program = parse_to_ast(_DIFFERENTIAL_PROGRAMS[label])
        _diags, arts = typecheck_with_artifacts(
            program, _DIFFERENTIAL_PROGRAMS[label], file=str(path))
        assert _disagreements(program, arts.expr_semantic_types), (
            "the program holds no disagreement, so it tests nothing"
        )
        assert _movers(path) == []

    def test_the_corpus_does_not_move(self) -> None:
        """Every example and conformance program that holds a disagreement.

        Asserted non-vacuous first: the sweep must have found programs to
        test, or an oracle that stopped recognising the idiom would pass it
        by finding nothing.
        """
        tested: list[str] = []
        moved: dict[str, list[str]] = {}
        for path in _CORPUS:
            source = path.read_text(encoding="utf-8")
            program = parse_to_ast(source)
            resolver = ModuleResolver(_root=path.parent)
            resolved = resolver.resolve_imports(program, path)
            diags, arts = typecheck_with_artifacts(
                program, source, file=str(path), resolved_modules=resolved)
            if resolver.errors or any(d.severity == "error" for d in diags):
                continue
            if not _disagreements(program, arts.expr_semantic_types):
                continue
            tested.append(path.name)
            movers = _movers(path)
            if movers:
                moved[path.name] = movers
        assert len(tested) >= 20, tested
        assert moved == {}, moved

    def test_the_lever_reports_a_reader_of_the_checker(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The instrument can see a mover: re-plant the release branch's
        destructure guard, which read the checker's type for the whole
        source, and the same program must move."""
        from vera.wasm.data import DataMixin

        def checker_reading(self: DataMixin, stmt: ast.LetDestruct,
                            index: int) -> bool:
            return self._adt_arg_is_nat(
                self._checker_resolved_type(stmt.value), index)

        path = tmp_path / "p.vera"
        path.write_text(_program("tuple destructure", "0 - 3", "Int"),
                        encoding="utf-8")
        assert _movers(path) == []
        monkeypatch.setattr(
            DataMixin, "_destructure_component_is_nat", checker_reading)
        assert _movers(path), (
            "the differential cannot see a guard that reads the checker"
        )

    @pytest.mark.parametrize("body", [
        "let @Int = (0 - 3) - @Nat.0;\n  @Int.0",
        "let @Nat = @Nat.0 + (0 - 1);\n  @Nat.0",
    ])
    def test_the_mixed_sign_operation_is_the_residual(
        self, body: str, tmp_path: Path,
    ) -> None:
        """A PIN, not a property: the one place a decision still reads the
        checker's `@Nat` where the value can be negative.

        An operation mixing a genuine `@Nat` operand with a negative
        literal-only one — the `@Nat`-subtraction test for `(0 - 3) -
        @Nat.0`, the width of `@Nat.0 + (0 - 1)` — keeps the checker's
        answer, because the classifier has no correct one to give: the
        signed width would reinterpret a `@Nat` above `i64.MAX`
        (`TestAnOperationWithAGenuineNatKeepsItsWidth`).  So replacing the
        checker's `@Nat` for the literal part MOVES these programs, and this
        cell says so; it goes red, to be flipped, when mixed-sign arithmetic
        gains the operand-widening check that decides it.
        """
        path = tmp_path / "p.vera"
        path.write_text(_shape_program(body), encoding="utf-8")
        assert _movers(path)


# =====================================================================
# The reader roster
# =====================================================================

#: Every function in code generation and the verifier that reads the
#: checker's SEMANTIC table, with the reason it may.  A decision about a
#: value's sign reads it only as a declaration's answer — a call's return,
#: an opaque composite's declared component — or through the shared sign
#: classifier; every other reader asks a question the sign does not enter.
#: A new reader fails this roster whatever it does, so the review that adds
#: it has to say which of these it is.
_LEAF = "the classifier's leaf: a declaration's type, never a literal's"
_MEASURE = ("a `decreases` component's width; a literal-only measure is a "
            "constant, which no recursive call decreases")
_WIDTH = ("an operand's width, after literal_operation_width has classified "
          "an operation of two literal-only operands by value; a mixed-sign "
          "operation keeps the checker's (the pinned residual)")
_READERS: dict[tuple[str, str, str], str] = {
    ("vera/codegen/closures.py",
     "ClosureLiftingMixin._compile_lifted_closure",
     "_expr_semantic_types"): "threads the table into a closure's context",
    ("vera/codegen/contracts.py", "ContractsMixin._dec_nat_measure_indices",
     "_checker_resolved_type"): _MEASURE,
    ("vera/codegen/core.py", "CodeGenerator.__init__",
     "_expr_semantic_types"): "stores the table",
    ("vera/codegen/functions.py", "FunctionCompilationMixin._compile_fn",
     "_expr_semantic_types"): "threads the table into a function's context",
    ("vera/codegen/monomorphize.py",
     "MonomorphizationMixin._build_mono_context",
     "_expr_semantic_types"): "clone naming (#1327), not a guard",
    ("vera/codegen/monomorphize.py",
     "MonomorphizationMixin._report_uninferred_type_args",
     "_expr_semantic_types"): "a diagnostic about instantiation",
    ("vera/verifier.py", "ContractVerifier._declared_result_is_nat",
     "_resolved_type_of"): _LEAF,
    ("vera/verifier.py", "ContractVerifier._check_decreases_bound",
     "_resolved_type_of"): _MEASURE,
    ("vera/verifier.py", "ContractVerifier._check_div_zero_obligation",
     "_resolved_type_of"): "whether the divisor is a Float64",
    ("vera/verifier.py",
     "ContractVerifier._check_nested_refinement_obligation",
     "_resolved_type_of"): "a refinement's predicate, never inferred "
                           "from a literal",
    ("vera/verifier.py", "ContractVerifier._declared_path_type",
     "_resolved_type_of"): _LEAF + " (down an enclosing pattern's path)",
    ("vera/verifier.py", "ContractVerifier._decreases_chain_may_be_declined",
     "_resolved_type_of"): "whether a measure component is rankable",
    ("vera/verifier.py", "ContractVerifier._has_nat_origin",
     "_resolved_type_of"): _LEAF + " (a call's or an index's element)",
    ("vera/verifier.py", "ContractVerifier._is_nat_typed",
     "_resolved_type_of"): "the static half of _narrows_into_nat, whose "
                           "underflow-leaf half refutes the literal case; "
                           "and the @Nat-subtraction test, which a "
                           "mixed-sign operation reaches (the pinned "
                           "residual)",
    ("vera/verifier.py", "ContractVerifier._narrows_into_refined",
     "_resolved_type_of"): "a refinement's identity, never inferred from "
                           "a literal",
    ("vera/verifier.py", "ContractVerifier._obligate_destructure_narrowings",
     "_resolved_type_of"): "the source's arity and refined components; "
                           "the sign legs read the component classifier",
    ("vera/verifier.py", "ContractVerifier._obligate_subpattern_narrowings",
     "_resolved_type_of"): "field enumeration and refined fields, plus "
                           "the component classifier's leaf",
    ("vera/verifier.py", "ContractVerifier._overflow_arith_fail_closed",
     "_resolved_type_of"): "whether an operand is a non-integer type",
    ("vera/verifier.py", "ContractVerifier._overflow_int_type",
     "_resolved_type_of"): _WIDTH,
    ("vera/verifier.py", "ContractVerifier._subpattern_source_facts",
     "_resolved_type_of"): "facts an opaque scrutinee's declaration "
                           "establishes",
    ("vera/verifier.py", "ContractVerifier._walk_for_nat_binding_obligations",
     "_resolved_type_of"): "facts a slot or call source establishes",
    ("vera/wasm/calls.py", "CallsMixin._unify_param_arg_wasm",
     "_expr_semantic_types"): "clone naming (#1327), not a guard",
    ("vera/wasm/context.py", "WasmContext.__init__",
     "_expr_semantic_types"): "stores the table",
    ("vera/wasm/context.py", "WasmContext.set_expr_semantic_types",
     "_expr_semantic_types"): "stores the table",
    ("vera/wasm/data.py", "DataMixin._declared_path_type",
     "_checker_resolved_type"): _LEAF + " (down an enclosing pattern's path)",
    ("vera/wasm/data.py", "DataMixin._destructure_ctor_name",
     "_checker_resolved_type"): "which constructor's fields a destructure "
                                "binds: the source's type NAME, never a "
                                "component's sign",
    ("vera/wasm/inference.py", "InferenceMixin._infer_vera_type",
     "_expr_semantic_types"): "clone naming (#1327): the walker first",
    ("vera/wasm/operators.py", "OperatorsMixin._declared_result_is_nat",
     "_resolved_codegen_type"): _LEAF,
    ("vera/wasm/operators.py", "OperatorsMixin._checker_resolved_type",
     "_expr_semantic_types"): "the accessor",
    ("vera/wasm/operators.py", "OperatorsMixin._has_nat_origin_codegen",
     "_resolved_codegen_type"): "an index's element type as `@Nat` "
                                "provenance, the verifier's "
                                "`_has_nat_origin`; a literal is never a "
                                "leaf of it",
    ("vera/wasm/operators.py", "OperatorsMixin._is_nat_operand",
     "_resolved_codegen_type"): "the static half of the `@Nat`-subtraction "
                                "test, the verifier's `_is_nat_typed`; the "
                                "pure-literal case is exempted by "
                                "provenance, and the mixed-sign one is the "
                                "pinned residual",
    ("vera/wasm/operators.py", "OperatorsMixin._overflow_codegen_type",
     "_resolved_codegen_type"): _WIDTH,
    ("vera/wasm/operators.py", "OperatorsMixin._resolved_codegen_type",
     "_expr_semantic_types"): "the accessor",
}

#: Every function that reads the checker's TARGET table — the type an
#: expression is bound AT.  A target is a declaration's type, one the context
#: forced through an expected type, or an instantiation the checker inferred
#: from an argument; the constructor door no longer records the last kind
#: for an argument holding a pure-literal subtraction (#1503), whose inferred
#: `@Nat` is the claim the classifier refutes, and carries a nested
#: application's context down to its arguments instead.  The function door
#: still records its inferred formal: a generic callee instantiated from a
#: literal subtraction is the checker's and the monomorphizer's to agree on
#: (`id(0 - 3)` is instantiated `Nat` by the one and `id$Int` by the other),
#: not a guard's.
_TARGET = "a target: the type a value is bound at"
_TARGET_READERS: dict[tuple[str, str, str], str] = {
    ("vera/codegen/closures.py",
     "ClosureLiftingMixin._compile_lifted_closure",
     "_expr_target_types"): "threads the table into a closure's context",
    ("vera/codegen/core.py", "CodeGenerator.__init__",
     "_expr_target_types"): "stores the table",
    ("vera/codegen/functions.py", "FunctionCompilationMixin._compile_fn",
     "_expr_target_types"): "threads the table into a function's context",
    ("vera/verifier.py", "ContractVerifier.__init__",
     "_expr_target_types"): "stores the table",
    ("vera/verifier.py", "ContractVerifier._int_widening_target",
     "_target_type_of"): _TARGET,
    ("vera/verifier.py", "ContractVerifier._is_hetero_int_widen_join",
     "_target_type_of"): _TARGET,
    ("vera/verifier.py", "ContractVerifier._nat_binding_target",
     "_target_type_of"): _TARGET,
    ("vera/verifier.py", "ContractVerifier._nested_refinement_formal",
     "_target_type_of"): _TARGET,
    ("vera/verifier.py", "ContractVerifier._refined_binding_target",
     "_target_type_of"): _TARGET,
    ("vera/verifier.py", "ContractVerifier._target_type_of",
     "_expr_target_types"): "the accessor",
    ("vera/verifier.py", "ContractVerifier._walk_for_nat_binding_obligations",
     "_target_type_of"): _TARGET,
    ("vera/wasm/calls_containers.py",
     "CallsContainersMixin._translate_map_insert",
     "_target_codegen_type_refined"): _TARGET,
    ("vera/wasm/context.py", "WasmContext.__init__",
     "_expr_target_types"): "stores the table",
    ("vera/wasm/context.py", "WasmContext.set_expr_target_types",
     "_expr_target_types"): "stores the table",
    ("vera/wasm/data.py", "DataMixin._ctor_field_mono_base",
     "_target_codegen_type_full"): _TARGET,
    ("vera/wasm/data.py", "DataMixin._ctor_field_targets_byte",
     "_target_codegen_type_full"): _TARGET,
    ("vera/wasm/data.py", "DataMixin._emit_construction_refine_guard",
     "_target_codegen_type_refined"): _TARGET,
    ("vera/wasm/data.py", "DataMixin._translate_array_lit",
     "_target_codegen_type_full"): _TARGET,
    ("vera/wasm/data.py", "DataMixin._translate_array_lit",
     "_target_codegen_type_refined"): _TARGET,
    ("vera/wasm/data.py", "DataMixin._translate_constructor_call",
     "_ctor_field_mono_base"): _TARGET,
    ("vera/wasm/data.py", "DataMixin._translate_constructor_call",
     "_target_codegen_type_full"): _TARGET,
    ("vera/wasm/operators.py", "OperatorsMixin._is_hetero_int_widen_join",
     "_target_codegen_type_full"): _TARGET,
    ("vera/wasm/operators.py", "OperatorsMixin._target_codegen_type_full",
     "_expr_target_types"): "the accessor",
    ("vera/wasm/operators.py", "OperatorsMixin._target_codegen_type_refined",
     "_expr_target_types"): "the accessor",
}


def _table_readers(calls: frozenset[str],
                   attr: str) -> set[tuple[str, str, str]]:
    """(file, Class.method, what) for every read of one of the checker's
    tables in code generation and the verifier."""
    import ast as pyast

    files = (sorted((_ROOT / "vera" / "wasm").glob("*.py"))
             + sorted((_ROOT / "vera" / "codegen").glob("*.py"))
             + [_ROOT / "vera" / "verifier.py"])
    found: set[tuple[str, str, str]] = set()
    for path in files:
        tree = pyast.parse(path.read_text(encoding="utf-8"))
        rel = path.relative_to(_ROOT).as_posix()
        for cls in (n for n in pyast.walk(tree)
                    if isinstance(n, pyast.ClassDef)):
            for fn in cls.body:
                if not isinstance(fn, (pyast.FunctionDef,
                                       pyast.AsyncFunctionDef)):
                    continue
                for node in pyast.walk(fn):
                    if (isinstance(node, pyast.Call)
                            and isinstance(node.func, pyast.Attribute)
                            and node.func.attr in calls):
                        found.add((rel, f"{cls.name}.{fn.name}",
                                   node.func.attr))
                    elif (isinstance(node, pyast.Attribute)
                            and node.attr == attr):
                        found.add((rel, f"{cls.name}.{fn.name}", attr))
    return found


def _semantic_table_readers() -> set[tuple[str, str, str]]:
    return _table_readers(frozenset({
        "_checker_resolved_type", "_resolved_codegen_type",
        "_resolved_type_of",
    }), "_expr_semantic_types")


def _target_table_readers() -> set[tuple[str, str, str]]:
    return _table_readers(frozenset({
        "_target_codegen_type_full", "_target_codegen_type_refined",
        "_target_type_of", "_ctor_field_mono_base",
    }), "_expr_target_types")


class TestTheReaderRoster:
    """Where the checker's tables are read, and why each reader may."""

    @pytest.mark.parametrize(("roster", "scan"), [
        (_READERS, _semantic_table_readers),
        (_TARGET_READERS, _target_table_readers),
    ], ids=["semantic table", "target table"])
    def test_every_reader_is_on_the_roster(self, roster, scan) -> None:
        unknown = scan() - set(roster)
        assert not unknown, (
            "a new reader of the checker's table; add it to the roster "
            "with the reason its decision is not a sign read, or route it "
            f"through `vera.narrowing`: {sorted(unknown)}"
        )

    @pytest.mark.parametrize(("roster", "scan"), [
        (_READERS, _semantic_table_readers),
        (_TARGET_READERS, _target_table_readers),
    ], ids=["semantic table", "target table"])
    def test_every_roster_row_is_still_a_reader(self, roster, scan) -> None:
        stale = set(roster) - scan()
        assert not stale, f"roster rows for readers that are gone: {stale}"

    def test_the_sign_guards_read_no_table_themselves(self) -> None:
        """The destructure and sub-pattern widening decisions — the readers
        #1416 and #757 introduced — are not semantic-table readers at all:
        they consult it only through the classifier's leaf."""
        readers = {key[1] for key in _semantic_table_readers()}
        for decision in ("DataMixin._destructure_component_is_nat",
                         "DataMixin._subpattern_field_is_nat",
                         "DataMixin._translate_let_destruct",
                         "DataMixin._translate_constructor_call"):
            assert decision not in readers, decision
