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

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.resolver import ModuleResolver
from vera.types import INT, NAT, AdtType, Type
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

_PRELUDE = "private data Wrap<A> { W(A) }\n\n"

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
    return False


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
    value, reached through `if` / `match` / block tails."""
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
    if plain is None or plain == fixed:
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
    ("vera/verifier.py", "ContractVerifier._call_result_is_nat",
     "_resolved_type_of"): _LEAF,
    ("vera/verifier.py", "ContractVerifier._check_decreases_bound",
     "_resolved_type_of"): _MEASURE,
    ("vera/verifier.py", "ContractVerifier._check_div_zero_obligation",
     "_resolved_type_of"): "whether the divisor is a Float64",
    ("vera/verifier.py",
     "ContractVerifier._check_nested_refinement_obligation",
     "_resolved_type_of"): "a refinement's predicate, never inferred "
                           "from a literal",
    ("vera/verifier.py", "ContractVerifier._declared_component_is_nat",
     "_resolved_type_of"): _LEAF,
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
    ("vera/wasm/data.py", "DataMixin._declared_component_is_nat",
     "_checker_resolved_type"): _LEAF,
    ("vera/wasm/inference.py", "InferenceMixin._infer_vera_type",
     "_expr_semantic_types"): "clone naming (#1327): the walker first",
    ("vera/wasm/operators.py", "OperatorsMixin._call_result_is_nat",
     "_resolved_codegen_type"): _LEAF,
    ("vera/wasm/operators.py", "OperatorsMixin._checker_resolved_type",
     "_expr_semantic_types"): "the accessor",
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
