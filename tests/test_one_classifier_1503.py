"""#1503 — every guard and every obligation reads a component where it is built.

Two sources can disagree about a component's sign: the checker's type for a
composite, and the value its construction holds.  `if b then { Tuple(0 - 5,
1) } else { Tuple(3, 1) }` is a `Tuple` whose first component can be -5,
whatever the checker's type for the join says, so a decision that reads the
component — a narrowing obligation, a narrowing guard, a refined binding's
assumed fact — reads it where it is built: the argument that built it where
the source is a constructor application, the declared type of the
constructor's field where the source is opaque (`vera.narrowing`'s
component sources).

A literal is an `Int` (spec §4.2), so `0 - 3` is the `@Int` it is, and the
instrument holds every reader to treating it exactly as an `@Int` parameter
holding -3.  The composite-construction MATRIX runs every position a
literal-arithmetic value can reach a binding through — {tuple, ADT
constructor, `if`-produced, `match`-produced, block-produced,
`let`-destructure, nested} — against both expected numeric types, and says
what each must do: an `@Int` binding returns the value, an `@Nat` binding is
refused on the record and at run time, and the literal is classified exactly
as an `@Int` parameter holding its value.  Where the checker's types are
read is no longer a roster's to pin: every phase reads them off the typed
program, and the class cell of `tests/test_typed_program_1525.py` fails on
any function outside the checker that derives one (#1525).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck_with_artifacts
from vera.parser import parse_to_ast
from tests import pipeline

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file or
# a module that decides its class, here the one sign classifier every guard and
# obligation reads.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/narrowing.py",
    ],
)

_I64_MAX = 2**63 - 1

#: What a tripped `@Int` -> `@Nat` narrowing guard reports (#754).
_NAT_GUARD = "Negative value bound into a @Nat slot"


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


def _check_clean(checked: pipeline.Checked) -> None:
    """Raise the parse error, or fail unless *checked* type-checked cleanly."""
    _ = checked.program  # raises the parse or transform error
    errors = checked.errors
    assert not errors, (
        "fixture must type-check: "
        f"{[(d.error_code, d.description[:80]) for d in errors]}"
    )


def _observe(source: str, fn: str, args: list[object]) -> Observed:
    """Check, verify, compile and run *source* through the checker's tables."""
    verified = pipeline.verify(source, file="fixture.vera")
    _check_clean(verified.checked)
    result = verified.result
    compiled = pipeline.compile(source, file="fixture.vera").result
    cg_errors = [d for d in compiled.diagnostics if d.severity == "error"]
    assert not cg_errors, (
        f"fixture must compile: {[d.description[:80] for d in cg_errors]}"
    )
    try:
        run = f"ran:{pipeline.run(compiled, fn, args, capture_stderr=False).execution.value}"
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

#: The cells whose -3 no rule refuses: the literal's `Array<Wrap<Int>>` is
#: admitted at the `let`'s `Array<Wrap<Nat>>` with no record and no guard,
#: #1695's composite coercion (its #1542 line).  At f1bc772d only this index
#: scrutinee trapped, by an accidental guard: code generation's walker named
#: the element `Wrap`, with no argument, and the sub-pattern bind was guarded
#: for want of the field's type; slot, call and `let` scrutinees of the same
#: value were already silent.  Read off the typed program the element is
#: `Wrap<Nat>`, whose field is a `Nat`, and the bind takes no guard.
_COMPOSITE_COERCION = frozenset({"nested, ADT in array"})
_REFUSED_MATRIX = [
    pytest.param(p, v, id=f"{p} / {v}", marks=pytest.mark.xfail(
        strict=True, reason="#1695 (#1542): the composite coercion is "
        "obligated and guarded nowhere"))
    if p in _COMPOSITE_COERCION else pytest.param(p, v, id=f"{p} / {v}")
    for p, v in _MATRIX
]
_DIRECT_MATRIX = [(p, v) for p, v in _MATRIX if p not in _NESTED]
_DIRECT_IDS = [f"{p} / {v}" for p, v in _DIRECT_MATRIX]

#: The sign-boundary half of each side: the obligation kinds and the guard
#: emitters a value's sign decides.
_SIGN_KINDS = frozenset({"nat_bind"})
_SIGN_EMITTERS = frozenset({
    "wasm/operators.py:_emit_nat_bind_guard",
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
    `@Int` parameter holding -3: the same narrowing obligations, the same
    narrowing guards.  On the release branch the two parted wherever a
    decision read the checker's `@Nat` for the literal — a narrowing
    obligated at the construction for the literal only.  Statuses are not
    compared: a literal is decided at compile time where a parameter is
    not.
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

    On the v0.2.0 release branch the ADT and `Option` positions failed
    `vera verify` with E503 and trapped on the narrowing guard, because a
    decision read the checker's `@Nat` for `0 - 3`.  No `@Nat` value is
    involved anywhere.
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


class TestNegativeLiteralArithmeticIsRefusedByANatBinding:
    """The same -3 bound at `@Nat` is refused.

    Taking the checker's `@Nat` away from a decision must not take the
    narrowing away with it: the run trips the narrowing guard at every
    position, and wherever a reader obligates the bind at all, `vera
    verify` reports it VIOLATED.
    """

    @pytest.mark.parametrize(("position", "value"), _REFUSED_MATRIX)
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


class TestTheComponentReadsOfTheReview:
    """Component readings PR #1537's review found, each a place where a
    decision still took a component's type from the wrong source."""

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
        was guarded as a `@Nat` and a valid -5 trapped.  The `Nat` field,
        read at `@Int`, is the value it holds at the top of the range."""
        source = self._box("Int", "let Box<@Int, @Int> = mk(@Int.0, @Nat.0);"
                                  "\n  @Int.1")
        assert _observe(source, "f", [-5, 7]).run == "ran:-5"
        top = self._box("Int", "let Box<@Int, @Int> = mk(@Int.0, @Nat.0);"
                               "\n  @Int.0")
        assert _observe(top, "f", [3, _I64_MAX]).run == f"ran:{_I64_MAX}"

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
        binds = [o for o in observed.obligations if o[0] == "nat_bind"]
        assert binds == [], observed.obligations

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


# =====================================================================
# A heterogeneous component widens at the argument that supplies it
# =====================================================================


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


#: What a tripped `@Nat`-subtraction guard reports (#1479).
_UNDERFLOW = "would be negative"


class TestANatReturnRefusesAnUnderflowItDoesNotGuard:
    """At a `@Nat` return, the #758 narrowing guard stands down only for a
    value read as a `@Nat` from a form the exemption trusted before #1503 —
    a slot, a call's declared return, arithmetic and joins over them
    (`vera.narrowing.NARROWING_EXEMPTION_READING`).  The widening rule reads
    an index, an effect operation and a `handle` from their declarations
    too; read that way here, the guard stood down for
    `@Array<Nat>.0[0] - @Nat.0`, whose underflow the `@Nat`-subtraction
    guard does not see (its static rule has no index arm), and -3 came
    back from a `@Nat` function (PR #1537 review).  `main` refuses every
    one of these at the return."""

    _PROGRAM = """public fn f(@Nat, @Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  BODY
}
"""

    @pytest.mark.parametrize(("body", "refusal"), [
        ("let @Array<Nat> = [@Nat.1];\n  @Array<Nat>.0[0] - @Nat.0",
         _UNDERFLOW),
        ("let @Array<Nat> = [@Nat.1];\n  @Array<Nat>.0[0] - 5", _NAT_GUARD),
        ("handle[State<Nat>](@Nat = @Nat.1) {\n"
         "    get(@Unit) -> { resume(@Nat.0) },\n"
         "    put(@Nat) -> { resume(()) }\n"
         "  } in {\n    State.get(()) - @Nat.0\n  }", _UNDERFLOW),
        ("(handle[Exn<Int>] {\n    throw(@Int) -> 7\n  } in {\n"
         "    @Nat.1\n  }) - @Nat.0", _UNDERFLOW),
    ], ids=["an index", "an index less a literal", "an effect operation",
            "a handle"])
    def test_the_return_refuses_it(self, body: str, refusal: str) -> None:
        """Refused at run time either way.  Where the subtraction has a
        `@Nat` operand of provenance beside the index, the effect operation
        or the `handle`, code generation reads those as the checker types
        them, `@Nat`, as the verifier does — the `@Nat` subtraction's own
        guard traps, at the site the verifier records `nat_sub` for (PR
        #1583 review).  Otherwise the return's check refuses it."""
        source = self._PROGRAM.replace("BODY", body)
        assert refusal in _observe(source, "f", [2, 5]).run
        assert _observe(source, "f", [8, 5]).run == "ran:3"

    def test_an_effect_operation_leaf_is_refused_by_its_own_return(
        self,
    ) -> None:
        """`State.get(()) - @Nat.0` as the return leaf of an effectful
        callee: the callee refuses the -3 — its `@Nat` subtraction's guard,
        which code generation now plants where the verifier records the
        `nat_sub` — rather than the caller's `@Int` widening reading it as
        a u64 above `i64.MAX`."""
        source = """private fn g(@Nat -> @Nat)
  requires(true)
  ensures(true)
  effects(<State<Nat>>)
{
  State.get(()) - @Nat.0
}

public fn f(@Nat, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Nat>](@Nat = @Nat.1) {
    get(@Unit) -> { resume(@Nat.0) },
    put(@Nat) -> { resume(()) }
  } in {
    g(@Nat.0)
  }
}
"""
        assert _UNDERFLOW in _observe(source, "f", [2, 5]).run
        assert _observe(source, "f", [8, 5]).run == "ran:3"


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


def _observe_modules(
    tmp_path: Path, files: dict[str, str], fn: str, args: list[object],
) -> Observed:
    """:func:`_observe` for an entry module ``main.vera`` beside *files*,
    resolved, checked, verified and compiled as `vera run` does."""
    path = pipeline.write_tree(tmp_path, files)
    verified = pipeline.verify(path)
    checked = verified.checked
    _ = checked.program  # raises the parse or transform error
    resolution_errors = list(checked.resolution_diagnostics)
    assert not resolution_errors, resolution_errors
    errors = [d for d in checked.checker_diagnostics if d.severity == "error"]
    assert not errors, [(d.error_code, d.description[:80]) for d in errors]
    result = verified.result
    compiled = pipeline.compile(path).result
    assert not [d for d in compiled.diagnostics if d.severity == "error"]
    try:
        run = f"ran:{pipeline.run(compiled, fn, args, capture_stderr=False).execution.value}"
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


_WLIB = "module wlib;\n\npublic data Wrap<A> {\n  W(A)\n}\n"


def _main_module(imports: str, params: str, body: str) -> str:
    return (
        f"{imports}\n\ntype PosInt = {{ @Int | @Int.0 > 0 }};\n\n"
        f"public fn f({params})\n  requires(true)\n  ensures(true)\n"
        f"  effects(pure)\n{{\n  {body}\n}}\n"
    )


class TestALookAheadKeepsTheBindingsDiagnostics:
    """A composite pattern's binding types are resolved ahead of the
    construction they read, to give it its context; the look-ahead restores
    the diagnostic state it used, so the binding's own resolution reports
    (PR #1537 review).  Keeping `_error`'s duplicate collapse from the
    look-ahead deduplicated the binding's E135 away, and
    `W(@Array<Unit>)` passed `vera check` and `vera verify` and failed to
    compile."""

    @pytest.mark.parametrize("body", [
        "match W([()]) {\n    W(@Array<Unit>) -> 1\n  }",
        "let Tuple<@Array<Unit>, @Int> = Tuple([()], 1);\n  @Int.0",
    ], ids=["a constructor sub-pattern", "a tuple destructure"])
    def test_e135_is_reported(self, body: str) -> None:
        source = (
            "private data Wrap<A> { W(A) }\n\n"
            "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{\n  " + body + "\n}\n"
        )
        diags, _arts = typecheck_with_artifacts(
            parse_to_ast(source), source, file="p.vera")
        assert "E135" in {d.error_code for d in diags}, [
            (d.error_code, d.description[:60]) for d in diags]


class TestAnImportedTypeNamesItsConstructor:
    """A destructure that names an imported type (`let Wrap<…>`) reads the
    type's constructor from the module table, as the verifier's other
    constructor readers do (PR #1537 review).  Looked up in the local
    registries alone, it found none: the bindings were classified neither
    way and the verifier recorded no obligation, while code generation
    still guarded them."""

    def test_the_refinement_is_obligated(self, tmp_path: Path) -> None:
        observed = _observe_modules(tmp_path, {
            "wlib.vera": _WLIB,
            "main.vera": _main_module(
                "import wlib;", "@Int -> @Int",
                "let Wrap<@PosInt> = W(0 - 5);\n  @PosInt.0"),
        }, "f", [0])
        assert "refine_bind" in {o[0] for o in observed.obligations}, (
            observed.obligations)
        assert "Refinement violation" in observed.run, observed.run

    def test_an_imported_type_name_is_not_another_type_s_constructor(
        self, tmp_path: Path,
    ) -> None:
        """`let Box<…>` over an imported `Box<Nat>`, beside a local
        constructor `Box` of another type: the source's type decides,
        through the module table, so `MkBox`'s `Int` field is read as
        `Int` — no narrowing claimed for either `@Int` binding — and -5
        comes back."""
        blib = ("module blib;\n\npublic data Box<T> {\n  MkBox(Int, T)\n}"
                "\n")
        main = _main_module(
            "import blib;", "@Int, @Nat -> @Int",
            "let @Box<Nat> = MkBox(@Int.0, @Nat.0);\n"
            "  let Box<@Int, @Int> = @Box<Nat>.0;\n  @Int.1",
        ).replace("type PosInt", "private data Other { Box(Nat, Nat) }\n\n"
                  "type PosInt")
        observed = _observe_modules(
            tmp_path, {"blib.vera": blib, "main.vera": main}, "f", [-5, 7])
        assert observed.run == "ran:-5", observed.run
        assert [o for o in observed.obligations
                if o[0] == "nat_bind"] == [], observed.obligations


# =====================================================================
# The type-source differential
# =====================================================================
#
# The oracle below is the test's own, written from the spec rather than
# imported from the implementation, so the instrument cannot agree with the
# code by construction.  Before #1541 the checker typed a literal-only
# expression bottom-up — every literal `@Nat`, `Nat - Nat` a `Nat` — so it
# said `@Nat` for `0 - 3`, whose value is -3.  Since #1541 it types such an
# expression by its value, and the table agrees with the value at every
# literal-only node.  The lever PLANTS the old reading back: at every
# literal-only node the checker now types `@Int` and the bottom-up rule
# typed `@Nat`, and at every composite whose component comes from one, the
# table is given the old `@Nat`.  A decision that reads the table at a
# literal node moves; one that reads the literal's value cannot.
