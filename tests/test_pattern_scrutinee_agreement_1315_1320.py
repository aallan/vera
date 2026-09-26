"""#1315 / #1320 — a pattern must be able to match the scrutinee's type.

Two issues, one hole.  ``_check_pattern`` dispatched on the pattern's own
form and never compared it with the scrutinee type, so every pattern form
admitted a scrutinee it cannot match:

* ``Some(@Int)`` / ``None`` over ``Array<T>``, ``Map<K,V>``, ``Set<T>`` —
  #1315.  ``_check_exhaustiveness`` returned early on an ADT with no
  ``data_types`` entry ("unknown ADT, can't check"), and the built-in
  containers have none, so nothing objected.
* ``true`` over ``Int``, ``1`` over ``String``, ``"x"`` over ``Int`` —
  #1320.  The literal arms of ``_check_pattern`` returned ``[]``
  unconditionally.

Neither was limited to the shapes the issues name.  Measured on
``origin/release/v0.2.0`` (6dc41d40), all of these type-checked with zero
diagnostics:

* ``Some(@Int) -> 1, _ -> 2`` over an ``Int`` scrutinee — the wildcard
  satisfies exhaustiveness, so the E313 backstop the issues credit for
  refusing primitive scrutinees never fires;
* ``Circle(@Int)`` (a constructor of ``Shape``) over a ``Color``
  scrutinee, and ``None`` as a third arm of an exhaustive ``Color`` match;
* ``@String -> 1`` as a binding pattern over an ``Int`` scrutinee;
* ``Tuple(@Int, @Int)`` over ``Array<Int>``;
* ``Some(true)`` over ``Option<Int>`` — the mismatch one level down.

The consequences are as varied as the shapes: ``match map_new() {
Some(@Int) -> 1, None -> 2 }`` compiled and ran, printing ``2``;
``match @Int.0 { true -> 100, _ -> 200 }`` failed WASM validation
("expected i32, found i64"); the #1315 repro dropped its export.  All
three are the same missing comparison.

The fix is one rule applied to every pattern form before the form's own
checking (:meth:`_check_pattern_scrutinee`), reporting E314.  The cells
below vary the axis the rule's correctness turns on — pattern form ×
scrutinee type — in both directions, because a rule that rejects the
whole matrix would pass every rejection cell and break the language.

Deliberate boundary, tested in ``TestBoundaries``: a scrutinee whose type
is (or contains) an unresolved type variable is skipped.  ``forall<T>``
means ``T`` can be instantiated at ``Option<Int>``, so ``Some(@Int)`` over
``@T.0`` is not decidable in the generic body.
"""
from __future__ import annotations

import pytest

from tests.checker_helpers import _check, _check_clean, _check_ok, _errors


# =====================================================================
# Sources
# =====================================================================

def _fn(params: str, body: str) -> str:
    return (
        f"public fn probe({params} -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"{body}\n"
        "}\n"
    )


def _match(scrutinee: str, arms: str) -> str:
    return f"  match {scrutinee} {{\n{arms}\n  }}"


COLOR_SHAPE = (
    "private data Color {\n"
    "  Red,\n"
    "  Green\n"
    "}\n\n"
    "private data Shape {\n"
    "  Circle(Int),\n"
    "  Square(Int)\n"
    "}\n\n"
)


def _e314(diags: list) -> list:
    return [d for d in diags if d.error_code == "E314"]


def _assert_e314(source: str, *, needles: tuple[str, ...] = ()) -> None:
    """Assert the source is rejected with E314 (an error, not a warning)."""
    diags = _check(source)
    hits = _e314(diags)
    assert hits, (
        "expected E314, got: "
        f"{[(d.error_code, d.severity, d.description) for d in diags]}"
    )
    assert all(d.severity == "error" for d in hits), (
        f"E314 must be an error: {[(d.severity, d.description) for d in hits]}"
    )
    for needle in needles:
        assert any(needle in d.description for d in hits), (
            f"expected {needle!r} in the E314 description, got: "
            f"{[d.description for d in hits]}"
        )


# =====================================================================
# The issues' own repros, verbatim
# =====================================================================

class TestIssueRepros:

    def test_1315_repro_json_keys(self) -> None:
        """#1315's repro: `json_keys` returns Array<String>, not Option<...>."""
        _assert_e314(
            "public fn count(@Json -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match json_keys(@Json.0) {\n"
            "    Some(@Array<String>) -> array_length(@Array<String>.0),\n"
            "    None -> 0\n"
            "  }\n"
            "}\n",
            needles=("Some", "Array<String>"),
        )

    def test_1315_map_scrutinee(self) -> None:
        """The container form: `match map_new() { Some(@Int), None }`.

        This one compiled AND ran on the base revision, printing 2 — the
        silent-wrong-answer end of the family, not a codegen crash.
        """
        _assert_e314(
            _fn("@Unit", _match(
                "map_new()",
                "    Some(@Int) -> 1,\n    None -> 2",
            )),
            needles=("Some", "Map<"),
        )

    def test_1320_repro_bool_literal_over_int(self) -> None:
        """#1320's repro: a Bool literal pattern over an Int scrutinee."""
        _assert_e314(
            _fn("@Int", _match("@Int.0", "    true -> 100,\n    _ -> 200")),
            needles=("Bool", "Int"),
        )


# =====================================================================
# Constructor and nullary patterns
# =====================================================================

class TestConstructorPatternAgainstScrutinee:

    @pytest.mark.parametrize(
        ("param", "scrutinee"),
        [
            ("@Array<Int>", "@Array<Int>.0"),
            ("@Map<String, Int>", "@Map<String, Int>.0"),
            ("@Set<Int>", "@Set<Int>.0"),
        ],
    )
    def test_option_arms_over_container(self, param: str, scrutinee: str) -> None:
        """#1315 proper: the constructor-less built-in containers."""
        _assert_e314(_fn(param, _match(
            scrutinee, "    Some(@Int) -> 1,\n    None -> 2",
        )))

    @pytest.mark.parametrize(
        ("param", "scrutinee"),
        [
            ("@Int", "@Int.0"),
            ("@String", "@String.0"),
            ("@Bool", "@Bool.0"),
            ("@Float64", "@Float64.0"),
        ],
    )
    def test_constructor_over_primitive_with_catch_all(
        self, param: str, scrutinee: str,
    ) -> None:
        """The E313 backstop does not cover this: a wildcard silences it.

        The issues describe primitive scrutinees as "correctly refused with
        E313".  That refusal is about exhaustiveness — add the catch-all it
        asks for and the ill-typed constructor arm is accepted again.
        """
        _assert_e314(_fn(param, _match(
            scrutinee, "    Some(@Int) -> 1,\n    _ -> 2",
        )))

    def test_constructor_of_another_user_adt(self) -> None:
        """`Circle` belongs to Shape; the scrutinee is a Color."""
        _assert_e314(
            COLOR_SHAPE + _fn("@Color", _match(
                "@Color.0", "    Circle(@Int) -> @Int.0,\n    _ -> 2",
            )),
            needles=("Circle", "Color"),
        )

    def test_nullary_of_another_adt_in_exhaustive_match(self) -> None:
        """`None` as a dead third arm of an otherwise exhaustive Color match."""
        _assert_e314(
            COLOR_SHAPE + _fn("@Color", _match(
                "@Color.0",
                "    Red -> 1,\n    Green -> 2,\n    None -> 3",
            )),
            needles=("None", "Color"),
        )

    def test_builtin_adt_constructor_over_other_builtin_adt(self) -> None:
        """`JNull` (Json) over an `Option<Int>` scrutinee."""
        _assert_e314(_fn("@Option<Int>", _match(
            "@Option<Int>.0", "    JNull -> 1,\n    _ -> 2",
        )))

    def test_result_constructor_over_option(self) -> None:
        _assert_e314(_fn("@Option<Int>", _match(
            "@Option<Int>.0", "    Ok(@Int) -> @Int.0,\n    _ -> 0",
        )))

    def test_tuple_pattern_arity_mismatch(self) -> None:
        """The variadic carrier has no E321 field-count rule of its own.

        `Tuple(@Int)` over a `Tuple<Int, Bool>` scrutinee bound component
        0 and ignored the rest: check-green, and it RAN — the base
        revision returned 7 for `Tuple(7, true)`.  The type-confusing
        spelling is worse: `Tuple(@Bool) -> @Bool.0` over the same type
        binds an `Int` component through a `Bool` binder and returns 0
        for `Tuple(7, false)`, a value neither component holds.
        """
        _assert_e314(
            _fn("@Tuple<Int, Bool>", _match(
                "@Tuple<Int, Bool>.0", "    Tuple(@Int) -> @Int.0",
            )),
            needles=("Tuple", "Tuple<Int, Bool>"),
        )
        _assert_e314(
            _fn("@Tuple<Int, Bool>", _match(
                "@Tuple<Int, Bool>.0",
                "    Tuple(@Int, @Bool, @Int) -> @Int.0",
            )),
        )

    def test_tuple_pattern_over_array(self) -> None:
        _assert_e314(_fn("@Array<Int>", _match(
            "@Array<Int>.0", "    Tuple(@Int, @Int) -> 1,\n    _ -> 2",
        )))

    def test_unknown_constructor_still_e320_only(self) -> None:
        """An unregistered constructor name keeps its own diagnostic.

        E314 compares against a constructor that exists; a name that names
        nothing is E320's job, and stacking both would be two errors for
        one mistake.
        """
        diags = _check(_fn("@Option<Int>", _match(
            "@Option<Int>.0", "    Nope(@Int) -> 1,\n    _ -> 2",
        )))
        assert [d.error_code for d in diags] == ["E320"], (
            f"{[(d.error_code, d.description) for d in diags]}"
        )


# =====================================================================
# Literal patterns
# =====================================================================

class TestLiteralPatternAgainstScrutinee:

    @pytest.mark.parametrize(
        ("param", "scrutinee", "literal"),
        [
            ("@Int", "@Int.0", "true"),
            ("@Int", "@Int.0", '"x"'),
            ("@Nat", "@Nat.0", "false"),
            ("@String", "@String.0", "true"),
            ("@String", "@String.0", "1"),
            ("@Bool", "@Bool.0", "1"),
            ("@Bool", "@Bool.0", '"x"'),
            ("@Float64", "@Float64.0", '"x"'),
            ("@Float64", "@Float64.0", "true"),
            ("@Array<Int>", "@Array<Int>.0", "1"),
            ("@Array<Int>", "@Array<Int>.0", '"x"'),
            ("@Option<Int>", "@Option<Int>.0", "1"),
            ("@Map<String, Int>", "@Map<String, Int>.0", "true"),
        ],
    )
    def test_literal_over_wrong_scrutinee(
        self, param: str, scrutinee: str, literal: str,
    ) -> None:
        _assert_e314(_fn(param, _match(
            scrutinee, f"    {literal} -> 100,\n    _ -> 200",
        )))

    @pytest.mark.parametrize(
        ("param", "scrutinee", "arms"),
        [
            ("@Int", "@Int.0", "    1 -> 100,\n    _ -> 200"),
            ("@Nat", "@Nat.0", "    0 -> 100,\n    _ -> 200"),
            ("@String", "@String.0", '    "x" -> 100,\n    _ -> 200'),
            ("@Bool", "@Bool.0", "    true -> 100,\n    false -> 200"),
        ],
    )
    def test_matching_literal_accepted(
        self, param: str, scrutinee: str, arms: str,
    ) -> None:
        _check_clean(_fn(param, _match(scrutinee, arms)))


# =====================================================================
# Binding patterns
# =====================================================================

class TestBindingPatternAgainstScrutinee:

    def test_unrelated_binding_type_rejected(self) -> None:
        """`@String` binding a value the scrutinee says is an Int."""
        _assert_e314(
            _fn("@Int", _match("@Int.0", "    @String -> 1")),
            needles=("String", "Int"),
        )

    def test_adt_binding_over_primitive_rejected(self) -> None:
        _assert_e314(_fn("@Int", _match(
            "@Int.0", "    @Option<Int> -> 1",
        )))

    @pytest.mark.parametrize(
        ("param", "scrutinee", "binder", "body"),
        [
            # Nat <: Int — widening, always sound.
            ("@Nat", "@Nat.0", "@Int", "@Int.0"),
            # Int -> Nat narrowing is the VERIFIER's obligation (E503),
            # not a type error; E314 must not pre-empt it.
            ("@Int", "@Int.0", "@Nat", "1"),
            # Same type.
            ("@Int", "@Int.0", "@Int", "@Int.0"),
            ("@Array<Int>", "@Array<Int>.0", "@Array<Int>", "1"),
            # A refinement of the scrutinee's own base type.
            ("@Int", "@Int.0", "@{ @Int | @Int.0 > 0 }", "1"),
        ],
    )
    def test_related_binding_types_accepted(
        self, param: str, scrutinee: str, binder: str, body: str,
    ) -> None:
        _check_ok(_fn(param, _match(scrutinee, f"    {binder} -> {body}")))


# =====================================================================
# Nesting — the rule applies at every depth
# =====================================================================

class TestNestedPatterns:

    def test_literal_sub_pattern_mismatch(self) -> None:
        """`Some(true)` over `Option<Int>`: the field, not the head."""
        _assert_e314(_fn("@Option<Int>", _match(
            "@Option<Int>.0", "    Some(true) -> 1,\n    None -> 0",
        )))

    def test_constructor_sub_pattern_mismatch(self) -> None:
        _assert_e314(_fn("@Option<Int>", _match(
            "@Option<Int>.0", "    Some(Ok(@Int)) -> 1,\n    None -> 0",
        )))

    def test_nested_pattern_from_spec_accepted(self) -> None:
        """spec §4.9.4's own nested example must stay green."""
        _check_ok(_fn("@Option<Option<Int>>", _match(
            "@Option<Option<Int>>.0",
            "    Some(Some(@Int)) -> @Int.0,\n"
            "    Some(None) -> 1,\n"
            "    None -> 0",
        )))


# =====================================================================
# Shapes that MUST stay green
# =====================================================================

class TestAcceptedShapes:

    def test_option(self) -> None:
        _check_clean(_fn("@Option<Int>", _match(
            "@Option<Int>.0", "    Some(@Int) -> @Int.0,\n    None -> 0",
        )))

    def test_result(self) -> None:
        _check_clean(_fn("@Result<Int, String>", _match(
            "@Result<Int, String>.0",
            "    Ok(@Int) -> @Int.0,\n    Err(@String) -> 0",
        )))

    def test_user_adt(self) -> None:
        _check_clean(COLOR_SHAPE + _fn("@Color", _match(
            "@Color.0", "    Red -> 1,\n    Green -> 2",
        )))

    def test_json(self) -> None:
        _check_clean(_fn("@Json", _match(
            "@Json.0", "    JNull -> 0,\n    _ -> 1",
        )))

    def test_future(self) -> None:
        _check_clean(_fn("@Future<Int>", _match(
            "@Future<Int>.0", "    Future(@Int) -> @Int.0",
        )))

    def test_tuple(self) -> None:
        _check_clean(_fn("@Tuple<Int, Bool>", _match(
            "@Tuple<Int, Bool>.0", "    Tuple(@Int, @Bool) -> @Int.0",
        )))

    def test_alias_of_adt(self) -> None:
        """An alias names the ADT; the constructor arms are still its own."""
        _check_clean(
            "type MaybeInt = Option<Int>;\n\n"
            + _fn("@MaybeInt", _match(
                "@MaybeInt.0", "    Some(@Int) -> @Int.0,\n    None -> 0",
            ))
        )

    def test_refined_scrutinee(self) -> None:
        """A refinement wrapper is stripped before the comparison."""
        _check_clean(_fn("@{ @Int | @Int.0 > 0 }", _match(
            "@Int.0", "    1 -> 10,\n    _ -> 20",
        )))

    def test_generic_option(self) -> None:
        _check_clean(
            "public forall<T> fn probe(@Option<T> -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @Option<T>.0 {\n"
            "    Some(@T) -> 1,\n"
            "    None -> 0\n"
            "  }\n"
            "}\n"
        )

    def test_wildcard_over_everything(self) -> None:
        for param, scrutinee in [
            ("@Int", "@Int.0"),
            ("@Array<Int>", "@Array<Int>.0"),
            ("@Option<Int>", "@Option<Int>.0"),
        ]:
            _check_clean(_fn(param, _match(scrutinee, "    _ -> 1")))


# =====================================================================
# Boundaries and diagnostic quality
# =====================================================================

class TestBoundaries:

    def test_bare_type_variable_scrutinee_is_skipped(self) -> None:
        """`T` can be instantiated at `Option<Int>` — undecidable here.

        Deliberately accepted: the rule refuses only what it can prove
        cannot match, and a generic body knows nothing about `T`.
        """
        _check_ok(
            "public forall<T> fn probe(@T -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @T.0 {\n"
            "    Some(@Int) -> 1,\n"
            "    _ -> 0\n"
            "  }\n"
            "}\n"
        )

    def test_integer_literal_over_a_byte_scrutinee_is_accepted(self) -> None:
        """A `Byte` is an integer 0..255, so an integer literal names one.

        The type rule refuses only what can never match, and a `Byte`
        literal arm can — so this is accepted here AND lowered: the same
        PR fixes the i64-against-an-i32-local comparison that made this
        program compile to a module no host would load ([#1381]).  The
        cell runs the program rather than stopping at `check`, because a
        type rule that accepts what the backend then drops is the very
        shape #1320 is about; `tests/test_codegen_match_literal_arms.py`
        carries the width matrix behind it.
        """
        source = (
            "public fn classify(@Byte -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @Byte.0 {\n"
            "    200 -> 10,\n"
            "    _ -> 20\n"
            "  }\n"
            "}\n"
            "\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  classify(200)\n"
            "}\n"
        )
        _check_clean(source)
        from tests.codegen_helpers import _run
        assert _run(source, "main", []) == 10

    def test_unresolvable_scrutinee_is_skipped(self) -> None:
        """An unresolved call's UnknownType result must not manufacture E314."""
        diags = _check(_fn("@Int", _match(
            "nosuchfn(@Int.0)", "    Some(@Int) -> 1,\n    _ -> 0",
        )))
        assert not _e314(diags), [d.description for d in diags]


class TestDiagnosticShape:

    def test_e314_fields_are_non_vacuous(self) -> None:
        diags = _check(_fn("@Int", _match(
            "@Int.0", "    true -> 100,\n    _ -> 200",
        )))
        hit = _e314(diags)[0]
        assert hit.severity == "error"
        assert hit.rationale and len(hit.rationale) > 30
        assert hit.fix and len(hit.fix) > 30
        assert hit.spec_ref == 'Chapter 4, Section 4.9.1 "Patterns"'
        # The instruction names both sides of the disagreement.
        assert "Bool" in hit.description and "Int" in hit.description

    def test_e314_is_registered(self) -> None:
        from vera.errors import ERROR_CODES
        assert "E314" in ERROR_CODES
        assert ERROR_CODES["E314"]

    def test_location_is_the_pattern_not_the_match(self) -> None:
        """Two bad arms report twice, at their own lines."""
        src = _fn("@Int", _match(
            "@Int.0",
            '    true -> 1,\n    "x" -> 2,\n    _ -> 3',
        ))
        lines = sorted(d.location.line for d in _e314(_check(src)))
        assert len(lines) == 2 and lines[0] != lines[1], lines


# =====================================================================
# Cross-component: check-green must mean compilable
# =====================================================================

class TestCheckGreenMeansCompilable:
    """The invariant the acceptance broke, as a differential.

    Each source below was check-green on the base revision and could not
    be lowered: the first ran to a wrong answer, the second failed WASM
    validation, the third dropped its export.  The rule under test is
    that the checker now refuses exactly these.
    """

    @pytest.mark.parametrize(
        "source",
        [
            _fn("@Unit", _match(
                "map_new()", "    Some(@Int) -> 1,\n    None -> 2")),
            _fn("@Int", _match(
                "@Int.0", "    true -> 100,\n    _ -> 200")),
            "public fn count(@Json -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match json_keys(@Json.0) {\n"
            "    Some(@Array<String>) -> array_length(@Array<String>.0),\n"
            "    None -> 0\n"
            "  }\n"
            "}\n",
        ],
        ids=["ran-wrong", "invalid-wasm", "dropped-export"],
    )
    def test_refused_at_check(self, source: str) -> None:
        assert _errors(source), "expected the checker to refuse this program"
