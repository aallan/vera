"""A literal match arm compares at the SCRUTINEE's representation.

``_translate_match_condition`` re-derived the comparison from the
pattern's own form against a hand-maintained arm list, instead of
consulting what ``_translate_match`` had already worked out — the
scrutinee's WAT representation, which it passes in as ``scr_wasm_type``
and which the literal arms ignored.  Two defects fall out of that one
omission, both measured on ``origin/release/v0.2.0`` (6dc41d40):

* an integer literal arm emitted ``i64.const`` / ``i64.eq``
  unconditionally, so a ``Byte`` scrutinee (an i32) produced a module
  no host will load — and produced it SILENTLY: ``vera check`` OK,
  ``vera verify`` "4 verified (Tier 1)", ``vera compile`` exit 0
  reporting "2 functions exported", and then wasmtime refusing the
  bytes with ``type mismatch: expected i64, found i32``;
* there was no ``StringPattern`` arm at all.  The grammar has one
  (``grammar.lark``), the checker, the formatter and the SMT layer all
  handle it, and spec §4.9.1 lists ``"hi"`` as a pattern form — but
  codegen fell through to the pair guard, which refused every
  non-wildcard pattern over a ``(ptr, len)`` scrutinee, so
  ``match @String.0 { "yes" -> 1, _ -> 3 }`` was check-green and lost
  its export to an E602 skip.

The fix is one literal-comparison emitter keyed by that representation
(i32 for ``Byte``/``Bool``, i64 for ``Int``/``Nat``, the pair for
``String`` through the same ``$eq_String`` helper ``==`` already uses),
and a dispatch that is exhaustive over the pattern forms the grammar
has, so a form nobody wrote an arm for is refused loudly instead of
falling through to whatever the last branch happened to be.

The values are chosen so that no cell can pass by coincidence: every
integer scrutinee matches against **200**, which is representable in
both widths, so an i64 compare against an i32 scrutinee cannot agree by
being small; the arms return 11 / 22 / 33, none of which is a literal
being matched, a default, or a length; and each type is exercised three
ways — the first literal, the SECOND literal (an always-take-the-first
bug survives the first cell), and a value matching neither (an
always-true comparison survives both of the others).
"""
from __future__ import annotations

import pytest

from tests.checker_helpers import _errors
from tests.codegen_helpers import _compile, _run


def _classify(param: str, arms: str, call: str) -> str:
    """A `classify` over *param* plus a `main` that calls it."""
    return (
        f"public fn classify({param} -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  match {param}.0 {{\n{arms}\n  }}\n"
        "}\n"
        "\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  classify({call})\n"
        "}\n"
    )


def _fresh_context():
    """A bare `WasmContext`, for asking the emitter a question directly.

    The dispatch's exhaustiveness cannot be driven from source — the
    grammar has no form it is missing — so the one cell that pins it
    calls the method with a synthetic pattern node.
    """
    from vera.wasm.context import WasmContext
    from vera.wasm.helpers import StringPool

    return WasmContext(StringPool())


INT_ARMS = "    200 -> 11,\n    100 -> 22,\n    _ -> 33"
BOOL_ARMS = "    true -> 11,\n    false -> 22"
STRING_ARMS = '    "yes" -> 11,\n    "no" -> 22,\n    _ -> 33'


# =====================================================================
# The matrix: representation × which arm should be taken
# =====================================================================

class TestLiteralArmsRunAtEveryWidth:

    @pytest.mark.parametrize(
        ("label", "param", "arms", "call", "expected"),
        [
            # i32 integer scrutinee — the width the i64-only compare broke.
            ("byte-first", "@Byte", INT_ARMS, "200", 11),
            ("byte-second", "@Byte", INT_ARMS, "100", 22),
            ("byte-neither", "@Byte", INT_ARMS, "7", 33),
            # i64 integer scrutinees — the same literals, so a cell cannot
            # pass by the value happening to fit one width.
            ("int-first", "@Int", INT_ARMS, "200", 11),
            ("int-second", "@Int", INT_ARMS, "100", 22),
            ("int-neither", "@Int", INT_ARMS, "7", 33),
            ("nat-first", "@Nat", INT_ARMS, "200", 11),
            ("nat-second", "@Nat", INT_ARMS, "100", 22),
            ("nat-neither", "@Nat", INT_ARMS, "7", 33),
            # i32 Bool.
            ("bool-true", "@Bool", BOOL_ARMS, "true", 11),
            ("bool-false", "@Bool", BOOL_ARMS, "false", 22),
            # (ptr, len) String — no arm existed at all.
            ("string-first", "@String", STRING_ARMS, '"yes"', 11),
            ("string-second", "@String", STRING_ARMS, '"no"', 22),
            ("string-neither", "@String", STRING_ARMS, '"maybe"', 33),
        ],
    )
    def test_arm_selection(
        self, label: str, param: str, arms: str, call: str, expected: int,
    ) -> None:
        source = _classify(param, arms, call)
        assert _errors(source) == [], [d.description for d in _errors(source)]
        assert _run(source, "main", []) == expected

    def test_a_float_scrutinee_needs_no_literal_arm(self) -> None:
        """`Float64` has no literal pattern form in the grammar.

        The wildcard is the only arm it can take, and an integer literal
        over one is refused at check (E314), so the emitter needs no f64
        comparison and does not carry a branch nothing can reach.
        """
        wildcard_only = _classify("@Float64", "    _ -> 33", "1.5")
        assert _errors(wildcard_only) == []
        assert _run(wildcard_only, "main", []) == 33

        with_int_literal = _classify(
            "@Float64", "    200 -> 11,\n    _ -> 33", "1.5",
        )
        assert any(
            d.error_code == "E314" for d in _errors(with_int_literal)
        ), [d.description for d in _errors(with_int_literal)]


# =====================================================================
# The emitted comparison, not just its answer
# =====================================================================

class TestComparisonWidthInTheWat:
    """A value assertion alone cannot say WHICH compare ran.

    `200` is equal to `200` at either width once the module loads, so a
    run that returns 11 is consistent with an i64 compare over a
    zero-extended i32 as well as with the right one.  These read the
    instruction stream.
    """

    def _wat(self, param: str, arms: str, call: str) -> str:
        result = _compile(_classify(param, arms, call))
        errors = [d for d in result.diagnostics if d.severity == "error"]
        assert not errors, [d.description for d in errors]
        return result.wat

    def test_byte_compares_at_i32(self) -> None:
        wat = self._wat("@Byte", INT_ARMS, "200")
        assert "i32.const 200" in wat and "i32.eq" in wat, wat[:400]
        assert "i64.const 200" not in wat

    def test_int_compares_at_i64(self) -> None:
        wat = self._wat("@Int", INT_ARMS, "200")
        assert "i64.const 200" in wat and "i64.eq" in wat, wat[:400]

    def test_nat_compares_at_i64(self) -> None:
        wat = self._wat("@Nat", INT_ARMS, "200")
        assert "i64.const 200" in wat and "i64.eq" in wat, wat[:400]

    def test_string_compares_through_the_shared_helper(self) -> None:
        """The same `$eq_String` content comparison `==` uses.

        One place knows how a String is compared; a second byte-loop
        written for match arms could drift from it.
        """
        wat = self._wat("@String", STRING_ARMS, '"yes"')
        assert "call $eq_String" in wat
        assert wat.count("$eq_String") >= 2  # the helper and its call(s)


# =====================================================================
# The two repros, verbatim
# =====================================================================

class TestIssueRepros:

    def test_string_pattern_program_keeps_its_exports(self) -> None:
        """Base: `[E602] ... unsupported StringPattern`, exports (none)."""
        source = (
            "public fn classify(@String -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @String.0 {\n"
            '    "yes" -> 1,\n'
            '    "no" -> 2,\n'
            "    _ -> 3\n"
            "  }\n"
            "}\n"
            "\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            '  classify("no")\n'
            "}\n"
        )
        result = _compile(source)
        assert not [d for d in result.diagnostics if d.severity == "error"]
        assert "classify" in result.exports and "main" in result.exports
        assert result.dropped_fns == {}
        assert _run(source, "main", []) == 2

    def test_byte_literal_program_loads(self) -> None:
        """Base: compile exit 0, then `expected i64, found i32` at load."""
        source = (
            "public fn classify(@Byte -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  match @Byte.0 {\n"
            "    1 -> 10,\n"
            "    _ -> 20\n"
            "  }\n"
            "}\n"
            "\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  classify(1)\n"
            "}\n"
        )
        assert _run(source, "main", []) == 10


# =====================================================================
# The dispatch is exhaustive, and says so when it is not
# =====================================================================

class TestUnknownPatternFormIsLoud:
    """A form nobody wrote an arm for must not become "unconditional".

    This is the property the two defects came from: the integer arm
    answered for a `Byte` because it was the branch nothing stopped, and
    a string arm did not exist at all.  Restoring a bare fall-through
    leaves every OTHER cell in this file green — measured — so the
    exhaustiveness has to be asserted directly, on a form the grammar
    cannot produce today but a future one might.
    """

    def test_a_form_with_no_arm_raises(self) -> None:
        from dataclasses import dataclass

        from vera import ast
        from vera.skip import CodegenSkip

        @dataclass(frozen=True)
        class FuturePattern(ast.Pattern):
            """A pattern form this dispatch has never been taught."""

        ctx = _fresh_context()
        with pytest.raises(CodegenSkip) as excinfo:
            ctx._translate_match_condition(
                FuturePattern(), 0, "i64", "Int",
            )
        assert "FuturePattern" in str(excinfo.value)

    def test_a_bool_literal_over_a_byte_is_refused_by_the_emitter(
        self,
    ) -> None:
        """Width alone cannot separate `Bool` from `Byte` — both are i32.

        E314 refuses this program, but the checker is not the emitter's
        only caller (`vera.codegen.compile()` is reachable directly, as
        these helpers do), so the emitter enforces the type rule it
        relies on instead of assuming it: without the base-type check a
        `true ->` arm over a `Byte` lowers to a truthiness read, and
        byte 200 takes the `true` arm.
        """
        from vera import ast
        from vera.skip import CodegenSkip

        ctx = _fresh_context()
        with pytest.raises(CodegenSkip) as excinfo:
            ctx._translate_match_condition(
                ast.BoolPattern(value=True), 0, "i32", "Byte",
            )
        assert "Byte" in str(excinfo.value)

    def test_an_int_literal_over_a_bool_is_refused_by_the_emitter(
        self,
    ) -> None:
        from vera import ast
        from vera.skip import CodegenSkip

        ctx = _fresh_context()
        with pytest.raises(CodegenSkip) as excinfo:
            ctx._translate_match_condition(
                ast.IntPattern(value=1), 0, "i32", "Bool",
            )
        assert "Bool" in str(excinfo.value)

    def test_the_admitted_pairs_still_lower(self) -> None:
        """The other direction: every pair the checker admits still emits."""
        from vera import ast

        ctx = _fresh_context()
        for pattern, wt, vera_type in (
            (ast.BoolPattern(value=True), "i32", "Bool"),
            (ast.IntPattern(value=200), "i32", "Byte"),
            (ast.IntPattern(value=200), "i64", "Int"),
            (ast.IntPattern(value=200), "i64", "Nat"),
        ):
            assert ctx._translate_match_condition(
                pattern, 0, wt, vera_type,
            ) is not None

    def test_wildcard_and_binding_stay_unconditional(self) -> None:
        """The control: the two forms that SHOULD answer None still do."""
        from vera import ast

        ctx = _fresh_context()
        assert ctx._translate_match_condition(
            ast.WildcardPattern(), 0, "i64", "Int",
        ) is None
        assert ctx._translate_match_condition(
            ast.BindingPattern(
                type_expr=ast.NamedType(name="Int", type_args=None),
            ), 0, "i64", "Int",
        ) is None


# =====================================================================
# What the pair guard still refuses
# =====================================================================

class TestPairScrutineeGuard:
    """Lowering a String comparison must not widen to every pair.

    An `Array<T>` has the same (ptr, len) representation and none of the
    semantics: comparing one to an interned literal would read the
    element buffer as UTF-8.  The checker refuses that program (E314),
    and codegen refuses it independently — the guard is not allowed to
    become "this is a pair, therefore it is a String".
    """

    def test_string_literal_over_an_array_is_refused_by_both(self) -> None:
        source = _classify(
            "@Array<Int>", '    "yes" -> 11,\n    _ -> 33', "array_range(0, 3)",
        )
        assert any(d.error_code == "E314" for d in _errors(source))
        result = _compile(source)
        assert "classify" not in result.exports or result.dropped_fns

    def test_constructor_pattern_over_a_pair_is_still_refused(self) -> None:
        source = _classify(
            "@String", "    Some(@Int) -> 11,\n    _ -> 33", '"x"',
        )
        assert any(d.error_code == "E314" for d in _errors(source))
        result = _compile(source)
        assert "classify" not in result.exports or result.dropped_fns
