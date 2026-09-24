"""#1309 — a `type` alias whose name is also a registered ADT name.

Codegen's ``_type_expr_to_wasm_type`` used to consult ``_adt_layouts``
BEFORE the alias table, so ``type Option = Int;`` emitted the slot at the
ADT's i32 pointer width instead of the alias target's i64.  The checker
resolves the other way (``vera/naming.py::_resolve_named`` — type parameter
-> primitive -> alias -> declared ADT), so check and verify were green and
the disagreement surfaced only in the emitted WAT.

Two failure modes were measured at the branch point, and they are NOT the
"same width is silently wrong" story the issue predicted:

* **Loud** where the widths differ AND the target is a scalar (``Int`` /
  ``Nat`` -> i64, ``Float64`` -> f64): the module fails WASM validation at
  load with ``type mismatch: expected i64, found i32``.
* **Silent** where the target is a PAIR type (``String`` / ``Array<T>`` ->
  ``i32_pair``, two words): the ADT branch's single i32 drops the length
  word, the module validates, and the program runs to completion with a
  WRONG VALUE — ``string_concat("ab", "ab")`` returned two junk bytes
  instead of ``"abab"``, and ``array_length`` over a 3-element array
  returned 0.
* **Inert** where the widths coincide (``Bool`` / ``Byte`` / ``Map`` /
  ``Set`` / ``Decimal``, all i32): the emitted WAT is byte-identical to a
  fresh-name control.  Matching widths are not a silent-wrongness case;
  the pair types are.

:class:`TestAliasOverAdtNameWidthBattery` is the differential that makes
width-luck impossible to reintroduce: every name in the LIVE built-in ADT
registry, aliased to every representation class, with the emitted function
signature compared against the identical program under a fresh alias name.
"""
from __future__ import annotations

import pytest

from vera import ast
from vera.codegen import CodeGenerator, execute

from tests.codegen_helpers import _compile, _compile_ok, _run, wat_fn_body


# The control name: not a registered ADT, not a primitive, not a prelude
# alias — so the alias branch is the only branch that can claim it.
_CONTROL = "ZzAliasCtl"


def _builtin_adt_names() -> list[str]:
    """Every built-in ADT name, from the LIVE registry.

    Read off a real ``CodeGenerator`` rather than restated here, so a
    built-in ADT added later joins the battery without anyone remembering
    to widen a list.
    """
    gen = CodeGenerator()
    gen._register_builtin_adts()
    return sorted(gen._adt_layouts)


# (alias target spelling, argument literal, body, declared return type)
# One entry per WASM representation class the target can land in.
_TARGETS: list[tuple[str, str, str, str]] = [
    ("Int", "21", "@{A}.0 + @{A}.0", "@Int"),
    ("Nat", "21", "@{A}.0 + @{A}.0", "@Nat"),
    ("Float64", "1.5", "@{A}.0 + @{A}.0", "@Float64"),
    ("Bool", "true", "if @{A}.0 then {{ 7 }} else {{ 9 }}", "@Int"),
    ("Byte", "3", "byte_to_int(@{A}.0) + byte_to_int(@{A}.0)", "@Int"),
    ("String", '"ab"', "string_concat(@{A}.0, @{A}.0)", "@String"),
    ("Array<Int>", "[5, 6, 7]", "array_length(@{A}.0)", "@Nat"),
    ("Map<String, Int>", "map_new()", "map_size(@{A}.0)", "@Nat"),
    ("Set<Int>", "set_new()", "set_size(@{A}.0)", "@Nat"),
    ("Decimal", "decimal_from_int(3)", "decimal_to_string(@{A}.0)", "@String"),
]


def _program(alias: str, target: str, lit: str, body: str, ret: str) -> str:
    """The same two-function program, parameterised by the alias name."""
    return (
        f"type {alias} = {target};\n\n"
        f"public fn twice(@{alias} -> {ret})\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  {body.format(A=alias)}\n"
        "}\n\n"
        f"public fn main(@Unit -> {ret})\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  twice({lit})\n"
        "}\n"
    )


def _run_value(source: str, fn: str = "main") -> object:
    """Execute and return the raw value (str for String returns, else scalar)."""
    result = _compile_ok(source)
    return execute(result, fn_name=fn).value


class TestAliasOverAdtNameLoud:
    """Scalar targets: the widths differ, so the base failure was at load."""

    def test_int_alias_named_option_runs(self) -> None:
        """The issue's own repro.

        Base: ``Invalid input WebAssembly code at offset 119: type
        mismatch: expected i64, found i32`` from ``vera run``, on a
        check-green / verify-green (4 Tier-1) program.
        """
        source = _program("Option", "Int", "21", "@{A}.0 + @{A}.0", "@Int")
        assert _run(source, fn="main") == 42

    def test_float_alias_named_result_runs(self) -> None:
        source = _program(
            "Result", "Float64", "1.5", "@{A}.0 + @{A}.0", "@Float64")
        assert _run_value(source) == pytest.approx(3.0)


class TestAliasOverAdtNameSilent:
    """Pair targets: the module VALIDATES and computes the wrong answer.

    This is the silent case the issue's "matching widths" prediction
    missed.  An ``i32_pair`` is two words; the ADT branch's single i32
    silently discards the length, and nothing traps.
    """

    def test_string_alias_named_option_keeps_the_bytes(self) -> None:
        """Base: exit 0, returned two junk bytes instead of ``"abab"``."""
        source = _program(
            "Option", "String", '"ab"', "string_concat(@{A}.0, @{A}.0)",
            "@String")
        assert _run_value(source) == "abab"

    def test_array_alias_named_option_keeps_the_length(self) -> None:
        """Base: exit 0, ``array_length`` returned 0 for a 3-element array."""
        source = _program(
            "Option", "Array<Int>", "[5, 6, 7]", "array_length(@{A}.0)",
            "@Nat")
        assert _run(source, fn="main") == 3


class TestAliasOverAdtNameInert:
    """Matching-width targets: green before AND after — a regression guard.

    Green on both sides of the fix proves nothing about the fix; these are
    here so the branch reorder cannot break the cases it must leave alone.
    """

    def test_bool_alias_named_ordering_still_runs(self) -> None:
        source = _program(
            "Ordering", "Bool", "true", "if @{A}.0 then {{ 7 }} else {{ 9 }}",
            "@Int")
        assert _run(source, fn="main") == 7

    def test_map_alias_named_tuple_still_runs(self) -> None:
        source = _program(
            "Tuple", "Map<String, Int>", "map_new()", "map_size(@{A}.0)",
            "@Nat")
        assert _run(source, fn="main") == 0


class TestBuiltinContainerNameShadow:
    """The alias branch must also beat the built-in CONTAINER branches.

    ``Array`` / ``Map`` / ``Set`` / ``Decimal`` / ``Tuple`` are not
    primitives in the checker (``vera.types.PRIMITIVES``), so an alias
    taking one of those names wins there too — and codegen tested them
    before the alias table exactly as it tested ``_adt_layouts``.  Base:
    each of these died with ``expected i64, found i32``.
    """

    @pytest.mark.parametrize(
        "name", ["Array", "Map", "Set", "Decimal", "Tuple", "Future"])
    def test_alias_named_after_a_builtin_container_runs(
        self, name: str,
    ) -> None:
        source = _program(name, "Int", "21", "@{A}.0 + @{A}.0", "@Int")
        assert _run(source, fn="main") == 42

    @pytest.mark.parametrize("name", ["Request", "Response", "UrlParts"])
    def test_alias_named_after_a_prelude_adt_runs(self, name: str) -> None:
        """A prelude-DECLARED ADT's name, shadowed by a main-file alias.

        ``Json`` and ``HtmlNode`` are deliberately absent: their prelude
        COMBINATOR BODIES (``json_get``, ``html_attr``) are emitted into
        every module and render their own ``@Json`` / ``@HtmlNode``
        parameters against the flat ``_type_aliases`` map, which a main-file
        alias of that name pollutes.  That is an alias-ENV SCOPING defect
        (#1316 — spec §8.4.1 makes the namespace module-scoped, so a prelude
        body must render against the prelude's env), not the branch-ORDER
        defect fixed here, and out of #1309's scope.

        It is NOT, however, an unchanged failure, and an earlier draft of
        this docstring said it was.  The reorder moves it: 17 prelude
        ``json_*`` signatures flip from ``(param $p0 i32)`` to ``(param $p0
        i64)``, the loader's complaint reverses from ``expected i64, found
        i32`` to ``expected i32, found i64``, its offset shifts, and
        ``html_attr`` loses one shadow-stack push.  Same root cause, same
        frame in the backtrace, a later point inside it.
        """
        source = _program(name, "Int", "21", "@{A}.0 + @{A}.0", "@Int")
        assert _run(source, fn="main") == 42

    def test_primitive_shadow_runs_at_the_primitive_width(self) -> None:
        """The behavioural half, and the one that can go wrong silently.

        ``type Bool = Int;`` then using ``@Bool`` AS a Bool.  The checker
        refuses the alias (E158, #1497: a primitive's name could never be
        named), so this drives a compile that skips the checker, and code
        generation must still resolve the primitive first: the primitive
        branch wins, so the slot stays i32.  Hoist the alias branch above
        the primitives and ``@Bool`` becomes i64 — which is why the unit
        assertions below are not the whole story.  The check-time refusal
        does not make this test redundant: code generation is reachable
        without the checker, and its width must not depend on it.
        """
        source = """\
type Bool = Int;

private fn f(@Bool -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  if @Bool.0 then { 1 } else { 2 }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{
  f(true)
}
"""
        assert _run(source, fn="main") == 1

    @pytest.mark.parametrize("name", ["Int", "Nat", "Bool", "Float64",
                                      "String", "Byte", "Unit"])
    def test_primitive_still_beats_a_same_named_alias(self, name: str) -> None:
        """The one branch that must NOT move: a primitive shadows the alias.

        ``_resolve_named`` tests ``PRIMITIVES`` before the alias table, so
        ``type Bool = Int;`` leaves ``@Bool`` a Bool.  Asked of the
        derivation directly because that is the only way to cover all seven
        primitives — two of the spellings are refused by the checker
        (``@Bool.0 + @Bool.0`` is E140, ``type Int = Int;`` is E132) — with
        the run-level program above carrying the behavioural half.
        """
        gen = CodeGenerator()
        gen._register_builtin_adts()
        gen._type_aliases[name] = ast.NamedType(name="Int", type_args=None)
        gen._sync_alias_env()
        expected = {
            "Int": "i64", "Nat": "i64", "Bool": "i32", "Float64": "f64",
            "String": "i32_pair", "Byte": "i32", "Unit": None,
        }[name]
        assert gen._type_expr_to_wasm_type(
            ast.NamedType(name=name, type_args=None)) == expected


class TestReturnTypeIsStringBranchOrder:
    """The THIRD consumer of the same pre-alias-branch disease (CR #1323).

    ``_return_type_is_string`` decides whether ``execute()`` decodes a
    function's (ptr, len) return as UTF-8 for display, and it tested the
    ``Future<T>`` strip before the alias table — where ``Future`` is an ADT
    name, not one of ``vera.types.PRIMITIVES``, so the checker resolves an
    alias of that name first.  Under ``type Future<T> = Array<T>;`` a
    ``@Future<String>`` return therefore took the transparent-wrapper strip,
    recursed onto ``String``, and was classified a string return — while the
    width derivation (fixed for #1309) resolves the alias and lowers it as
    an ``Array<String>``.  ``vera run`` decoded the array's backing bytes as
    text and printed two NULs where the fresh-name control printed the
    pointer.  Expressible, and measured identically at the branch point, so
    it is pre-existing rather than introduced by the #1309 reorder.

    ``String`` stays ahead of the alias branch because it IS a primitive —
    the same single exception the width derivation keeps.
    """

    _ALIASED = """\
type Future<T> = Array<T>;

public fn main(@Unit -> @Future<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  ["ab", "cd"]
}
"""

    _CONTROL = _ALIASED.replace("Future", "Zz")

    def test_a_future_named_alias_to_array_is_not_a_string_return(self) -> None:
        assert "main" not in _compile_ok(self._ALIASED).fn_string_returns

    def test_the_fresh_name_control_agrees(self) -> None:
        """The differential: the same program under a name that is not an
        ADT's was always classified correctly, so the alias TARGET is not
        what decides this — the name is."""
        assert "main" not in _compile_ok(self._CONTROL).fn_string_returns

    def test_a_future_named_alias_to_string_is_still_a_string_return(self) -> None:
        """Over-correction control: resolving the alias must not lose a
        genuine string return that reaches one THROUGH the shadowed name."""
        source = """\
type Future<T> = Array<T>;

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  "hi"
}
"""
        assert "main" in _compile_ok(source).fn_string_returns

    def test_the_genuine_transparent_future_still_decodes(self) -> None:
        """The #841 / #1047 behaviour the Future branch exists for, with no
        alias shadowing the name — it must survive the reorder."""
        source = """\
public fn mk(@Unit -> @Future<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  async("hi")
}
"""
        assert "mk" in _compile_ok(source).fn_string_returns

    def test_an_alias_to_a_transparent_future_still_decodes(self) -> None:
        """PR #1041's shape: the alias branch must keep substituting its own
        parameters, which is what it was moved above, not past."""
        source = """\
type Deferred<T> = Future<T>;

public fn mk(@Unit -> @Deferred<String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  async("hi")
}
"""
        assert "mk" in _compile_ok(source).fn_string_returns


class TestAliasOverAdtNameWidthBattery:
    """The differential: EVERY built-in ADT name x EVERY representation.

    For each pair, compile the alias-named program and the identical
    program under a fresh alias name, and compare the emitted ``$twice``
    body in full — the parameter, local and result widths of the header,
    and the instructions under it.  The whole body, not the header alone:
    a header-only comparison reads the parameter and result widths but
    not the ``(local …)`` declarations, and the module docstring's
    "byte-identical to a fresh-name control" is a claim about the body
    (measured: identical in every cell of the battery).  A single width
    that resolves through the ADT branch instead of the alias branch shows
    up here regardless of whether it happens to trap, so the loud cases
    cannot be the only ones anyone notices.
    """

    @pytest.mark.parametrize("adt", _builtin_adt_names())
    @pytest.mark.parametrize(
        "target,lit,body,ret", _TARGETS,
        ids=[t[0] for t in _TARGETS],
    )
    def test_emitted_widths_match_the_fresh_name_control(
        self, adt: str, target: str, lit: str, body: str, ret: str,
    ) -> None:
        aliased = _compile(_program(adt, target, lit, body, ret))
        control = _compile(_program(_CONTROL, target, lit, body, ret))

        control_errors = [
            d for d in control.diagnostics if d.severity == "error"]
        assert not control_errors, (
            f"control program for {target} is itself broken: {control_errors}")

        aliased_errors = [
            d for d in aliased.diagnostics if d.severity == "error"]
        assert not aliased_errors, (
            f"type {adt} = {target}; failed to assemble: {aliased_errors}")

        want = wat_fn_body(control.wat, "twice")
        got = wat_fn_body(aliased.wat, "twice")
        assert got == want, (
            f"type {adt} = {target}; emitted {got!r}, "
            f"but the same program under a fresh alias name emitted {want!r}"
        )

    @pytest.mark.parametrize("adt", _builtin_adt_names())
    def test_derivation_follows_the_alias_not_the_adt(self, adt: str) -> None:
        """The branch order itself, at the one function that decides it.

        The unit dual of the WAT differential above: under ``type <Adt> =
        Int;`` the derivation must answer ``i64``.  ``i32`` is the ADT
        pointer width — the bug.
        """
        gen = CodeGenerator()
        gen._register_builtin_adts()
        gen._type_aliases[adt] = ast.NamedType(name="Int", type_args=None)
        gen._sync_alias_env()
        assert gen._type_expr_to_wasm_type(
            ast.NamedType(name=adt, type_args=None)) == "i64"

    @pytest.mark.parametrize("adt", _builtin_adt_names())
    def test_unaliased_adt_name_is_still_a_pointer(self, adt: str) -> None:
        """The complement: with no alias in scope the ADT branch still wins.

        Without this, "make the alias branch win" could be satisfied by a
        change that broke every ordinary ADT parameter.
        """
        gen = CodeGenerator()
        gen._register_builtin_adts()
        gen._sync_alias_env()
        assert gen._type_expr_to_wasm_type(
            ast.NamedType(name=adt, type_args=None)) == "i32"
