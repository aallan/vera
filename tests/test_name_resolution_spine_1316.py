"""#1316 / #1321 / #1331 — ONE name-resolution spine, asked in the DECLARING
namespace.

Three issues, one root.  Every derivation that turns a type NAME into a
representation used to re-implement the checker's branch order by hand,
against whatever alias and ADT tables happened to be installed:

* **#1321 / #1331 — the ORDER.**  Codegen's ``_type_expr_to_wasm_type``, the
  WASM layer's ``_canonical_wasm_type`` / ``_slot_name_to_wasm_type`` /
  ``_ref_type_name_wasm_type`` and the ``_is_pair_type_name`` predicate all
  tested the built-in container names (``Array`` / ``Map`` / ``Set`` /
  ``Decimal`` / ``Future``) BEFORE the declared-ADT lookup, while
  ``naming._resolve_named`` documents the declared ADT ahead of them.  §8.4.1
  lets a declaration take a name a container already uses, so ``private data
  Array { MkArr(Int) }`` was measured as the container's ``i32_pair``: the
  match over it was refused as a pair scrutinee with a located ``[E602]``
  naming ``String`` / ``Array<T>``, its callers dropped behind ``[E620]``, and
  ``vera run`` reported ``Available exports: (none)`` on a check-green,
  verify-green program where a fresh-name control printed 7.  ``Map``, ``Set``
  and ``Decimal`` were inert by width-luck (their branch answers ``i32``,
  which is what the ADT branch would have answered), which is the same
  coincidence that hid most of #1309.

* **#1316 — the ENVIRONMENT.**  ``_type_aliases`` is one flat map, and a
  PRELUDE combinator's body was rendered against whatever it held — the entry
  file's.  Under ``type Json = Int;`` the prelude's own ``json_get`` took the
  alias's i64 where its body wanted the ADT's i32 pointer and the module died
  at load (``type mismatch: expected i32, found i64`` inside
  ``wasm[0]::function[…]::json_get``), again on a check-green, verify-green
  program.  ``type HtmlNode = Int;`` was the same failure in ``html_attr``.

The fix is one spine and one scope.  :func:`vera.naming.classify_named` now
owns the branch ORDER — type parameter -> primitive -> alias -> declared ADT
-> built-in — and ``naming._resolve_named`` is its semantic arm, so the
checker's resolution and codegen's width derivation cannot hold different
orders.  The prelude is a namespace like any other
(:data:`vera.prelude.PRELUDE_NAMESPACE`): its declarations register, its
bodies compile, and its clones are emitted inside
``_module_alias_scope(PRELUDE_NAMESPACE)``, so an entry-file alias or ``data``
declaration reaches the entry file's bodies and nothing else.

Structure of this file, and why each part is here:

* :class:`TestClassifyNamedIsTheOrder` — the spine's own precedence, on an env
  where ONE name is simultaneously a type parameter, a primitive, an alias and
  a declared ADT, so each assertion can only pass by taking the right branch.
* :class:`TestResolveNamedIsDrivenByTheSpine` — the semantic arm agrees with
  the classification for every sort.  Without this the spine could drift into
  a second opinion that only codegen reads.
* :class:`TestDeclaredAdtBeatsTheBuiltinName` — #1321/#1331 end to end, over
  EVERY built-in ADT and container name from the live registry, with a
  byte-identical WAT differential against a fresh-name control.  Shape-varied
  on the axis the fix turns on: the name.
* :class:`TestPreludeNamespaceScope` — #1316 end to end for all 16 names, plus
  the positional assertion that a prelude body is compiled in the prelude's
  namespace and the entry's ``data`` declarations are not members of it.
* :class:`TestCrossDerivationDifferential` — the invariant that keeps the
  family closed: every derivation asked the same name in the same scope
  returns the same answer.  A unit test on any one of them would have stayed
  green while the other three disagreed, which is exactly how #1331 survived
  a two-site fix.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from vera import ast, naming
from vera.checker.registration import RegistrationMixin
from vera.codegen import CodeGenerator, execute
from vera.codegen.api import CompileResult
from vera.naming import AliasEnv, NameSort, classify_named
from vera.parser import parse_to_ast
from vera.prelude import PRELUDE_NAMESPACE, prelude_adt_names
from vera.types import PRIMITIVES
from vera.wasm import WasmContext

from tests.codegen_helpers import (
    _compile,
    _compile_ok,
    _compile_with_generator,
    _run,
    wat_fn_body,
)


def _check(source: str) -> list[object]:
    """The CHECK-phase diagnostics for *source*.

    `_compile` runs code generation, which never sees a program the checker
    refuses — so a check-phase rail has to be asked at the check phase.
    """
    from tests.checker_helpers import _errors

    return list(_errors(source))


def _nt(name: str, args: tuple[ast.TypeExpr, ...] | None = None) -> ast.NamedType:
    return ast.NamedType(name=name, type_args=args)


def _probe_context(gen: CodeGenerator) -> WasmContext:
    """A ``WasmContext`` carrying exactly what *gen* would hand a body.

    The two fields the spine reads on the wasm side, built the way
    ``_compile_fn`` builds them — the namespace-scoped ADT name set and the
    ``AliasEnv`` it is derived from — so a probe asks the derivations the
    same question a real emission does.
    """
    ctx = WasmContext(
        gen.string_pool,
        adt_type_names=set(gen._alias_env.data_types),
    )
    ctx.set_alias_env(gen._alias_env)
    return ctx


# =====================================================================
# The spine
# =====================================================================


class TestRegistryCoverage:
    """The batteries and the width table are held against the LIVE registries.

    Both directions of the same failure: a battery that names fewer types
    than exist tests fewer shadows than a program can write (PR #1372 review
    found it omitting the four the prelude injects — precisely #1316's own
    repro), and a width table with fewer entries than ``PRIMITIVES`` sends a
    primitive down a path that has no answer for it.
    """

    def test_the_width_table_covers_every_primitive(self) -> None:
        """`classify_named` answers PRIMITIVE for every bare key of
        ``vera.types.PRIMITIVES``, and `_type_expr_to_wasm_type` then reads
        its width from `_PRIMITIVE_WASM_TYPES` — so the two key sets must be
        equal, or a primitive reaches codegen with no width stated.

        The lookup is guarded (an unknown primitive is ``"unsupported"``,
        which the existing E605 refusal reports), so the gap is loud rather
        than a `KeyError`; this is what stops it being introduced at all.
        """
        from vera.codegen.core import _PRIMITIVE_WASM_TYPES

        assert set(_PRIMITIVE_WASM_TYPES) == set(PRIMITIVES), (
            f"missing: {sorted(set(PRIMITIVES) - set(_PRIMITIVE_WASM_TYPES))}; "
            f"extra: {sorted(set(_PRIMITIVE_WASM_TYPES) - set(PRIMITIVES))}"
        )

    def test_the_battery_names_every_declared_type_a_program_can_shadow(
        self,
    ) -> None:
        """`_builtin_type_names()` must be the union of every registry a
        ``data`` or ``type`` declaration could take a name from.

        Read off the live registries in the helper, and asserted here against
        them independently, so neither a new built-in ADT nor a new prelude
        data type can join the language without joining the battery.  No
        assertion on the POPULATION SIZE: the parametrisation is derived, so
        a legitimate registry addition joins the battery by itself and a
        pinned count would only fail the suite for it (PR #1372 review).  The
        four named below carry the drift signal instead, being the ones a
        registry-shaped union can silently lose.
        There are no exclusions: the first draft carried one for ``Tuple``
        and it did not survive measurement.
        """
        gen = CodeGenerator()
        gen._register_builtin_adts()
        expected = (
            set(gen._adt_layouts)
            | set(prelude_adt_names())
            | {"Array", "Map", "Set", "Decimal", "Future"}
        )
        assert set(_builtin_type_names()) == expected
        # The four the Pass-0.5 snapshot is taken too early to see, named
        # positively: a union that silently lost them would still satisfy the
        # equality above if the helper and this test drifted together.
        assert {"Json", "HtmlNode", "Request", "Response"} <= set(
            _builtin_type_names())


class TestClassifyNamedIsTheOrder:
    """Precedence, on an env where one name could take four branches.

    Every case below uses the SAME name in the same env, changing only what
    the env says about it, so a passing assertion cannot be explained by the
    name being absent from the losing table.
    """

    def _env(self, **kw: object) -> AliasEnv:
        base: dict[str, object] = {
            "aliases": {"Int": _nt("Bool"), "Shp": _nt("Int")},
            "alias_params": {"Int": None, "Shp": None},
            "data_types": {"Int": 0, "Shp": 0, "Array": 0},
        }
        base.update(kw)
        return AliasEnv(**base)  # type: ignore[arg-type]

    def test_type_param_shadows_everything(self) -> None:
        env = naming.with_type_params(self._env(), ["Int"])
        assert classify_named(_nt("Int"), env) is NameSort.TYPE_PARAM

    def test_primitive_beats_an_alias_and_an_adt_of_its_name(self) -> None:
        """``Int`` is an alias AND a declared ADT in this env, and still
        classifies as the primitive — the checker's second branch."""
        assert classify_named(_nt("Int"), self._env()) is NameSort.PRIMITIVE

    def test_alias_beats_a_declared_adt_of_its_name(self) -> None:
        """``Shp`` is both; the alias branch is third and the ADT fourth."""
        assert classify_named(_nt("Shp"), self._env()) is NameSort.ALIAS

    def test_declared_adt_beats_the_builtin_container_name(self) -> None:
        """#1321's whole question, at the spine.  ``Array`` names a built-in
        container and a declaration here; the declaration wins."""
        assert (
            classify_named(_nt("Array"), self._env()) is NameSort.DECLARED_ADT
        )

    def test_an_undeclared_container_name_is_builtin(self) -> None:
        env = self._env(data_types={"Shp": 0})
        assert classify_named(_nt("Array"), env) is NameSort.BUILTIN
        assert classify_named(_nt("Map"), env) is NameSort.BUILTIN
        assert classify_named(_nt("Decimal"), env) is NameSort.BUILTIN

    def test_arity_mismatch_is_its_own_sort(self) -> None:
        env = AliasEnv(
            aliases={"Box": _nt("Array", (_nt("T"),))},
            alias_params={"Box": ("T",)},
        )
        assert classify_named(_nt("Box", (_nt("Int"),)), env) is NameSort.ALIAS
        assert (
            classify_named(_nt("Box"), env) is NameSort.ALIAS_ARITY_MISMATCH
        )

    def test_a_parameterised_primitive_spelling_is_not_the_primitive(
        self,
    ) -> None:
        """``PRIMITIVES`` only claims the BARE spelling — ``Int<Bool>`` is
        not ``Int``, and the checker falls through for it."""
        assert (
            classify_named(_nt("Int", (_nt("Bool"),)), AliasEnv({}, {}))
            is NameSort.BUILTIN
        )

    def test_the_declaration_index_bound_applies_to_both_registries(
        self,
    ) -> None:
        """An alias body sees only what was declared BEFORE it (#1208), and
        the bound orders the alias and ADT registries against each other."""
        env = AliasEnv(
            aliases={"A": _nt("Int")}, alias_params={"A": None},
            data_types={"Decimal": 5}, _order={"A": 3},
        )
        assert classify_named(_nt("A"), env, limit=9) is NameSort.ALIAS
        assert classify_named(_nt("A"), env, limit=2) is NameSort.BUILTIN
        assert (
            classify_named(_nt("Decimal"), env, limit=9)
            is NameSort.DECLARED_ADT
        )
        assert classify_named(_nt("Decimal"), env, limit=4) is NameSort.BUILTIN

    def test_an_order_entry_with_no_body_falls_through(self) -> None:
        """The branch stays TOTAL for an env assembled elsewhere."""
        env = AliasEnv(
            aliases={}, alias_params={}, data_types={"Zz": 1}, _order={"Zz": 0},
        )
        assert classify_named(_nt("Zz"), env) is NameSort.DECLARED_ADT

    def test_alias_body_substitutes_the_supplied_arguments(self) -> None:
        env = AliasEnv(
            aliases={"Box": _nt("Array", (_nt("T"),))},
            alias_params={"Box": ("T",)},
        )
        body = naming.alias_body(_nt("Box", (_nt("Int"),)), env)
        assert isinstance(body, ast.NamedType)
        assert body.name == "Array"
        assert body.type_args is not None
        assert isinstance(body.type_args[0], ast.NamedType)
        assert body.type_args[0].name == "Int"


class TestResolveNamedIsDrivenByTheSpine:
    """The semantic arm takes the branch the spine names, for every sort.

    ``resolve_type_expr`` is the checker's rendering; ``classify_named`` is
    what codegen asks.  If they could disagree, the split would reintroduce
    the very divergence the spine exists to close — so the agreement is
    asserted directly rather than left to the reading.
    """

    @pytest.mark.parametrize("name", sorted(PRIMITIVES))
    def test_every_primitive_resolves_to_its_primitive(self, name: str) -> None:
        env = AliasEnv(
            aliases={name: _nt("Bool")}, alias_params={name: None},
            data_types={name: 0},
        )
        assert classify_named(_nt(name), env) is NameSort.PRIMITIVE
        assert naming.resolve_type_expr(_nt(name), env) is PRIMITIVES[name]

    def test_alias_sort_resolves_through_the_alias(self) -> None:
        env = AliasEnv(
            aliases={"Shp": _nt("Int")}, alias_params={"Shp": None},
            data_types={"Shp": 0},
        )
        assert classify_named(_nt("Shp"), env) is NameSort.ALIAS
        assert naming.resolve_type_expr(_nt("Shp"), env) is PRIMITIVES["Int"]

    def test_arity_mismatch_resolves_to_unknown(self) -> None:
        env = AliasEnv(
            aliases={"Box": _nt("Int")}, alias_params={"Box": ("T",)},
        )
        assert (
            classify_named(_nt("Box"), env) is NameSort.ALIAS_ARITY_MISMATCH
        )
        assert naming.resolve_type_expr(_nt("Box"), env).__class__.__name__ == (
            "UnknownType"
        )

    def test_declared_adt_sort_keeps_its_type_arguments(self) -> None:
        """A user ``Decimal`` keeps its arguments where the built-in branch
        drops them — the divergence the ADT branch's POSITION protects."""
        env = AliasEnv(aliases={}, alias_params={}, data_types={"Decimal": 0})
        assert (
            classify_named(_nt("Decimal"), env) is NameSort.DECLARED_ADT
        )
        ty = naming.resolve_type_expr(_nt("Decimal", (_nt("Int"),)), env)
        assert getattr(ty, "type_args", ()) != ()

    def test_builtin_decimal_drops_its_type_arguments(self) -> None:
        env = AliasEnv(aliases={}, alias_params={})
        assert classify_named(_nt("Decimal"), env) is NameSort.BUILTIN
        ty = naming.resolve_type_expr(_nt("Decimal", (_nt("Int"),)), env)
        assert getattr(ty, "type_args", None) == ()

    def test_removed_alias_stays_unknown_only_while_undeclared(self) -> None:
        bare = AliasEnv(aliases={}, alias_params={})
        assert naming.resolve_type_expr(
            _nt("Float"), bare).__class__.__name__ == "UnknownType"
        declared = AliasEnv(aliases={}, alias_params={}, data_types={"Float": 0})
        assert classify_named(_nt("Float"), declared) is NameSort.DECLARED_ADT
        assert naming.resolve_type_expr(
            _nt("Float"), declared).__class__.__name__ == "AdtType"


# =====================================================================
# #1321 / #1331 — a declaration beats the built-in reading of its name
# =====================================================================


#: The names a `data` declaration may not take (#1397, E158), read from the
#: COMPILER's own reservation rather than restated here: the compiler
#: special-cases their SEMANTICS by name, so a declaration of one cannot be
#: told apart from the built-in.  They stay in the ALIAS battery —
#: `type Tuple = Int;` is still legal and still has to resolve correctly.
#:
#: Imported, not copied, so the two halves of this file's partition —
#: refused here, fully working there — cannot drift apart from what the
#: checker actually refuses.  A second hand list is a second place to
#: forget.
_UNDECLARABLE = tuple(RegistrationMixin._SPECIAL_CASED_BUILTIN_ADTS)

#: The reservation #1397 makes, written out.  Every cell that asserts a
#: REFUSAL is parametrized over this rather than over `_UNDECLARABLE`, so
#: running these files against a compiler that does not reserve a name
#: cannot make the cell for that name silently disappear: a derived
#: parametrize collapses to whatever the tree under test happens to reserve,
#: which at `release/v0.2.0` is `Future` alone — so the name this issue is
#: about would drop out and the cell would pass on both sides (PR #1404
#: review, finding 6).  `test_the_compiler_reserves_exactly_these` holds the
#: two against each other, so the pair cannot drift.
_EXPECTED_RESERVED = ("Future", "Tuple")


def _declarable_type_names() -> list[str]:
    """:func:`_builtin_type_names` minus the names E158 now refuses."""
    return [n for n in _builtin_type_names() if n not in _UNDECLARABLE]


def _builtin_type_names() -> list[str]:
    """Every name a user ``data`` declaration could shadow, from the LIVE
    registries, so a name added later joins the battery without anyone
    remembering to widen a list.

    THREE registries, because no one of them is the whole set (PR #1372
    review).  ``_register_builtin_adts`` holds ``Option`` / ``Result`` /
    ``Ordering`` / ``UrlParts`` / ``Tuple`` / ``MdInline`` / ``MdBlock``;
    :func:`~vera.prelude.prelude_adt_names` holds the four the PRELUDE
    injects on demand — ``Json``, ``HtmlNode``, ``Request``, ``Response`` —
    which the Pass-0.5 snapshot is taken too early to see, and which are
    exactly the names #1316's own repro is about; and the built-in
    CONTAINERS are branched on by name in codegen and are in neither.
    Reading only the first missed the four the prelude declares.

    ``Tuple`` is INCLUDED, and was wrongly excluded at first on the grounds
    that codegen's constructor path special-cases the name: that is a
    different question from the width one this battery measures, and
    ``private data Tuple { … }`` is measured compiling and running like any
    other shadow.  An exclusion whose reason does not survive measurement is
    a hole in a battery whose whole job is to have none.
    """
    gen = CodeGenerator()
    gen._register_builtin_adts()
    return sorted(
        set(gen._adt_layouts)
        | set(prelude_adt_names())
        | {"Array", "Map", "Set", "Decimal", "Future"},
    )


_CONTROL_ADT = "ZzShadowCtl"


def _shadow_program(name: str) -> str:
    """The same program, parameterised by the declared ADT's name."""
    return (
        f"private data {name} {{ MkShadow(Int) }}\n\n"
        f"public fn unwrap(@{name} -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  match @{name}.0 {{\n"
        "    MkShadow(@Int) -> @Int.0\n"
        "  }\n"
        "}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(@Int.result == 7)\n"
        "  effects(pure)\n"
        "{\n"
        "  unwrap(MkShadow(7))\n"
        "}\n"
    )


class TestDeclaredAdtBeatsTheBuiltinName:
    """#1331's repro, over every name it could be written with.

    Base: ``Array`` compiled to a module with NO exports at all, and the
    remaining names passed by width-luck.  The differential against a
    fresh-name control is what makes that luck impossible to rely on again —
    it fails for a name whose emitted signature merely happens to be right
    for a wrong reason.
    """

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_a_data_declaration_of_a_builtin_name_runs(self, name: str) -> None:
        assert _run(_shadow_program(name), fn="main") == 7

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_it_emits_the_control_program_byte_for_byte(
        self, name: str,
    ) -> None:
        """The declared ADT's WAT must be the fresh name's WAT.

        A run assertion alone accepts a body that computes 7 through a
        different representation; this pins the representation itself.
        """
        shadowed = _compile_ok(_shadow_program(name))
        control = _compile_ok(_shadow_program(_CONTROL_ADT))
        for fn in ("unwrap", "main"):
            assert wat_fn_body(shadowed.wat, fn) == wat_fn_body(
                control.wat, fn), f"{name}: {fn} differs from the control"

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_no_diagnostic_at_all(self, name: str) -> None:
        """Base: ``[E602]`` at the match arm plus an ``[E620]`` cascade."""
        result = _compile(_shadow_program(name))
        assert [d.error_code for d in result.diagnostics] == []
        assert sorted(result.exports) == ["main", "unwrap"]

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_show_over_a_shadow_renders_the_declaration(
        self, name: str,
    ) -> None:
        """The ABILITY-DISPATCH deciders, found by the same sweep.

        ``_translate_show`` and its hash twin dispatch on the type's base
        name, so a declared ``data Array`` took the array arm and walked its
        one-word heap pointer as a (ptr, len) pair: ``show(MkShadowS(7))``
        compiled to a module that fails to load with ``expected i32 but
        nothing on stack``.  Measured by withdrawing the guard, so the cell
        is known to bite rather than assumed to.

        Total over the declarable names since #1397: the one name that had
        to be skipped here — ``Tuple``, whose declaration rendered ``(7)``
        through the built-in variadic-product path — is refused at check
        instead, so it is asserted by :class:`TestSpecialCasedBuiltinAdtsAreRefused`
        rather than excused here.
        """
        source = (
            f"private data {name} {{ MkShadowS(Int) }}\n\n"
            "public fn main(@Unit -> @String)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n"
            "  show(MkShadowS(7))\n"
            "}\n"
        )
        result = _compile_ok(source)
        assert execute(result, fn_name="main").value == "MkShadowS(7)"

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_equality_over_a_shadow_compares_the_declaration(
        self, name: str,
    ) -> None:
        """The structural-Eq arm of the same dispatch.

        Total for the same reason as its ``show`` twin: the ``Tuple``
        declaration that was refused ``[E243]`` here against the BUILT-IN's
        fields is now refused at check.
        """
        source = (
            f"private data {name} {{ MkShadowS(Int) }}\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n"
            f"  if MkShadowS(7) == MkShadowS(7) then {{ 7 }} else {{ 0 }}\n"
            "}\n"
        )
        assert _run(source, fn="main") == 7

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_a_shadow_INSIDE_a_container_is_never_silently_miscompiled(
        self, name: str,
    ) -> None:
        """The element position, which the battery above never reached.

        `_shadow_program` places the shadowed name in a parameter and a
        match; nothing put it INSIDE a container, where a different family
        of deciders answers.  With the element side still reading a declared
        ``Array`` as a two-word pair while the scrutinee side had stopped,
        the halves disagreed and an index over ``@Array<Array>`` compiled at
        **rc 0 with zero diagnostics** to a module no runtime can load
        (`type mismatch: expected a type but nothing on stack`) — strictly
        worse than the loud `[E602]` the same program got before the
        scrutinee-side fix.

        The property asserted is the one that holds for EVERY name: the
        program either runs and gives the right answer, or is refused with a
        diagnostic.  It is never accepted and unloadable.  Which of the two
        it is depends on the name — for ``Array`` the head of
        ``Array<Array>`` is the DECLARATION (spec §8.4.1), so indexing it is
        refused; for the rest the container is still the container — and
        pinning the disjunction rather than one branch is what makes the
        cell meaningful for all sixteen.
        """
        source = (
            f"private data {name} {{ MkShadowV(Int) }}\n\n"
            f"private fn unwrap(@{name} -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n"
            f"  match @{name}.0 {{\n"
            "    MkShadowV(@Int) -> @Int.0\n"
            "  }\n}\n\n"
            f"private fn g(@Array<{name}> -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n"
            f"  unwrap(@Array<{name}>.0[0])\n"
            "}\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  g([MkShadowV(7)])\n}\n"
        )
        result = _compile(source)
        if result.diagnostics:
            return  # refused, loudly — the acceptable branch
        assert _run(source, fn="main") == 7, (
            f"{name}: accepted with no diagnostic and did not run correctly"
        )

    def test_an_alias_to_an_array_is_a_pair_in_element_position(
        self,
    ) -> None:
        """The element deciders resolve aliases, like every other decider.

        ``type Row = Array<Int>;`` used as ``@Array<Row>`` gives the element
        deciders the NAME ``Row``, which is not ``String`` and does not begin
        ``Array<`` — so before they could resolve an alias they sized it as a
        4-byte pointer with a single ``i32.load``, where the value is the
        8-byte (ptr, len) pair its target is.  Asked directly, because the
        deciders are the thing under test and an end-to-end program routes
        around them through the AST type arguments.
        """
        _result, gen = _compile_with_generator(
            "type Row = Array<Int>;\n\n"
            "public fn main(@Unit -> @Nat)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  array_length([1, 2, 3])\n}\n"
        )
        ctx = _probe_context(gen)
        assert ctx._is_pair_element_type("Row") is True
        assert ctx._element_mem_size("Row") == 8
        assert ctx._element_load_op("Row") is None  # pair: two loads
        assert ctx._element_wasm_type("Row") == "i32_pair"
        # And it agrees with what the same alias reads as a slot type.
        assert ctx._is_pair_type_name("Row") is True

    def test_an_alias_to_a_scalar_is_that_scalar_in_element_position(
        self,
    ) -> None:
        """The arm only ``_resolve_element_name`` decides.

        A pair-valued alias is caught by `_is_pair_element_type`'s own
        canonicalization, so it does not exercise the shared resolution the
        four size/load/store/type deciders read.  A SCALAR alias does: under
        ``type Cnt = Int;`` the name ``Cnt`` is in neither the primitive
        table nor the pair predicate, so before the resolution it fell
        through to the ADT default — 4 bytes and a single ``i32.load`` for a
        value that is an 8-byte ``i64``.

        Measured at ``release/v0.2.0``: ``_element_mem_size("Cnt")`` is 4 and
        ``_element_load_op("Cnt")`` is ``i32.load`` there.  It is a LATENT
        disagreement rather than a live miscompile — every corpus route to
        these deciders carries the resolved element type rather than the
        alias's bare name — which is exactly why it needs a decider-level
        cell: no program exercises it, and the next caller that passes a bare
        alias name would inherit a wrong width silently.
        """
        _result, gen = _compile_with_generator(
            "type Cnt = Int;\n\n"
            "public fn main(@Unit -> @Cnt)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  7\n}\n"
        )
        ctx = _probe_context(gen)
        assert ctx._element_mem_size("Cnt") == 8
        assert ctx._element_load_op("Cnt") == "i64.load"
        assert ctx._element_store_op("Cnt") == "i64.store"
        assert ctx._element_wasm_type("Cnt") == "i64"
        assert ctx._is_pair_element_type("Cnt") is False

    def test_the_container_element_control_runs(self) -> None:
        """The same program under a fresh ADT name compiles and returns 7 at
        every revision — so the cell above cannot pass by refusing
        everything."""
        source = _shadow_program(_CONTROL_ADT).replace(
            "public fn main", "private fn g(@Array<" + _CONTROL_ADT + "> -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  unwrap(@Array<" + _CONTROL_ADT + ">.0[0])\n}\n\n"
            "public fn main", 1,
        ).replace("  unwrap(MkShadow(7))", "  g([MkShadow(7)])")
        assert _run(source, fn="main") == 7

    def test_the_container_still_works_when_nothing_declares_its_name(
        self,
    ) -> None:
        """The relaxation must not cost the built-in reading.

        Green before AND after by construction, so it proves nothing about
        the fix — it is here so the reorder cannot break what it must leave
        alone."""
        source = """\
public fn total(@Array<Int> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  array_length(@Array<Int>.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  total([5, 6, 7])
}
"""
        assert _run(source, fn="main") == 3


# =====================================================================
# #1316 — the prelude is a namespace
# =====================================================================


def _alias_program(name: str) -> str:
    """``type <name> = Int;`` over the same two-function program.

    The #1309 battery's shape, extended to the two names it had to exclude:
    ``Json`` and ``HtmlNode``, whose prelude combinator bodies are emitted
    into the module and rendered their own parameters against the flat map
    this fixes.
    """
    return (
        f"type {name} = Int;\n\n"
        f"public fn twice(@{name} -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        f"  @{name}.0 + @{name}.0\n"
        "}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true)\n"
        "  ensures(true)\n"
        "  effects(pure)\n"
        "{\n"
        "  twice(21)\n"
        "}\n"
    )


_MODULE_SHADOW = """\
module tlib;

private data {name} {{ MkShadow(Int) }}

public fn probe(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  match MkShadow(@Int.0) {{
    MkShadow(@Int) -> @Int.0
  }}
}}
"""

_MODULE_SHADOW_MAIN = """\
import tlib;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  tlib::probe(7)
}
"""


class TestSpecialCasedBuiltinAdtsAreRefused:
    """#1397 — `data Tuple` / `data Future` are refused at check (E158).

    The spine tells a declared `Array` / `Map` / `Set` / `Decimal` apart from
    the container of that name, which is what #1321/#1331 established.  It
    cannot do that for these two: `Tuple` is registered by
    `_register_builtin_adts` AND rendered through a variadic-product path
    keyed on its name, and `Future` is the transparent wrapper several
    derivations peel before asking what the name means.  Measured at
    `release/v0.2.0`: `show(MkShadowS(7))` under `data Tuple` printed `(7)`,
    dropping the constructor name and refusing `[E243]` on equality against
    the BUILT-IN's fields, and the same program under `data Future` compiled
    to a module that fails to load.

    So the name is refused, on the rule E151 already applies to built-in
    functions and E152 to built-in effects.
    """

    def test_the_compiler_reserves_exactly_these(self) -> None:
        """The ruling, pinned as an EQUALITY against an explicit set.

        Red-capable in both directions, which the previous complement-based
        assertion was not (PR #1404 review, finding 3):
        `_declarable_type_names()` is *defined* as `live - _UNDECLARABLE`, so
        any "the halves partition the live set" assertion holds by
        construction — measured, a fake special-cased built-in added to the
        registry and left unreserved leaves such an assertion green.  This
        one fails if the compiler stops reserving a name #1397 reserves, and
        equally if it starts reserving one this file does not expect, so a
        new special-cased built-in cannot be added to the compiler's tuple
        without a deliberate edit here.
        """
        assert set(_UNDECLARABLE) == set(_EXPECTED_RESERVED), (
            f"compiler reserves {sorted(_UNDECLARABLE)}, "
            f"this file expects {sorted(_EXPECTED_RESERVED)}"
        )

    @pytest.mark.parametrize("name", _EXPECTED_RESERVED)
    def test_the_declaration_is_refused(self, name: str) -> None:
        codes = [d.error_code for d in _check(_shadow_program(name))]
        assert "E158" in codes, codes

    @pytest.mark.parametrize("name", _EXPECTED_RESERVED)
    def test_the_declaration_is_refused_in_a_module_too(
        self, name: str, tmp_path: Path,
    ) -> None:
        """One rule, both declaration sites.

        The entry file and a module are separate registration passes, and
        the neighbouring data-namespace rails answer them differently — a
        module `data Option` is E621 at CODEGEN while the entry's is
        accepted (#1312's asymmetry).  A reservation that held only where
        the checker happened to be asked first would leave the other door
        open, so the module door is measured rather than assumed.
        """
        from tests.module_fixture_helpers import build_multi_module_past_check

        check_errors, _result, _cg = build_multi_module_past_check(
            tmp_path,
            {
                "tlib.vera": _MODULE_SHADOW.format(name=name),
                "main.vera": _MODULE_SHADOW_MAIN,
            },
        )
        assert "E158" in [code for code, _ in check_errors], check_errors

    @pytest.mark.parametrize("name", _EXPECTED_RESERVED)
    def test_an_alias_of_the_same_name_is_still_legal(self, name: str) -> None:
        """Only the DATA namespace is reserved.  `type Tuple = Int;` shadows
        nothing the compiler special-cases by name — it resolves through the
        spine like any other alias, and #1309's battery covers it."""
        assert _run(_alias_program(name), fn="main") == 42

    @pytest.mark.parametrize(
        "name", ["Option", "Result", "Ordering", "UrlParts", "Array", "Map"])
    def test_every_other_builtin_name_stays_declarable(
        self, name: str,
    ) -> None:
        """The reservation is exactly the special-cased names.

        §8.4.1 makes the prelude's data types ordinary declarations a program
        may shadow, `examples/vera/collections.vera` ships a `public data
        Option<T>`, and #1312's E623 rail is built on entry-file shadowing
        being legal — so widening this would refuse programs the language
        documents as valid.
        """
        assert "E158" not in [
            d.error_code for d in _check(_shadow_program(name))]

    def test_every_reserved_name_is_one_the_compiler_knows(self) -> None:
        """A reserved name must be a name the live registry actually has.

        Measured red by perturbation: `"Tupl"` in the reserved set fails
        the subset test, and a set shrunk to `()` fails non-emptiness —
        which matters because a parametrize over an empty set makes every
        refusal cell pass vacuously.

        Behavioural totality is NOT asserted here and cannot be: it lives in
        :class:`TestDeclaredAdtBeatsTheBuiltinName`, which runs every
        unreserved name end to end with no skips, so an unreserved
        special-cased built-in turns those cells red the moment its
        semantics misbehave under a user declaration — which is exactly what
        `Tuple` did before #1397.
        """
        live = set(_builtin_type_names())
        assert _EXPECTED_RESERVED, "the reserved set must not be empty"
        assert set(_EXPECTED_RESERVED) <= live, (
            f"reserved names the compiler does not know: "
            f"{sorted(set(_EXPECTED_RESERVED) - live)}"
        )

    def test_the_builtin_tuple_is_untouched_by_the_reservation(self) -> None:
        """Reserving the NAME must not disturb the built-in it protects.

        Retracting codegen's FIX-3 discrimination (which existed only to
        tell a user `data Tuple` from the variadic carrier) leaves the
        carrier on the `expr.name == "Tuple"` path it always had; this pins
        that construction, `show`, `match` and `hash` over the built-in
        still answer as §9 specifies.
        """
        source = """\
public fn shown(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Tuple(1, 2))
}

public fn summed(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Tuple(3, 4) {
    Tuple(@Int, @Int) -> @Int.0 + @Int.1
  }
}

public fn hashes_alike(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if hash(Tuple(1, 2)) == hash(Tuple(1, 2)) then { 7 } else { 0 }
}
"""
        result = _compile_ok(source)
        assert execute(result, fn_name="shown").value == "(1, 2)"
        assert execute(result, fn_name="summed").value == 7
        assert execute(result, fn_name="hashes_alike").value == 7

    @pytest.mark.parametrize("name", _EXPECTED_RESERVED)
    def test_a_constructor_of_the_name_is_refused_too(self, name: str) -> None:
        """The CONSTRUCTOR namespace, which the type reservation does not
        reach (PR #1404 review, CodeRabbit).

        `ctor_layouts` is flattened by CONSTRUCTOR name across every ADT
        (`vera/codegen/functions.py`), and both retracted sites key on
        `expr.name` — a constructor name.  So `private data Box { Tuple(Bool) }`
        put its FIXED layout in the built-in carrier's flat slot: measured,
        `ctor_layouts["Tuple"].field_offsets` became `((8, "i64"),)` where
        the carrier's is `()`.

        Measured at `release/v0.2.0`, that silently disabled the #820
        widen guard on a GENUINE built-in tuple construction elsewhere in
        the same program — `tc(u64.MAX)` returned a reinterpreted negative
        `@Int` with no trap — and the verifier stopped obligating it, because
        `_lookup_constructor_info("Tuple")` found `Box`'s constructor and
        skipped the carrier fallback.  A declaration in one corner of a file
        changing what a built-in means in another is the same disease the
        type reservation cures, so the name is refused in both namespaces.
        """
        codes = [d.error_code for d in _check(
            f"private data ZzBox {{ {name}(Bool) }}\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  0\n}\n"
        )]
        assert "E158" in codes, codes

    @pytest.mark.parametrize("name", _EXPECTED_RESERVED)
    def test_a_constructor_of_the_name_is_refused_in_a_module_too(
        self, name: str, tmp_path: Path,
    ) -> None:
        """Both doors for the CONSTRUCTOR half as well as the type half.

        The type reservation is measured at both declaration sites, and the
        constructor one has to be too: the collision it prevents is a FLAT
        `ctor_layouts` slot shared across every ADT in the compiled module,
        so a module's declaration reaches the entry program's built-in tuple
        constructions exactly as an entry-file one does.  Measured at
        `release/v0.2.0`: accepted in a module, for both names.
        """
        from tests.module_fixture_helpers import build_multi_module_past_check

        module = (
            "module tlib;\n\n"
            f"private data ZzBox {{ {name}(Bool) }}\n\n"
            "public fn probe(@Int -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  @Int.0\n}\n"
        )
        check_errors, _result, _cg = build_multi_module_past_check(
            tmp_path,
            {"tlib.vera": module, "main.vera": _MODULE_SHADOW_MAIN},
        )
        assert "E158" in [code for code, _ in check_errors], check_errors

    def test_a_constructor_of_an_unreserved_builtin_name_is_not_E158(
        self,
    ) -> None:
        """E158 does not fire — which is all this measures.

        Named for the assertion, not for a safety property it does not
        establish (PR #1404 review, finding 7).  "Unreserved" is not "safe":
        the flat-by-constructor-name layout table reaches every built-in
        constructor, and for `Less` it was a silent wrong value while
        `Some` / `None` / `Ok` / `Err` are loud (E213 / E215 / E121).  That
        clobber is #1414, fixed in this PR by per-owner keying rather than
        by widening the reservation — §8.4.1 makes the prelude's data types
        shadowable and `examples/vera/collections.vera` declares `None` and
        `Some`, so a reservation over prelude constructor names would refuse
        a shipped example.  What stays true here is only the E158 boundary.
        """
        codes = [d.error_code for d in _check(
            "private data ZzBox { UrlParts(Bool) }\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  0\n}\n"
        )]
        assert "E158" not in codes, codes

    @pytest.mark.parametrize("name", _EXPECTED_RESERVED)
    def test_a_refused_constructor_is_not_registered(self, name: str) -> None:
        """A name the checker refused must not stay resolvable (#1404 review).

        Registration continues past `_error` so the rest of the declaration
        still reports, which used to leave the refused constructor in
        `env.constructors` — harmless today, because a check failure stops
        the pipeline before anything reads it, but a table that disagrees
        with the diagnostics is a trap for the next consumer.

        Mutation-validated: withdrawing the `continue` in `_register_data`
        puts the entry back and turns this red, so the cell is known to bite
        rather than assumed to.
        """
        from vera.checker.core import TypeChecker

        source = (
            f"private data ZzBox {{ {name}(Bool) }}\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  0\n}\n"
        )
        checker = TypeChecker(source)
        checker.check_program(parse_to_ast(source))
        registered = checker.env.constructors.get(name)
        # `Future` legitimately occupies the name already — the built-in ADT
        # registers its own constructor in `environment.py` — so the property
        # is OWNERSHIP, not absence: whatever sits under the name must not be
        # the refused declaration's.
        assert getattr(registered, "parent_type", None) != "ZzBox", (
            f"{name!r} was refused but ZzBox's constructor was registered")

    def test_the_builtin_tuple_is_still_not_eq(self) -> None:
        """And the built-in's own limitation is unchanged either way.

        `Tuple` is Hash- and Show-derivable but NOT Eq-derivable (§9.8;
        SKILL.md's ability table says so), so `==` over the carrier is
        `[E243]` at check.  Measured identical at `release/v0.2.0` — it is
        pinned here so the retraction cannot be read as having caused it,
        and so a later fix to the built-in's Eq is a deliberate change to
        this cell rather than a silent one.
        """
        codes = [d.error_code for d in _check("""\
public fn same(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  Tuple(1, 2) == Tuple(1, 2)
}
""")]
        assert codes == ["E243"], codes



class TestUserConstructorCannotDisplaceABuiltinOne:
    """#1414 — a user constructor of a built-in/prelude constructor NAME must
    not change what the built-in one means.

    Codegen holds constructor layouts in one table keyed by bare constructor
    name across every ADT (`ctor_layouts.update(layouts)` over
    `_adt_layouts.items()`, built-ins first), so a later user ADT wins the
    slot.  #1408 closed this for `Tuple` and `Future` by reserving those two
    names, but the mechanism is general and reserving the rest is not
    available: §8.4.1 makes the prelude's data types shadowable, #1277 says
    so in terms, and `examples/vera/collections.vera` ships a `public data
    Option<T> { None, Some(T) }` that a prelude-constructor reservation would
    refuse.

    So the fix is per-owner keying, and these are its two measured repros.
    Both were check-clean AND verify-clean at `release/v0.2.0` and at the
    #1404 merge tip.
    """

    def test_an_unrelated_declaration_does_not_change_what_compare_returns(
        self,
    ) -> None:
        """Base: every `Ordering` rendered as the clobbering constructor.

        `show(compare(1, 2))`, `(2, 1)` and `(2, 2)` all returned
        `'Less(false)'` where the control returns `Less` / `Greater` /
        `Equal`.  `ZzBox` is never used — its mere declaration changed the
        answer for every input, on a program with zero diagnostics.
        """
        source = """\
private data ZzBox { Less(Bool) }

public fn lt(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(1, 2))
}

public fn gt(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(2, 1))
}

public fn eqq(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(2, 2))
}
"""
        result = _compile_ok(source)
        got = {
            fn: execute(result, fn_name=fn).value
            for fn in ("lt", "gt", "eqq")
        }
        assert got == {"lt": "Less", "gt": "Greater", "eqq": "Equal"}, got

    def test_the_control_without_the_declaration_is_identical(self) -> None:
        """The same three functions with no colliding declaration.

        Green at every revision by construction — it is here so the cell
        above cannot be satisfied by breaking `compare` for everyone.
        """
        source = """\
public fn lt(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(1, 2))
}

public fn gt(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(2, 1))
}

public fn eqq(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(2, 2))
}
"""
        result = _compile_ok(source)
        got = {
            fn: execute(result, fn_name=fn).value
            for fn in ("lt", "gt", "eqq")
        }
        assert got == {"lt": "Less", "gt": "Greater", "eqq": "Equal"}, got

    def test_a_colliding_declaration_does_not_drop_the_function(self) -> None:
        """The second repro: a `[E602]` degrade rather than a wrong value.

        Base: `show(@UrlParts.0)` beside `private data ZzBox {
        UrlParts(Bool) }` was check-clean and verify-clean, then compiled to
        a module with NO exports behind an `[E602]` warning.  No
        `UrlParts(...)` pattern appears, so nothing collides at check.
        """
        source = """\
private data ZzBox { UrlParts(Bool) }

public fn render(@UrlParts -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(@UrlParts.0)
}
"""
        result = _compile(source)
        assert [d.error_code for d in result.diagnostics] == [], (
            [(d.severity, d.error_code, d.description[:70])
             for d in result.diagnostics]
        )
        assert "render" in result.exports, sorted(result.exports)

    def test_the_user_constructor_still_works_on_its_own_type(self) -> None:
        """Per-owner keying must not cost the DECLARATION its meaning.

        §8.4.1 grants the shadow; the point is that both readings coexist,
        so the user's `Less(Bool)` has to construct and match as its own
        type while `Ordering`'s `Less` stays the prelude's.
        """
        source = """\
private data ZzBox { Less(Bool) }

public fn mine(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(Less(true))
}

public fn theirs(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(1, 2))
}
"""
        result = _compile_ok(source)
        assert execute(result, fn_name="mine").value == "Less(true)"
        assert execute(result, fn_name="theirs").value == "Less"


    def test_the_nested_recovery_collision_is_refused_at_check(self) -> None:
        """Why the nested-recovery site is LATENT, pinned so it stays so.

        `_recover_ptype_via_nested_fields` reads a constructor's
        `field_types` to rebuild a generic ADT's type arguments, and read
        the flat by-name table to do it — the render site's defect, one pass
        over (PR #1419 review).  It is owner-qualified now, and no program
        reaches the old path, and since #1425 the reason is a rail rather
        than a coincidence: two declarations in one namespace sharing a
        constructor name are `[E159]` at the declaration, in either order.
        Before that rail the shielding was accidental — the CHECKER
        resolved the call through the same last-wins by-name rule, so when
        the flat map held the wrong ADT the checker had already refused the
        call against that same wrong resolution.

        Two layers wrong in the same direction is a coincidence, not a
        guarantee.  This cell pins the coincidence: if the checker is ever
        taught per-owner resolution without code generation following, the
        E212 disappears, this cell goes red, and it names the site whose
        owner-qualified read then becomes load-bearing.
        """
        rose = "private data Rose<T> { Leaf(T), Node(T, Rose<T>) }"
        zz = "private data ZzBox { Node(Bool) }"
        body = (
            "\n\npublic fn main(@Unit -> @String)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  show(Node(1, Leaf(2)))\n}\n"
        )
        # Since #1425 the pair is refused at the DECLARATION, in either
        # order — stronger shielding than the E212-on-use it used to rely
        # on, and it no longer depends on which declaration won the slot.
        for src in (rose + "\n\n" + zz + body, zz + "\n\n" + rose + body):
            codes = [d.error_code for d in _check(src)]
            # E159 always; one order additionally carries the E212 the USE
            # used to be shielded by, which is now redundant but harmless.
            assert "E159" in codes, (
                f"the shielding refusal is gone ({codes}) — see the docstring")


#: A shadowing `Less` at each TAG INDEX.  The first entry is the shape the
#: fix was first written against, and it is the one index where a
#: reader-only fix cannot be caught: the user's `Less` sits at tag 0, which
#: is also `Ordering`'s, so a value tagged through the wrong table still
#: renders right.  Shifting the index separates the writer from the reader
#: (PR #1419 review).
_LESS_AT_INDEX = {
    "tag0": "private data ZzBox { Less(Bool) }",
    "tag1": "private data ZzBox { Pad(Bool), Less }",
    "tag3": "private data ZzBox { A, B, C, Less }",
}

_COMPARE_TRIO = """
public fn lt(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(%(a)s, %(b)s))
}

public fn gt(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(%(b)s, %(a)s))
}

public fn eqq(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(%(b)s, %(b)s))
}
"""

#: `compare` over each ordered primitive, so the fix is not pinned on `Int`
#: alone — the desugaring is shared and a per-type regression would hide.
_COMPARE_OPERANDS = {
    "Int": {"a": "1", "b": "2"},
    "String": {"a": '"a"', "b": '"b"'},
    "Float64": {"a": "1.0", "b": "2.0"},
}


class TestShadowingConstructorTagIndex:
    """#1414 — the tag a compiler-emitted constructor is WRITTEN with must
    come from the same table it is READ through.

    Converting only the reader left the value tagged through the user's ADT
    and rendered through `Ordering`'s, which agree exactly when the
    shadowing constructor sits at its namesake's index.  Measured on the
    reader-only fix: `ZzBox { Pad(Bool), Less }` gave `Equal` / `Greater` /
    `Equal` for lt / gt / eqq, and `ZzBox { A, B, C, Less }` gave
    `Greater` / `Greater` / `Equal`, on programs `vera check` and
    `vera verify` both call clean.
    """

    @pytest.mark.parametrize("index", sorted(_LESS_AT_INDEX))
    @pytest.mark.parametrize("ty", sorted(_COMPARE_OPERANDS))
    def test_compare_renders_correctly_at_every_shadow_index(
        self, ty: str, index: str,
    ) -> None:
        source = (
            _LESS_AT_INDEX[index] + "\n"
            + _COMPARE_TRIO % _COMPARE_OPERANDS[ty]
        )
        result = _compile_ok(source)
        got = {
            fn: execute(result, fn_name=fn).value
            for fn in ("lt", "gt", "eqq")
        }
        assert got == {"lt": "Less", "gt": "Greater", "eqq": "Equal"}, got

    @pytest.mark.parametrize("index", sorted(_LESS_AT_INDEX))
    def test_eq_and_hash_of_compare_results_agree_at_every_index(
        self, index: str,
    ) -> None:
        """`show` is not the only reader of the tag.

        A wrongly-tagged `Ordering` compares and hashes wrongly too, and
        `eq(compare(1, 2), compare(2, 2))` returned 1 on the reader-only
        fix — `Less` and `Equal` indistinguishable — with `hash` agreeing,
        so neither would have caught it.
        """
        source = _LESS_AT_INDEX[index] + """

public fn lt_vs_eq(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(compare(1, 2), compare(2, 2))
}

public fn hash_agrees(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(hash(compare(1, 2)), hash(compare(2, 2)))
}
"""
        result = _compile_ok(source)
        # A `@Bool` comes back as WASM's 0 / 1, not a Python bool.
        assert execute(result, fn_name="lt_vs_eq").value == 0, (
            "Less and Equal must not compare equal")
        assert execute(result, fn_name="hash_agrees").value == 0, (
            "Less and Equal must not hash alike")


class TestStructuralEqEnumerationIsUnobservable:
    """#1414 — why `operators.py`'s owner-qualified enumeration is INERT,
    stated as the three legs that make it so.

    Forcing `_generate_adt_eq_fn_body` back to the flat map leaves the whole
    tag-index battery green, so no behavioural cell can red on it.  That is
    not because the site is unreached — it runs, measured, as
    `$eq_Ordering` — but because its output is insensitive for the only
    shapes a program can build.  Each leg is asserted here, so if any of
    them changes the argument fails loudly instead of rotting.
    """

    _SRC = """\
private data ZzBox { Pad(Bool), Less }

public fn cmp_eq(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(compare(1, 2), compare(2, 2))
}
"""

    def test_leg1_the_flat_enumeration_really_does_lose_a_constructor(
        self,
    ) -> None:
        """The collision is real at this site — the conversion is not a
        no-op dressed up as one."""
        _result, gen = _compile_with_generator(self._SRC)
        flat_owner = {
            c: adt for adt, ls in gen._adt_layouts.items() for c in ls
        }
        assert flat_owner["Less"] == "ZzBox", flat_owner["Less"]
        flat_enum = sorted(c for c, p in flat_owner.items() if p == "Ordering")
        assert flat_enum == ["Equal", "Greater"], flat_enum
        assert sorted(gen._adt_layouts["Ordering"]) == [
            "Equal", "Greater", "Less"]

    def test_leg2_orderings_constructors_are_all_nullary(self) -> None:
        """Which is why losing one cannot change the emitted equality: with
        no fields anywhere, the generated body reduces to a tag comparison
        and the per-constructor field plans contribute nothing."""
        _result, gen = _compile_with_generator(self._SRC)
        assert all(
            not layout.field_offsets
            for layout in gen._adt_layouts["Ordering"].values()
        )

    @pytest.mark.parametrize("decl,expected", [
        # Two USER declarations sharing a name — E159, this PR.
        ("private data A1 { Wrap(Int) }\n\nprivate data A2 { Wrap(Bool) }",
         "E159"),
        # Shadowing a FIELD-CARRYING prelude constructor — refused at the use.
        ("private data ZzBox { Pad(Bool), Some(Bool) }", "E213"),
    ])
    def test_leg3_the_single_file_routes_to_that_shadow_are_refused(
        self, decl: str, expected: str,
    ) -> None:
        """Both SINGLE-FILE routes to a field-carrying shadow are refused.

        Deliberately narrower than the claim this cell first made.  "The
        shadow is unbuildable" is FALSE: it is buildable across a module
        boundary, where an entry-file declaration takes a constructor name
        an imported type also declares — the shape #1419's review calls
        finding A, which is miscompiled today and is not fixed by this PR.
        What survives is the conclusion, for a different reason: no `$eq_`
        helper is generated for that cross-namespace shape at all (the tag
        is what goes wrong there), so this enumeration is still not the site
        at fault, and no program reaches it with disagreeing tables.
        """
        source = decl + """

private fn use_it(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
"""
        codes = [d.error_code for d in _check(source)]
        assert expected in codes, codes


class TestRedeclaringAPreludeAdtNeverICEs:
    """#1419 finding B — a legal redeclaration must not reach an internal
    compiler error.

    §8.4.1 lets a program redeclare a prelude data type, including with
    FEWER constructors.  `_owned_ctor_layout` briefly raised
    `CodegenInvariantError` when an owner-stamped reference named a
    constructor its owner did not declare, and `private data Ordering {
    Less, Equal }` + `show(compare(1, 2))` — check-clean and verify-clean —
    became "Internal compiler error … Please file a bug report".  The door
    degrades to no-layout instead, so the caller's `CodegenSkip` reports the
    construct and drops the function, which is what the compiler did before
    #1414.

    What is NOT yet true, and is deliberately not asserted: that `compare`
    still WORKS beside a user `Ordering`.  Making it work needs the render
    side to become owner-aware at the same time — resolving only the
    constructor against the built-in table was measured producing a module
    that fails to load, which is worse than the skip.  That is the same
    per-(owner, ADT, constructor) keying finding A needs.
    """

    @pytest.mark.parametrize("decl", [
        "private data Ordering { Less, Equal }",
        "public data Ordering { Lt, Eq, Gt }",
        "private data Ordering { Less, Equal, Greater }",
    ])
    def test_no_internal_compiler_error(self, decl: str) -> None:
        source = decl + """

public fn probe(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(compare(1, 2))
}
"""
        assert not _check(source), [d.error_code for d in _check(source)]
        result = _compile(source)
        # Either it compiles, or it is refused with a located diagnostic —
        # never an invariant violation.
        for d in result.diagnostics:
            assert "Internal compiler error" not in d.description, d.description
            assert d.error_code != "E999", d.description


class TestNoUnannotatedBareConstructorLookup:
    """#1414 — the STRUCTURAL rail: every constructor lookup that could
    carry an owner must go through the one door.

    `WasmContext._owned_ctor_layout` is that door.  Everything else in
    `vera/wasm/` and `vera/smt.py` that reaches into the flat, by-name
    `_ctor_layouts` map has to say why it cannot name an owner, with a
    `# ctor-owner-exempt: <reason>` marker — the same shape the repo already
    uses for `# encoding-exempt` and `# diag-fields-exempt`.

    This is what the behavioural cells cannot do.  Two of the three
    wrong-value sites in this issue were found one at a time, by review,
    after the first fix looked complete; a new bare lookup added tomorrow
    would be invisible to every program-level test until someone wrote the
    program that observes it.  Here it is red immediately.
    """

    #: Every module that can reach a flat constructor projection — the whole
    #: of `vera/wasm/` and `vera/codegen/` plus `vera/smt.py`, discovered by
    #: globbing rather than listed, so a new module joins the rail by
    #: existing.  The previous form named seven files by hand and included
    #: `vera/smt.py` for an attribute it does not use, which made its
    #: listing vacuous while `vera/codegen/monomorphize.py` — which builds
    #: its own flat ownership map — was outside the rail entirely (PR #1419
    #: review, finding C).
    _DIRS = ("vera/wasm", "vera/codegen")
    _EXTRA_FILES = ("vera/smt.py",)
    #: All three flat projections, not just the layouts one: `_ctor_to_adt`
    #: answers "which ADT owns this name" and `_ctor_adt_tp_indices` its
    #: type-parameter positions, and both are keyed the same way.
    _ATTRS = frozenset({
        "_ctor_layouts", "_ctor_to_adt", "_ctor_adt_tp_indices",
    })
    #: The door itself, plus the constructors that store the maps.  Matched
    #: on the (class, function) pair, not the bare name, so an `__init__`
    #: elsewhere cannot inherit the exemption.
    _ALLOWED = frozenset({
        ("WasmContext", "_owned_ctor_layout"),
        ("WasmContext", "__init__"),
    })

    def _files(self) -> list[str]:
        from pathlib import Path as _P

        root = _P(__file__).resolve().parents[1]
        out: list[str] = []
        for d in self._DIRS:
            out += sorted(
                str(f.relative_to(root)) for f in (root / d).glob("*.py"))
        return out + list(self._EXTRA_FILES)

    @staticmethod
    def _exempt_at(lines: list[str], lineno: int) -> bool:
        """Is the access at *lineno* carrying an exemption marker?

        The marker may sit at the end of the access line, or — where that
        would push the line past PEP 8, which most of the reasons do — in
        the comment block immediately above it (PR #1419 review).  Only a
        CONTIGUOUS run of comment lines counts, so a marker cannot drift
        away from the access it excuses and keep working.
        """
        if "ctor-owner-exempt" in lines[lineno - 1]:
            return True
        i = lineno - 2
        while i >= 0 and lines[i].lstrip().startswith("#"):
            if "ctor-owner-exempt" in lines[i]:
                return True
            i -= 1
        return False

    def _bare_lookups(self) -> list[tuple[str, int, str]]:
        import ast as pyast
        from pathlib import Path as _P

        root = _P(__file__).resolve().parents[1]
        found: list[tuple[str, int, str]] = []
        for rel in self._files():
            src = (root / rel).read_text(encoding="utf-8")
            lines = src.split("\n")
            tree = pyast.parse(src)
            spans: list[tuple[int, int, str, str]] = []
            for cls in pyast.walk(tree):
                if not isinstance(cls, pyast.ClassDef):
                    continue
                for fn in pyast.walk(cls):
                    if isinstance(fn, (pyast.FunctionDef,
                                       pyast.AsyncFunctionDef)):
                        spans.append(
                            (fn.lineno, fn.end_lineno, cls.name, fn.name))
            for fn in pyast.walk(tree):
                if isinstance(fn, (pyast.FunctionDef, pyast.AsyncFunctionDef)):
                    if not any(s[0] == fn.lineno for s in spans):
                        spans.append((fn.lineno, fn.end_lineno, "", fn.name))
            for node in pyast.walk(tree):
                if not (isinstance(node, pyast.Attribute)
                        and node.attr in self._ATTRS):
                    continue
                cls, fn_name = next(
                    ((c, f) for a, b, c, f in sorted(spans)
                     if a <= node.lineno <= b),
                    ("", "<module>"),
                )
                if (cls, fn_name) in self._ALLOWED:
                    continue
                if self._exempt_at(lines, node.lineno):
                    continue
                found.append((rel, node.lineno, f"{cls}.{fn_name}"))
        return found

    def test_every_bare_lookup_is_the_door_or_annotated(self) -> None:
        found = self._bare_lookups()
        assert not found, (
            "constructor layouts resolved by bare name with no owner and no "
            "`# ctor-owner-exempt:` reason — route through "
            "`WasmContext._owned_ctor_layout`, or annotate why an owner is "
            f"unavailable here: {found}"
        )

    def test_the_rail_is_not_vacuous(self) -> None:
        """The walk must actually FIND the sites it is clearing.

        A rail that matched nothing — a renamed attribute, a moved file —
        would pass silently forever.  This asserts the walk still sees the
        annotated population, so the cell above is known to be measuring
        something.
        """
        import ast as pyast
        from pathlib import Path as _P

        root = _P(__file__).resolve().parents[1]
        total = 0
        per_attr = {a: 0 for a in self._ATTRS}
        for rel in self._files():
            tree = pyast.parse((root / rel).read_text(encoding="utf-8"))
            for n in pyast.walk(tree):
                if isinstance(n, pyast.Attribute) and n.attr in self._ATTRS:
                    total += 1
                    per_attr[n.attr] += 1
        assert total >= 35, (
            f"only {total} flat-projection accesses found — the walk has "
            "probably stopped matching")
        # And EVERY attribute the rail claims to cover is actually present,
        # so the set cannot quietly include a name nothing uses (which is
        # what made `vera/smt.py`'s listing vacuous before).
        assert all(per_attr.values()), per_attr
        # And the door is one of them, so the rail is anchored on the very
        # method it exists to protect.
        door = pyast.parse(
            (root / "vera/wasm/context.py").read_text(encoding="utf-8"))
        assert any(
            isinstance(n, pyast.FunctionDef) and n.name == "_owned_ctor_layout"
            for n in pyast.walk(door)
        ), "the owner-qualified door has been renamed or removed"


class TestCompareDesugaringIsOwnerKeyed:
    """#1414 — the SMT desugaring of `compare` means `Ordering`'s
    constructors, whatever the program declares.

    `_desugar_compare`'s docstring promises it "mirrors codegen's Pass 1.6
    exactly … so the verifier reasons over the SAME term the runtime
    produces".  That was untrue once codegen started stamping the three
    references with their owner and the SMT copy did not: the SMT node had
    no recorded type of its own (its span is the `compare(...)` call's), so
    sort resolution fell through to a scan keyed on the bare constructor
    name, which a user declaration captures.
    """

    _REFUTED = """\
%s
public fn f(@Unit -> @Ordering)
  requires(true)
  ensures(@Ordering.result == Greater)
  effects(pure)
{
  compare(1, 2)
}
"""

    @pytest.mark.parametrize("decl", [
        "",
        "private data ZzBox { Less(Bool) }\n",
        "private data ZzBox { Pad(Bool), Less }\n",
        "private data ZzBox { A, B, C, Less }\n",
    ])
    def test_a_refuted_postcondition_over_compare_is_violated(
        self, decl: str,
    ) -> None:
        """`compare(1, 2)` is `Less`, so `ensures(result == Greater)` is
        statically false and must be reported.

        Measured before the owner-keyed sort resolution: with any of the
        colliding declarations present the obligation demoted to `tier3`
        with NO diagnostic and `vera verify` exited 0 — a refuted
        postcondition passing silently.  The empty-declaration row is the
        control that reported `violated` all along, so the cell cannot pass
        by refusing everything.
        """
        from tests.verifier_helpers import _verify

        result = _verify(self._REFUTED % decl)
        ensures = [o for o in result.obligations if o.kind == "ensures"]
        assert len(ensures) == 1, ensures
        assert ensures[0].status == "violated", (
            f"a statically false postcondition demoted to "
            f"{ensures[0].status!r} under {decl!r}")
        assert "E500" in [
            d.error_code for d in result.diagnostics if d.severity == "error"]


class TestSiblingConstructorCollision:
    """#1425 — constructor names are unique per NAMESPACE (spec §8.4).

    The intra-namespace sibling of E610 (two modules) and E157 (two
    imports).  Before it, two declarations sharing a constructor name were
    accepted with no diagnostic, and a USE of the name produced `[E212]` /
    `[E213]` describing whichever declaration registered last rather than
    the collision — measured, `Rose<T> { Leaf(T), Node(T, Rose<T>) }` beside
    `ZzBox { Node(Bool) }` gave "Constructor 'Node' expects 1 field(s), got
    2", the OTHER type's arity.
    """

    _FN = (
        "\n\npublic fn main(@Unit -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  0\n}\n"
    )

    @pytest.mark.parametrize("pair", [
        ("private data A1 { Pair(Int, Int) }",
         "private data A2 { Pair(Bool, Bool) }"),
        ("private data Rose<T> { Leaf(T), Node(T, Rose<T>) }",
         "private data ZzBox { Node(Bool) }"),
    ])
    def test_two_declarations_sharing_a_ctor_name_are_refused(
        self, pair: tuple[str, str],
    ) -> None:
        first, second = pair
        codes = [d.error_code for d in _check(first + "\n\n" + second + self._FN)]
        assert codes == ["E159"], codes
        # Order-independent: the rule is about the namespace, not the order.
        codes = [d.error_code for d in _check(second + "\n\n" + first + self._FN)]
        assert codes == ["E159"], codes

    @pytest.mark.parametrize("decl", [
        "private data Option<T> { None, Some(T) }",
        "private data Result<T, E> { Ok(T), Err(E) }",
        "private data Ordering { Less, Equal, Greater }",
    ])
    def test_restating_a_prelude_type_is_not_a_collision(
        self, decl: str,
    ) -> None:
        """The first legal shadowing shape, which E159 must not touch.

        §8.4.1 makes the prelude's data types ordinary declarations a
        program may shadow, and `examples/vera/collections.vera` ships a
        `public data Option<T> { None, Some(T) }` that a rail keyed on
        `env.constructors` — which already holds the prelude's entries by
        registration time — would refuse.
        """
        assert "E159" not in [d.error_code for d in _check(decl + self._FN)]

    def test_one_declaration_listing_many_constructors_is_fine(self) -> None:
        assert "E159" not in [d.error_code for d in _check(
            "private data A1 { P1(Int), P2(Bool), P3 }" + self._FN)]

    def test_shadowing_an_imported_constructor_is_not_a_collision(
        self, tmp_path: Path,
    ) -> None:
        """The second legal shadowing shape (§8.5.2).

        A local declaration shadows an imported constructor; that is one
        declaration in this namespace and one in another, not two here.
        """
        from tests.module_fixture_helpers import build_multi_module

        lib = (
            "module shapelib;\n\n"
            "public data Shape { Sq(Int), Ci(Int) }\n\n"
            "public fn mk(@Int -> @Shape)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  Sq(@Int.0)\n}\n"
        )
        main = (
            "import shapelib;\n\n"
            "private data Local { Sq(Bool) }\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n"
            "{\n  7\n}\n"
        )
        # Raises on a check error, so reaching the assert IS the property.
        verify_errors, _result, cg = build_multi_module(
            tmp_path, {"shapelib.vera": lib, "main.vera": main})
        assert not verify_errors and not cg, (verify_errors, cg)


class TestPreludeNamespaceScope:
    """A main-file shadow reaches the main file's bodies and nothing else."""

    @pytest.mark.parametrize("name", ["Json", "HtmlNode"])
    def test_the_two_residuals_of_the_1309_battery_now_run(
        self, name: str,
    ) -> None:
        """Base: the module failed to LOAD.

        ``type Json = Int;`` — with no json call anywhere in the program —
        died at ``Invalid input WebAssembly code … type mismatch: expected
        i32, found i64`` inside the prelude's own ``json_get``, and ``type
        HtmlNode = Int;`` inside ``html_attr``.  Both programs are
        check-green and verify-green.
        """
        assert _run(_alias_program(name), fn="main") == 42

    @pytest.mark.parametrize("name", _builtin_type_names())
    def test_an_alias_of_any_builtin_name_runs(self, name: str) -> None:
        """The whole-name sweep, now with no residuals."""
        assert _run(_alias_program(name), fn="main") == 42

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_a_data_shadow_of_any_builtin_name_leaves_the_prelude_alone(
        self, name: str,
    ) -> None:
        """The ``data`` half of the same question.

        An entry ``data Array { … }`` must not make the PRELUDE's own
        ``Array<T>`` parameters a one-word ADT pointer — which is what a
        permissive namespace membership would have done, since a single-file
        program has no module structure to scope by.
        """
        assert _run(_shadow_program(name), fn="main") == 7

    def test_prelude_bodies_compile_in_the_prelude_namespace(self) -> None:
        """POSITIONAL, not just behavioural: every prelude declaration is
        compiled with ``PRELUDE_NAMESPACE`` installed, and every user
        declaration with the entry's.

        A behavioural test passes as soon as ONE name is fixed; this one
        fails if any prelude body is ever compiled in the entry's scope
        again, which is the mechanism rather than a symptom of it.
        """
        seen: list[tuple[str, object]] = []
        original = CodeGenerator._compile_fn_tracked

        def recording(gen: CodeGenerator, decl: ast.FnDecl, **kw: object) -> object:
            seen.append((decl.name, gen._active_module_path))
            return original(gen, decl, **kw)  # type: ignore[arg-type]

        CodeGenerator._compile_fn_tracked = recording  # type: ignore[method-assign,assignment]
        try:
            _compile_ok(_alias_program("Json"))
        finally:
            CodeGenerator._compile_fn_tracked = original  # type: ignore[method-assign]

        prelude_seen = [n for n, ns in seen if ns == PRELUDE_NAMESPACE]
        assert prelude_seen, "no declaration compiled in the prelude namespace"
        assert any(n.startswith("json_") for n in prelude_seen), (
            f"the json combinators were not in it: {sorted(prelude_seen)}"
        )
        assert ("twice", None) in seen and ("main", None) in seen, (
            "a user declaration left the entry namespace"
        )

    def test_an_entry_data_array_leaves_the_prelude_s_own_arrays_alone(
        self,
    ) -> None:
        """The membership scoping, end to end and behaviourally.

        The prelude's ``Json`` combinators carry ``Array<Json>`` fields and
        ``@Array<Json>`` parameters.  If the WASM layer's ADT-name set were
        the FLAT layout map rather than this namespace's data types, the
        entry file's ``data Array`` would be a data type inside the prelude's
        own bodies and those parameters would lower as a one-word ADT
        pointer instead of the container's (ptr, len) pair.

        The scoping is what stops that, and only a program that declares the
        name AND demands the prelude family can tell: the shadow battery
        above compiles no prelude body that mentions ``Array``.
        """
        source = """\
private data Array { MkArr(Int) }

public fn unwrap(@Array -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Array.0 {
    MkArr(@Int) -> @Int.0
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match json_parse("[1,2,3]") {
    Ok(@Json) -> json_array_length(@Json.0) + unwrap(MkArr(4)),
    Err(@String) -> 0
  }
}
"""
        assert _run(source, fn="main") == 7

    def test_the_prelude_registry_records_the_prelude_s_own_widths(
        self,
    ) -> None:
        """The REGISTRY, not just the emitted body.

        A prelude combinator's signature is registered at Pass 1.2 and its
        body compiled at Pass 2; both must be derived in the prelude's
        namespace or the two describe different functions.  Today the
        emitted signature comes from the Pass-2 derivation, so a wrong
        registry entry is masked — which is exactly why it is asserted
        directly rather than left to a behaviour test: `_fn_sigs` is what
        call sites and the `fn_param_types` consumers read, and an entry
        that says i64 where the function takes i32 is a falsehood waiting
        for its first consumer.
        """
        _result, gen = _compile_with_generator(_alias_program("Json"))
        params, _ret = gen._fn_sigs["json_get"]
        assert params[0] == "i32", (
            "json_get's registered parameter took the entry file's `type "
            f"Json = Int;` width: {params}"
        )

    def test_the_entry_declarations_are_not_prelude_members(self) -> None:
        """The membership half, asked directly.

        ``_adt_members_in_scope`` must answer the prelude's own view — global
        infrastructure only — whatever the entry file declares, and must do
        so for a SINGLE-FILE program, where the permissive ``None`` would
        otherwise hand the prelude the entry's declarations.
        """
        result, gen = _compile_with_generator(_shadow_program("Array"))
        assert isinstance(result, CompileResult) and result.ok
        saved = gen._active_module_path
        try:
            gen._active_module_path = None
            entry_members = gen._adt_members_in_scope()
            gen._active_module_path = PRELUDE_NAMESPACE
            prelude_members = gen._adt_members_in_scope()
        finally:
            gen._active_module_path = saved
        assert prelude_members is not None
        assert "Array" not in prelude_members
        assert "Option" in prelude_members
        assert entry_members is None or "Array" in entry_members


# =====================================================================
# The cross-derivation differential
# =====================================================================


class TestCrossDerivationDifferential:
    """Every derivation asked the same name in the same scope agrees.

    This is the invariant that keeps the family closed, and it is a
    DIFFERENTIAL rather than four unit tests on purpose: #1331 survived a
    fix to two of these four sites precisely because nothing compared them.
    Each derivation is reached through the real generator and the real
    ``WasmContext``, so a future site that stops consulting the spine goes
    red here even if its own tests still pass.
    """

    @staticmethod
    def _answers(source: str, name: str) -> dict[str, object]:
        """Every derivation's answer for *name*, in a compiled program's
        entry namespace.

        Four sites, two currencies.  ``_type_expr_to_wasm_type`` (codegen)
        and ``_canonical_wasm_type`` (wasm) take a type EXPRESSION and are
        total.  ``_slot_name_to_wasm_type`` and ``_ref_type_name_wasm_type``
        take a slot-name STRING and answer a narrower contract — a
        pair-represented name is ``None`` in the first, because its callers
        ask ``_is_pair_type_name`` before reaching it.  The differential
        below therefore compares each site against ITSELF under a fresh
        name, which is well defined for all four, rather than against a
        single expected width, which is not.
        """
        _result, gen = _compile_with_generator(source)
        ctx = _probe_context(gen)
        te = _nt(name)
        return {
            "codegen width": gen._type_expr_to_wasm_type(te),
            "wasm canonical width": ctx._canonical_wasm_type(te),
            "wasm slot-name width": ctx._slot_name_to_wasm_type(name),
            "wasm ref-name width": ctx._ref_type_name_wasm_type(name),
            "wasm pair predicate": ctx._is_pair_type_name(name),
            # The ELEMENT side (PR #1372 review).  These five were
            # module-level free functions over a bare `str` — no `self`, no
            # env, no ADT table — so this differential could not ask them the
            # question at all, and they went on laying `Array` out as an
            # 8-byte pair after the scrutinee side had learned otherwise.  A
            # decider a differential cannot address is a decider outside it.
            "element pair predicate": ctx._is_pair_element_type(name),
            "element mem size": ctx._element_mem_size(name),
            "element load op": ctx._element_load_op(name),
            "element store op": ctx._element_store_op(name),
            "element wasm type": ctx._element_wasm_type(name),
        }

    @pytest.mark.parametrize("name", _declarable_type_names())
    def test_a_declared_shadow_answers_as_a_fresh_name_does(
        self, name: str,
    ) -> None:
        """Every site must answer for ``data Array`` exactly what it answers
        for ``data ZzShadowCtl`` — the declaration beats the built-in
        reading, at all five, or the shapes disagree."""
        shadowed = self._answers(_shadow_program(name), name)
        control = self._answers(_shadow_program(_CONTROL_ADT), _CONTROL_ADT)
        assert shadowed == control, (
            f"{name}: a declared shadow reads differently from a fresh name "
            f"— {shadowed} vs {control}"
        )
        assert shadowed["codegen width"] == "i32", shadowed
        # And the element side agrees it is a one-word heap pointer, which
        # is the half that produced an unloadable module when it did not.
        assert shadowed["element pair predicate"] is False, shadowed
        assert shadowed["element mem size"] == 4, shadowed
        assert shadowed["element wasm type"] == "i32", shadowed

    @pytest.mark.parametrize("name", _builtin_type_names())
    def test_an_alias_shadow_answers_as_a_fresh_alias_does(
        self, name: str,
    ) -> None:
        """The alias half of the same invariant (#1309's axis, kept)."""
        shadowed = self._answers(_alias_program(name), name)
        control = self._answers(_alias_program(_CONTROL_ADT), _CONTROL_ADT)
        assert shadowed == control, (
            f"{name}: an alias shadow reads differently from a fresh alias "
            f"— {shadowed} vs {control}"
        )
        assert shadowed["codegen width"] == "i64", shadowed

    def test_every_derivation_consults_the_spine(self) -> None:
        """STRUCTURAL, because one of the five is inert TODAY.

        ``_ref_type_name_wasm_type``'s declared-ADT branch changes no
        answer at present: for a pair name the ``_is_pair_type_name``
        guard above it already declines, and for ``Map`` / ``Set`` /
        ``Decimal`` the handle branch below it answers ``i32``, which is
        what the ADT branch answers too.  Measured: withdrawing that one
        branch leaves this file, the #1309 battery and the whole suite
        green — the same width-luck that hid #1309 and #1331, now on the
        fix's side.

        It is kept because the invariant is "every derivation asks the
        spine", not "every derivation currently disagrees without it" —
        the next representation whose widths differ would otherwise
        reintroduce the family — and it is pinned HERE, structurally,
        rather than left to a behaviour test that cannot fail.
        """
        import inspect

        from vera.wasm.inference import InferenceMixin

        for meth in (
            InferenceMixin._is_pair_type_name,
            InferenceMixin._slot_name_to_wasm_type,
            InferenceMixin._ref_type_name_wasm_type,
            InferenceMixin._canonical_wasm_type,
            InferenceMixin._is_pair_element_type,
        ):
            src = inspect.getsource(meth)
            assert "_declares_adt" in src, (
                f"{meth.__name__} no longer asks the declared-ADT branch"
            )
        codegen_src = inspect.getsource(
            CodeGenerator._type_expr_to_wasm_type)
        assert "classify_named" in codegen_src

    def test_no_element_decider_survives_as_a_free_function(self) -> None:
        """A namer outside the spine is the family's defining shape.

        The five element-layout deciders lived in ``vera/wasm/helpers.py`` as
        module-level functions taking a bare ``str``, so no namespace could
        reach them; that is how the element side went on answering "pair" for
        a declared ``Array`` after every other decider had stopped.  They are
        methods now, and this pins that they stay methods — a future
        module-level layout decider would be the same defect with a new
        name.
        """
        from vera.wasm import helpers

        for name in (
            "_is_pair_element_type", "_element_mem_size", "_element_load_op",
            "_element_store_op", "_element_wasm_type",
        ):
            assert not hasattr(helpers, name), (
                f"{name} is a module-level function again — it decides a "
                f"layout from a bare name, with no namespace to ask"
            )
            assert hasattr(WasmContext, name), name

    @pytest.mark.parametrize(
        "name,expected",
        [("Array", "i32_pair"), ("Map", "i32"), ("Set", "i32"),
         ("Decimal", "i32"), ("Option", "i32"), ("Result", "i32"),
         ("String", "i32_pair"), ("Int", "i64"), ("Nat", "i64"),
         ("Bool", "i32"), ("Byte", "i32"), ("Float64", "f64")],
    )
    def test_an_unshadowed_name_keeps_the_builtin_reading(
        self, name: str, expected: str,
    ) -> None:
        """The control arm: with nothing shadowing the name, the two TOTAL
        derivations agree on the built-in's own width and the pair predicate
        agrees with them.

        Green before AND after the reorder by construction — it is here so
        the relaxation cannot cost the built-in reading it must leave alone.
        """
        answers = self._answers(_shadow_program(_CONTROL_ADT), name)
        assert answers["codegen width"] == expected, answers
        assert answers["wasm canonical width"] == expected, answers
        assert answers["wasm pair predicate"] == (expected == "i32_pair"), (
            answers
        )
        # The element side keeps the built-in reading too, so the guard
        # cannot be satisfied by making every element a pointer.
        assert answers["element pair predicate"] == (expected == "i32_pair"), (
            answers
        )
        assert answers["element mem size"] == {
            "Int": 8, "Nat": 8, "Float64": 8, "Bool": 1, "Byte": 1,
        }.get(name, 8 if expected == "i32_pair" else 4), answers
