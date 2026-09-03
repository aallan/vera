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


import pytest

from vera import ast, naming
from vera.codegen import CodeGenerator, execute
from vera.codegen.api import CompileResult
from vera.naming import AliasEnv, NameSort, classify_named
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


#: The name a `data` declaration may no longer take (#1397, E158): the
#: compiler special-cases their SEMANTICS by name, so a declaration of either
#: cannot be told apart from the built-in.  They stay in the ALIAS battery —
#: `type Tuple = Int;` is still legal and still has to resolve correctly.
_UNDECLARABLE = ("Future",)


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

# Names whose ABILITY dispatch is still keyed on the bare name, measured
# identical at `release/v0.2.0` and here — pre-existing, and NOT reachable by
# the `_declares_adt` guard the `Array` / `Map` / `Set` / `Decimal` / `Future`
# arms use.  Those five names are not registered built-in ADTs, so
# "this namespace declares it" and "it is in `_adt_type_names`" coincide for
# them; `Tuple` IS registered (as are `Option`, `Result`, `Json`, …), so the
# same guard there disables the BUILT-IN path unconditionally — measured:
# `show(Tuple(1, 2))` rendered `Tuple(1, 2)` instead of `(1, 2)`.  Separating
# them needs a per-namespace "declared HERE" set on the wasm side, which is
# the same per-owner keying PR-C3 builds; skipped rather than asserted wrong
# so the cell turns green by itself when that lands.
#: The ability-dispatch residue that remains OPEN (#1397).  `Future` is
#: refused at declaration now (E158), but `Tuple` cannot be: this tree
#: deliberately supports a user `data Tuple` — `vera/wasm/data.py`'s FIX-3
#: discriminates the built-in variadic carrier from it, and
#: `TestFix3UserTupleGate` plus two verifier cells pin that it constructs,
#: verifies and runs.  So the show/eq misbehaviour stays measured and
#: skipped rather than asserted wrong, and turns green by itself when #1397
#: is ruled on.  Identical at `release/v0.2.0`.
_SHOW_RESIDUE: dict[str, str] = {
    "Tuple": (
        "open (#1397): `_composite_ctor_plans` renders a user `data Tuple` "
        "through the built-in variadic-product path, dropping the "
        "constructor name (`(7)`), and Eq is refused (E243) against the "
        "built-in's fields; identical at release/v0.2.0.  Cannot be closed "
        "by reserving the name — this tree supports a user `Tuple` on "
        "purpose (vera/wasm/data.py FIX-3, TestFix3UserTupleGate)"
    ),
}

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
        """
        if name in _SHOW_RESIDUE:
            pytest.skip(_SHOW_RESIDUE[name])
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
        """The structural-Eq arm of the same dispatch."""
        if name in _SHOW_RESIDUE:
            pytest.skip(_SHOW_RESIDUE[name])
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


class TestSpecialCasedBuiltinAdtsAreRefused:
    """#1397 — `data Tuple` / `data Future` are refused at check (E158).

    The spine tells a declared `Array` / `Map` / `Set` / `Decimal` apart from
    the container of that name, which is what #1321/#1331 established.  It
    cannot do that for these two: `Tuple` is registered by
    `_register_builtin_adts` AND rendered through a variadic-product path
    keyed on its name, and `Future` is the transparent wrapper several
    derivations peel before asking what the name means.  Measured at
    `release/v0.2.0`: `show(MkShadowS(7))` under `data Tuple` printed `(7)`,
    dropping the constructor name, and the same program under `data Future`
    compiled to a module that fails to load.

    So the name is refused, on the rule E151 already applies to built-in
    functions and E152 to built-in effects.
    """

    @pytest.mark.parametrize("name", _UNDECLARABLE)
    def test_the_declaration_is_refused(self, name: str) -> None:
        codes = [d.error_code for d in _check(_shadow_program(name))]
        assert "E158" in codes, codes

    @pytest.mark.parametrize("name", _UNDECLARABLE)
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
        """The reservation is exactly two names.

        §8.4.1 makes the prelude's data types ordinary declarations a program
        may shadow, `examples/vera/collections.vera` ships a `public data
        Option<T>`, and #1312's E623 rail is built on entry-file shadowing
        being legal — so widening this would refuse programs the language
        documents as valid.
        """
        assert "E158" not in [
            d.error_code for d in _check(_shadow_program(name))]


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
