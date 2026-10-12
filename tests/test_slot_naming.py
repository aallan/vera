"""Rule table for :mod:`vera.naming` — the ONE slot/family naming renderer.

Each test pins one clause of THE RULE (see the module docstring of
``vera/naming.py``) to an EXACT rendered string.  The companion
``test_slot_naming_differential.py`` proves the module agrees with the
checker across the whole corpus; this file states what that agreed-upon
rendering *is*, so a future change to either side has to argue with a
written-down expectation rather than silently re-baseline.
"""

from __future__ import annotations


from vera import ast
from vera.checker.core import TypeChecker
from vera.naming import (
    EMPTY_ALIAS_ENV,
    AliasEnv,
    alias_env_from_environment,
    family_base_name,
    family_name,
    refinement_binder_parts,
    slot_name,
    slot_ref_key,
    type_arg_name,
    with_type_params,
)
from vera.parser import parse_to_ast

from tests.naming_helpers import alias_env_from_declarations
from tests import pipeline

# =====================================================================
# Helpers
# =====================================================================

ALIASES = """\
type MyAlias = Int;
type A2 = MyAlias;
type Box<T> = Option<T>;
type PosT<T> = { @T | @T.0 > 0 };
type Pos = { @Int | @Int.0 > 0 };
type Neg = { @Int | @Int.0 < 0 };
type FnAlias = fn(Int -> Int) effects(pure);
type Count = Nat;
type Composite = Option<Int>;
type BoxedComposite = Box<MyAlias>;
type Txt = String;
type Sized = { @Array<Txt> | array_length(@Array<Txt>.0) > 0 };
type Cyc1 = Cyc2;
type Cyc2 = Cyc1;
type Fwd = Later;
type Later = Int;
"""

_FN = """\
public {forall}fn probe({shape} -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}
"""


def _parse(shape: str, prelude: str = ALIASES, forall: str = "") -> ast.Program:
    return pipeline.parse(prelude + _FN.format(shape=shape, forall=forall)).program


def _probe(
    shape: str, prelude: str = ALIASES, forall: str = "",
) -> tuple[ast.TypeExpr, AliasEnv]:
    """The first parameter's TypeExpr plus the module-scoped naming env."""
    prog = _parse(shape, prelude, forall)
    fn = next(d.decl for d in prog.declarations
              if isinstance(d.decl, ast.FnDecl))
    env = alias_env_from_declarations(prog.declarations)
    if fn.forall_vars:
        env = with_type_params(env, fn.forall_vars)
    return fn.params[0], env


def _name(shape: str, prelude: str = ALIASES, forall: str = "") -> str:
    te, env = _probe(shape, prelude, forall)
    return slot_name(te, env)


def _env(prelude: str = ALIASES) -> AliasEnv:
    return alias_env_from_declarations(pipeline.parse(prelude).program.declarations)


# =====================================================================
# Clause: the head is SYNTACTIC (alias-opaque)
# =====================================================================

def test_bare_head_renders_as_itself() -> None:
    assert _name("@Int") == "Int"


def test_alias_head_stays_opaque() -> None:
    """`@MyAlias` counts MyAlias bindings, not Int bindings."""
    assert _name("@MyAlias") == "MyAlias"
    assert _name("@A2") == "A2"


def test_parameterised_alias_head_stays_opaque() -> None:
    assert _name("@Box<Int>") == "Box<Int>"


# =====================================================================
# Clause: type ARGUMENTS are fully resolved
# =====================================================================

def test_alias_argument_resolves() -> None:
    assert _name("@Option<MyAlias>") == "Option<Int>"


def test_nested_alias_argument_resolves_through_the_chain() -> None:
    assert _name("@Option<A2>") == "Option<Int>"


def test_parameterised_alias_argument_substitutes_then_resolves() -> None:
    assert _name("@Option<Box<MyAlias>>") == "Option<Option<Int>>"


def test_multi_argument_join_matches_the_checkers() -> None:
    assert _name("@Map<MyAlias, Box<A2>>") == "Map<Int, Option<Int>>"


def test_argument_arity_mismatch_renders_unknown() -> None:
    """A partially-applied alias is E133 at check and `?` here."""
    assert _name("@Option<Box>") == "Option<?>"
    assert _name("@Option<Box<Int, Int>>") == "Option<?>"


def test_head_arity_mismatch_still_renders_the_head_syntactically() -> None:
    assert _name("@Box") == "Box"


# =====================================================================
# Clause: refinements
# =====================================================================

def test_refinement_at_top_level_renders_its_base() -> None:
    assert _name("@{ @Int | @Int.0 > 0 }") == "Int"
    # The base is a head, so ITS arguments resolve: `Array<String>`, not the
    # source spelling `Array<Txt>`.  Codegen's refinement binder gives the
    # SAME answer — #1208 made it `slot_name`'s — which is what
    # `test_refinement_binder_names_parameterised_bases_through_slot_name`
    # closes: it asserts the same `Array<String>` and that a predicate's
    # `@Array<Txt>.0` resolves onto it.  (The comment here used to claim the
    # binder still produced the source spelling, and cited a test that does
    # not exist; PR #1224 review.)
    assert _name("@{ @Array<Txt> | array_length(@Array<Txt>.0) > 0 }") \
        == "Array<String>"


def test_refinement_alias_at_top_level_stays_opaque() -> None:
    assert _name("@Pos") == "Pos"


def test_refinement_in_argument_position_renders_the_elided_form() -> None:
    assert _name("@Option<Pos>") == "Option<{@Int | ...}>"


def test_parameterised_refinement_alias_substitutes_before_refining() -> None:
    """Ordering: substitute the alias parameters, THEN take the refinement
    branch — otherwise the binder renders as the un-substituted `{@T | ...}`
    and never matches the instantiated key."""
    assert _name("@Option<PosT<Int>>") == "Option<{@Int | ...}>"
    assert _name("@Option<PosT<MyAlias>>") == "Option<{@Int | ...}>"


# =====================================================================
# Clause: function types
# =====================================================================

def test_function_type_at_top_level_renders_fn() -> None:
    assert _name("@fn(Int -> Int) effects(pure)") == "Fn"


def test_function_type_in_argument_position_renders_in_full() -> None:
    assert _name("@Option<fn(MyAlias -> Int) effects(pure)>") \
        == "Option<fn(Int -> Int) effects(pure)>"


def test_function_type_argument_sorts_its_effect_row() -> None:
    """Written unsorted; rendered sorted, so the name is stable across
    hash seeds (the row is a frozenset)."""
    assert _name("@Option<fn(Int -> Int) effects(<State<Int>, IO>)>") \
        == "Option<fn(Int -> Int) effects(<IO, State<Int>>)>"


# =====================================================================
# Clause: total — the `?` paths
# =====================================================================

def test_decimal_with_arguments_drops_them() -> None:
    """`Decimal` is opaque and non-parameterised (E134 at check); the
    arguments do not reach the name."""
    assert _name("@Option<Decimal<Int>>") == "Option<Decimal>"


def test_removed_alias_renders_unknown_in_argument_position() -> None:
    assert _name("@Option<Float>") == "Option<?>"


def test_removed_alias_head_stays_syntactic() -> None:
    assert _name("@Float") == "Float"


# =====================================================================
# Clause: a DECLARED ADT outranks the special-cased names
# =====================================================================

_ADT_SHADOWS = ALIASES + """\
private data Float { MkFl(Int) }
private data Decimal { MkDec(Int) }
"""


def test_declared_adt_outranks_the_removed_alias_branch() -> None:
    """`private data Float { ... }` checks clean (`Float` is not a primitive,
    only a REMOVED alias), and the checker reaches its data-type branch
    BEFORE its removed-alias branch — so the argument renders `Float`, not
    the `?` the removed-alias branch would give."""
    assert _name("@Option<Float>", prelude=_ADT_SHADOWS) == "Option<Float>"
    assert _name("@Float", prelude=_ADT_SHADOWS) == "Float"


def test_declared_adt_outranks_the_builtin_decimal_branch() -> None:
    """The built-in `Decimal` branch is opaque and DROPS type arguments; a
    user-declared `data Decimal` keeps them, because the data-type branch is
    reached first."""
    assert _name("@Option<Decimal<Int>>", prelude=_ADT_SHADOWS) \
        == "Option<Decimal<Int>>"
    assert _name("@Decimal<Float>", prelude=_ADT_SHADOWS) == "Decimal<Float>"


def test_an_alias_still_outranks_a_same_named_adt() -> None:
    """Alias before data type, as in the checker: both may be declared under
    one name, and an argument resolves to the alias body."""
    prelude = ALIASES + "private data MyAlias { MkMy(Int) }\n"
    assert _name("@Option<MyAlias>", prelude=prelude) == "Option<Int>"


def test_adt_visibility_is_bounded_by_declaration_index() -> None:
    """ADT visibility is bounded by declaration index, exactly as alias
    visibility is — the two registries share ONE index space (#1208).

    An alias body naming a special-cased ADT declared BELOW it resolves
    against the table as it stood when `_register_alias` ran, which did not
    yet hold the ADT: the built-in `Decimal` branch, arguments dropped.  The
    ADT is only reachable from an alias declared AFTER it.  Both directions
    are asserted, because a bound applied in the wrong direction would agree
    with the checker on one ordering and not the other."""
    forward = "type M = Decimal<Int>;\nprivate data Decimal { MkDec(Int) }\n"
    assert _name("@Option<M>", prelude=forward) == "Option<Decimal>"
    backward = "private data Decimal { MkDec(Int) }\ntype M = Decimal<Int>;\n"
    assert _name("@Option<M>", prelude=backward) == "Option<Decimal<Int>>"


def test_removed_alias_adt_visibility_is_bounded_the_same_way() -> None:
    """The mirror spelling of the corner: a `data Float` declared below the
    alias leaves the removed-alias branch reachable (`?`); declared above it,
    the ADT branch wins."""
    forward = "type F = Float;\nprivate data Float { MkFl(Int) }\n"
    assert _name("@Option<F>", prelude=forward) == "Option<?>"
    backward = "private data Float { MkFl(Int) }\ntype F = Float;\n"
    assert _name("@Option<F>", prelude=backward) == "Option<Float>"


def test_adt_visibility_bound_does_not_reach_the_top_level() -> None:
    """The bound applies INSIDE an alias body only.  A slot named directly
    for the ADT renders against the whole table, whatever the declaration
    order — the checker resolves those after registration has finished."""
    forward = "type M = Decimal<Int>;\nprivate data Decimal { MkDec(Int) }\n"
    assert _name("@Option<Decimal<Int>>", prelude=forward) \
        == "Option<Decimal<Int>>"
    assert _name("@Decimal<Int>", prelude=forward) == "Decimal<Int>"


def test_unresolvable_type_expression_renders_question_mark() -> None:
    class _Alien(ast.TypeExpr):
        pass

    assert slot_name(_Alien(), EMPTY_ALIAS_ENV) == "?"
    assert type_arg_name(_Alien(), EMPTY_ALIAS_ENV) == "?"


# =====================================================================
# Clause: type parameters SHADOW aliases
# =====================================================================

def test_type_parameter_shadows_a_same_named_alias() -> None:
    """`type MyAlias = Int` is in scope, but a `forall<MyAlias>` parameter
    of the same name wins — the shadowing test comes first."""
    env = _env()
    te = ast.NamedType(
        name="Option",
        type_args=(ast.NamedType(name="MyAlias", type_args=None),),
    )
    assert slot_name(te, env) == "Option<Int>"
    assert slot_name(te, with_type_params(env, ["MyAlias"])) \
        == "Option<MyAlias>"


def test_type_parameter_argument_renders_as_the_variable() -> None:
    assert _name("@Option<T>", forall="forall<T> ") == "Option<T>"
    assert _name("@T", forall="forall<T> ") == "T"


# =====================================================================
# Clause: alias visibility follows declaration order
# =====================================================================

def test_alias_cycle_terminates_on_the_opaque_placeholder() -> None:
    """`type Cyc1 = Cyc2; type Cyc2 = Cyc1;` — E132 at check.  The renderer
    neither hangs nor raises: an alias body sees only the aliases declared
    before it, so the cycle bottoms out exactly where the checker's
    registration-order resolution bottoms out."""
    assert _name("@Option<Cyc1>") == "Option<Cyc2>"
    assert _name("@Option<Cyc2>") == "Option<Cyc2>"


def test_forward_reference_stays_opaque() -> None:
    """`type Fwd = Later;` is declared before `Later`, so its body resolved
    against a table that did not yet contain `Later`."""
    assert _name("@Option<Fwd>") == "Option<Later>"
    assert _name("@Option<Later>") == "Option<Int>"


def test_deep_alias_chain_resolves_without_a_depth_bound() -> None:
    """The naming walk is bounded by declaration order, not by a depth
    limit, so a 40-deep chain resolves rather than degrading."""
    depth = 40
    chain = f"type L{depth} = Int;\n" + "".join(
        f"type L{i} = L{i + 1};\n" for i in reversed(range(depth))
    )
    assert _name("@Option<L0>", prelude=chain) == "Option<Int>"
    # Declared the other way round, every link is a forward reference and
    # each one stays opaque — the registration-order rule, not a bound.
    forward = "".join(
        f"type F{i} = F{i + 1};\n" for i in range(depth)
    ) + f"type F{depth} = Int;\n"
    assert _name("@Option<F0>", prelude=forward) == "Option<F1>"


# =====================================================================
# Slot-reference keys
# =====================================================================

def test_slot_ref_key_matches_the_binding_side() -> None:
    env = _env()
    ref = ast.SlotRef(
        type_name="Option",
        type_args=(ast.NamedType(name="MyAlias", type_args=None),),
        index=0,
    )
    te, _ = _probe("@Option<MyAlias>")
    assert slot_ref_key(ref, env) == slot_name(te, env) == "Option<Int>"


def test_bare_slot_ref_key_is_the_type_name() -> None:
    ref = ast.SlotRef(type_name="MyAlias", type_args=None, index=2)
    assert slot_ref_key(ref, _env()) == "MyAlias"


def test_slot_ref_key_resolves_nested_alias_arguments() -> None:
    ref = ast.SlotRef(
        type_name="Array",
        type_args=(ast.NamedType(
            name="Option",
            type_args=(ast.NamedType(name="A2", type_args=None),)),),
        index=0,
    )
    assert slot_ref_key(ref, _env()) == "Array<Option<Int>>"


# =====================================================================
# Family names (#1209) — cell identity, not source spelling
# =====================================================================

def _fam(name: str, fallback: str = "FALLBACK") -> str:
    return family_name(
        ast.NamedType(name=name, type_args=None), _env(), fallback)


def _fam_base(name: str, fallback: str = "FALLBACK") -> str:
    return family_base_name(
        ast.NamedType(name=name, type_args=None), _env(), fallback)


def test_family_name_collapses_a_scalar_alias() -> None:
    assert _fam("Count") == "Nat"


def test_family_name_collapses_a_composite_alias() -> None:
    """#1209: `State<Composite>` is the same cell as `State<Option<Int>>`."""
    assert _fam("Composite") == "Option<Int>"


def test_family_name_collapses_a_parameterised_composite_alias() -> None:
    assert _fam("BoxedComposite") == "Option<Int>"
    assert family_name(
        ast.NamedType(
            name="Box",
            type_args=(ast.NamedType(name="A2", type_args=None),)),
        _env(), "FALLBACK") == "Option<Int>"


def test_family_name_keeps_a_refinement_apart_from_its_base() -> None:
    """#1218: a refined cell is its OWN cell, so its family carries the
    predicate.  The checker keeps `State<Pos>` and `State<Int>` apart —
    `EffectInstance` holds the `RefinedType` and E125 refuses to pass one
    where the other is required — so collapsing them to `Int` gave two
    checker cells one host cell."""
    assert _fam("Pos") != "Int"
    assert _fam("Pos").startswith("{Int|")
    assert _fam("Pos") != _fam("Neg")


def test_family_base_name_is_the_refinement_s_base() -> None:
    """The REPRESENTATION half of the same rule (#1218).

    Two refinements of one base are two cells and one width, so the base is
    derived separately rather than recovered from the identity name — every
    decision keyed on `"Nat"`/`"Int"`/`"Byte"`/`"String"` asks this one.
    """
    assert _fam_base("Pos") == "Int"
    assert _fam_base("Neg") == "Int"
    assert _fam_base("Count") == "Nat"
    assert _fam_base("Composite") == "Option<Int>"


def test_family_and_base_agree_about_having_no_family_at_all() -> None:
    """Both halves fall back on exactly the same type expressions, so a
    consumer can never get an identity for a cell whose representation it
    cannot name, or the reverse."""
    for name in ("Float", "FnAlias"):
        assert _fam(name) == "FALLBACK"
        assert _fam_base(name) == "FALLBACK"


def test_family_name_falls_back_when_there_is_no_nameable_family() -> None:
    assert family_name(None, _env(), "FALLBACK") == "FALLBACK"
    assert _fam("Float") == "FALLBACK"  # removed alias -> unresolvable
    fn_te, env = _probe("@fn(Int -> Int) effects(pure)")
    assert family_name(fn_te, env, "FALLBACK") == "FALLBACK"


# =====================================================================
# Refinement binders (codegen's guard derivation, as a pure function)
# =====================================================================

def test_refinement_binder_names_the_base_slot() -> None:
    binder = refinement_binder_parts(
        ast.NamedType(name="Pos", type_args=None), _env())
    assert binder is not None
    assert binder.binder_name == "Int"
    assert not binder.base_is_refinement


def test_refinement_binder_names_parameterised_bases_through_slot_name() -> None:
    """The binder is `slot_name`'s answer (#1208), so it agrees with what a
    predicate's `@Array<Txt>.0` resolves to through `slot_ref_key` and with
    what the checker bound the predicate's binder under.  The pre-
    consolidation derivation named the arguments by SOURCE spelling
    (`Array<Txt>`) and met a reference side that was syntactic too; with both
    resolved they meet here."""
    binder = refinement_binder_parts(
        ast.NamedType(name="Sized", type_args=None), _env())
    assert binder is not None
    assert binder.binder_name == "Array<String>"
    assert binder.binder_name == slot_ref_key(
        ast.SlotRef(
            type_name="Array",
            type_args=(ast.NamedType(name="Txt", type_args=None),),
            index=0,
        ),
        _env(),
    )


def test_refinement_binder_conjoins_the_nat_range() -> None:
    prelude = ALIASES + "type PosCount = { @Count | @Count.0 < 10 };\n"
    binder = refinement_binder_parts(
        ast.NamedType(name="PosCount", type_args=None), _env(prelude))
    assert binder is not None
    assert binder.binder_name == "Count"
    assert isinstance(binder.predicate, ast.BinaryExpr)
    assert binder.predicate.op is ast.BinOp.AND
    lower = binder.predicate.left
    assert isinstance(lower, ast.BinaryExpr) and lower.op is ast.BinOp.GE
    assert lower.left == ast.SlotRef(
        type_name="Count", type_args=None, index=0)


def test_refinement_binder_flags_a_refinement_over_a_refinement() -> None:
    prelude = ALIASES + "type Tiny = { @Pos | @Pos.0 < 10 };\n"
    binder = refinement_binder_parts(
        ast.NamedType(name="Tiny", type_args=None), _env(prelude))
    assert binder is not None
    assert binder.base_is_refinement


def test_refinement_binder_returns_none_for_a_non_refinement() -> None:
    assert refinement_binder_parts(
        ast.NamedType(name="Count", type_args=None), _env()) is None


# =====================================================================
# Environment construction
# =====================================================================

def test_alias_env_from_environment_reads_the_registered_bodies() -> None:
    """The C0 `TypeAliasInfo.body` wiring: a live checker environment
    yields the same naming env the declarations do."""
    src = ALIASES + _FN.format(shape="@Option<MyAlias>", forall="")
    prog = parse_to_ast(src)
    checker = TypeChecker(source=src)
    checker.check_program(prog)
    env = alias_env_from_environment(checker.env)
    assert "MyAlias" in env.aliases
    assert env.alias_params["Box"] == ("T",)
    te = next(d.decl for d in prog.declarations
              if isinstance(d.decl, ast.FnDecl)).params[0]
    assert slot_name(te, env) == "Option<Int>"


def test_alias_env_from_declarations_layers_a_base_underneath() -> None:
    base = _env("type MyAlias = Int;\n")
    layered = alias_env_from_declarations(
        parse_to_ast("type Wrap = Option<MyAlias>;\n").declarations, base)
    assert set(layered.aliases) == {"MyAlias", "Wrap"}
    assert family_name(
        ast.NamedType(name="Wrap", type_args=None), layered, "FB") \
        == "Option<Int>"


def test_empty_alias_env_resolves_nothing() -> None:
    te = ast.NamedType(
        name="Option",
        type_args=(ast.NamedType(name="MyAlias", type_args=None),),
    )
    assert slot_name(te, EMPTY_ALIAS_ENV) == "Option<MyAlias>"


def test_with_type_params_does_not_mutate_its_input() -> None:
    env = _env()
    extended = with_type_params(env, ["MyAlias"])
    assert env.type_params == frozenset()
    assert extended.type_params == frozenset({"MyAlias"})


# =====================================================================
# Clause: TOTAL — no renderer raises, at any legal chain length
# =====================================================================

def _chain_program(hops: int) -> str:
    """``type A0 = Int; type A1 = A0; …`` plus a function naming the top.

    Generated rather than stored: the point is the LENGTH, and a stored
    fixture of this shape is 7 KB of noise.
    """
    lines = ["type A0 = Int;"]
    lines += [f"type A{i} = A{i - 1};" for i in range(1, hops)]
    lines.append(f"""
public fn deep(@Option<A{hops - 1}> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  option_unwrap_or(@Option<A{hops - 1}>.0, 0)
}}
""")
    return "\n".join(lines)


def test_deep_alias_chain_renders_without_recursing_per_hop() -> None:
    """A 400-hop alias chain RESOLVES, rather than raising ``RecursionError``.

    The checker stores each alias's ``resolved_type`` at registration, so its
    own cost is O(1) per hop and a chain this long is a perfectly legal
    program.  The naming module resolved by recursive descent and died at
    ~340 hops — from inside a renderer its own docstring calls TOTAL (#1208
    review, probe ``d01_deep_chain``).

    The assertion is the RENDERING, not merely the absence of a crash: a
    depth bound that answered ``Option<?>`` would also "not raise", and would
    break both the checker-equivalence rule and the 41-hop
    ``ch07_state_alias_chain`` conformance program.
    """
    source = _chain_program(400)
    program = parse_to_ast(source)
    checker = TypeChecker(source=source, file="<deep>")
    checker.check_program(program)
    assert not [d for d in checker.errors if d.severity == "error"]

    fn = next(d.decl for d in program.declarations
              if isinstance(d.decl, ast.FnDecl))
    env = alias_env_from_environment(checker.env)
    assert slot_name(fn.params[0], env) == "Option<Int>"
    # The reference side too — it is the half that silently misses.
    ref = ast.SlotRef(
        type_name="Option",
        type_args=(ast.NamedType(name="A399", type_args=None),),
        index=0,
    )
    assert slot_ref_key(ref, env) == "Option<Int>"


def test_deep_alias_chain_agrees_with_the_checker() -> None:
    """The same chain, compared against the CHECKER's own rendering.

    ``_type_expr_to_slot_name`` delegates to :mod:`vera.naming`, so this is
    the equivalence the depth fix has to preserve: same answer, no truncation.
    """
    source = _chain_program(400)
    program = parse_to_ast(source)
    checker = TypeChecker(source=source, file="<deep>")
    checker.check_program(program)
    fn = next(d.decl for d in program.declarations
              if isinstance(d.decl, ast.FnDecl))
    assert checker._type_expr_to_slot_name(fn.params[0]) == "Option<Int>"


def test_deep_alias_chain_of_composites_renders() -> None:
    """The chain need not be bare names: each hop may WRAP the next.

    ``type A1 = Option<A0>`` grows the resolved type as well as the chain, so
    it exercises the dependency ordering rather than a bare-name fast path.
    Kept shorter than the bare chain because the resulting ``Type`` really is
    that deeply nested, and rendering it is inherently proportional — still
    long enough that the pre-fix per-hop descent overflowed.
    """
    hops = 250
    lines = ["type A0 = Int;"]
    lines += [f"type A{i} = Option<A{i - 1}>;" for i in range(1, hops)]
    source = "\n".join(lines) + f"""
public fn deep(@Box<A{hops - 1}> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}
"""
    # ONE text on both sides: the checker's `source` is what it slices for a
    # diagnostic's `source_line`, so parsing a text one line longer than the
    # one handed to the checker made every span off by one (PR #1283 review).
    source = "type Box<T> = Option<T>;\n" + source
    program = parse_to_ast(source)
    checker = TypeChecker(source=source, file="<deep2>")
    checker.check_program(program)
    assert not [d for d in checker.errors if d.severity == "error"]
    fn = next(d.decl for d in program.declarations
              if isinstance(d.decl, ast.FnDecl))
    env = alias_env_from_environment(checker.env)
    rendered = slot_name(fn.params[0], env)
    assert rendered.startswith("Box<Option<Option<"), rendered[:60]
    assert rendered == checker._type_expr_to_slot_name(fn.params[0])


def _sibling_program(levels: int) -> str:
    """An alias graph whose bodies mention SIBLINGS as well as ancestors.

    Every alias still resolves to ``Int`` (so the resolved type stays O(1) and
    the rendering is a fixed string), but each ``D`` body mentions both ``B``
    and ``C`` at its own level and ``C`` in turn mentions ``B`` — so a
    resolution that puts a whole pending list in progress at once filters
    ``B`` out of ``C``'s dependencies and reaches it by recursing instead
    (#1208 round-2 review, probe ``sib_300``).
    """
    lines = [
        "type Drop<Z> = Int;",
        "type Drop2<Y, Z> = Int;",
        "type B0 = Int;",
        "type C0 = Drop<B0>;",
        "type D0 = Drop2<B0, C0>;",
    ]
    for k in range(1, levels + 1):
        lines += [
            f"type B{k} = D{k - 1};",
            f"type C{k} = Drop<B{k}>;",
            f"type D{k} = Drop2<B{k}, C{k}>;",
        ]
    lines.append(f"""
public fn main(@Option<D{levels}> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  0
}}
""")
    return "\n".join(lines)


def test_sibling_dependency_graph_renders_without_recursing_per_level() -> None:
    """A 300-level sibling-mentioning alias graph RESOLVES (#1208 round 2).

    The chain tests above are a straight line, which the dependency-first
    walk handles however it pushes.  This is the shape that distinguishes the
    two: pushing a body's whole pending list makes SIBLINGS in progress
    together, the ``in_progress`` guard then filters a sibling that is a real
    dependency, and the resolution reaches it through a nested
    ``_resolve_alias`` — one Python frame per level, ``RecursionError`` from a
    renderer this module documents as TOTAL.

    The assertion is the RENDERING, on both the binding and the reference
    side, so a depth bound answering ``Option<?>`` cannot pass either.
    """
    source = _sibling_program(300)
    program = parse_to_ast(source)
    checker = TypeChecker(source=source, file="<sib>")
    checker.check_program(program)
    assert not [d for d in checker.errors if d.severity == "error"]

    fn = next(d.decl for d in program.declarations
              if isinstance(d.decl, ast.FnDecl))
    env = alias_env_from_environment(checker.env)
    assert slot_name(fn.params[0], env) == "Option<Int>"
    assert slot_ref_key(
        ast.SlotRef(
            type_name="Option",
            type_args=(ast.NamedType(name="D300", type_args=None),),
            index=0,
        ),
        env,
    ) == "Option<Int>"
    # And the CHECKER agrees — the equivalence the evaluation order preserves.
    assert checker._type_expr_to_slot_name(fn.params[0]) == "Option<Int>"


def test_sibling_dependency_graph_nests_a_constant_depth() -> None:
    """The structural claim, independent of ``sys.getrecursionlimit()``.

    "Does not raise at N=300" is a threshold test: it passes for an
    implementation that recurses once per level on a machine with a generous
    limit, and it says nothing about N+1.  What the fix actually establishes
    is that ``_resolve_alias`` nests a CONSTANT depth whatever the graph
    size — one frame below the walk, for the memo hit underneath the body
    being resolved — so that is what is asserted here, at a size (1000
    levels) no per-level recursion could reach.
    """
    from vera import naming as naming_module

    source = _sibling_program(1000)
    program = parse_to_ast(source)
    checker = TypeChecker(source=source, file="<sib1k>")
    checker.check_program(program)
    env = alias_env_from_environment(checker.env)

    original = naming_module._resolve_alias
    depth = 0
    max_depth = 0
    calls = 0

    def counting(name: str, alias_env: AliasEnv) -> object:
        nonlocal depth, max_depth, calls
        calls += 1
        depth += 1
        max_depth = max(max_depth, depth)
        try:
            return original(name, alias_env)
        finally:
            depth -= 1

    naming_module._resolve_alias = counting  # type: ignore[assignment]
    try:
        fn = next(d.decl for d in program.declarations
                  if isinstance(d.decl, ast.FnDecl))
        assert slot_name(fn.params[0], env) == "Option<Int>"
    finally:
        naming_module._resolve_alias = original  # type: ignore[assignment]

    # The floor comes FIRST: `max_depth <= 2` is trivially true of a wrapper
    # that never fired at all — a rendering that stopped consulting
    # `_resolve_alias`, or a patch that missed the name the renderer calls,
    # would read as the strongest possible pass (PR #1224 round-3).  One call
    # per level is the floor the walk cannot go below and still have resolved
    # a 1000-level graph.
    assert calls >= 1000, (
        f"the instrumented `_resolve_alias` fired only {calls} times over a "
        "1000-level graph — the depth assertion below is measuring nothing"
    )
    assert max_depth <= 2, (
        f"_resolve_alias nested {max_depth} deep over a 1000-level graph — "
        "the walk is recursing per level again, which is a RecursionError "
        "waiting for a larger program"
    )


def test_alias_with_an_order_entry_but_no_body_falls_through() -> None:
    """An env whose ``_order`` names an alias it has no body for is TOTAL.

    Every environment this module builds keeps the two maps in step, so this
    is insurance rather than a live path — but the branch used to index
    ``env.aliases`` unconditionally, which is a raise inside a renderer
    documented as raising nothing.
    """
    env = AliasEnv(
        aliases={},
        alias_params={"Ghost": None},
        _order={"Ghost": 0},
    )
    assert slot_name(ast.NamedType(name="Ghost", type_args=None), env) == "Ghost"
    assert type_arg_name(
        ast.NamedType(name="Ghost", type_args=None), env) == "Ghost"
