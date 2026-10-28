"""Regression tests for #970 — a user ``forall<T>`` var colliding *by name*
with a built-in generic's internal type-variable name.

Root cause: the inference skip-guard in ``_unify_for_inference``
(``vera/checker/resolution.py``) tests the concrete argument's type-args *by
name* against the callee's ``forall_vars``.  The built-in registry
(``vera/environment.py`` ``_register_builtins``) named its internal generic
vars ``T``/``U``/``A``/``B``/``E``/``K``/``V``, so a user ``forall<T>`` (or
``E``/``A``/``K``/``V``/…) var identical in name aborted unification.

The *filed* bare ``@Array<T>`` repro was masked by a name coincidence (the
unsubstituted param ``Array<T>`` happens to equal the argument ``Array<T>``
when the user's ``T`` and the built-in's ``T`` share a name).  The live defect
surfaces whenever the colliding user var is the **immediate** type-argument of
a *compound* argument type — ``array_length(@Array<Option<T>>.0)`` under a user
``forall<T>`` is rejected with a spurious E202.  It fires across every
generic-builtin family (array/option/result/set/map), every internal registry
name, and in bodies, ``requires``/``ensures`` clauses, and where-helpers.

Fix: alpha-rename every built-in registry internal generic var to a
parser-unwritable form (``T`` → ``T#b``; ``#`` is outside the ``UPPER_IDENT``
grammar ``[A-Z][A-Za-z0-9_]*`` so no user type name can collide, and it avoids
``$`` reserved for fresh inference placeholders).  The skip-guard is unchanged
— after the rename it can no longer match a user name.

Written test-first: every RED below FAILS on the pre-fix compiler with E202
(or, for the differential battery, the collide-variant errors while the
byte-identical control-variant checks clean).  A false *rejection* of
well-typed programs — a completeness defect, never a false accept.
"""

from __future__ import annotations

import dataclasses

import pytest

from vera.ast import AbilityConstraint
from vera.environment import TypeEnv

from tests.checker_helpers import _check_ok, _errors
from tests.verifier_helpers import _verify, _verify_ok


# =====================================================================
# Focused RED unit tests (steps a–d of the fix plan)
# =====================================================================

class TestBuiltinTypevarCollision970:
    """Each test checks/verifies clean AFTER the fix; each fails today."""

    def test_array_length_compound_user_T(self) -> None:
        """(a) ``array_length(@Array<Option<T>>.0)`` under user ``forall<T>``.

        The immediate type-arg of the argument (``Option<T>``) contains the
        colliding user ``T``; today the guard aborts unification and E202
        fires.  The control name (``forall<Z>``) has always checked clean.
        """
        _check_ok(
            "private forall<T> fn f(@Array<Option<T>> -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ array_length(@Array<Option<T>>.0) }\n"
        )

    def test_result_compound_user_E(self) -> None:
        """(b) ``result_unwrap_or`` with ``@Result<Int, Option<E>>`` under
        user ``forall<E>`` — the ``E`` collides with ``result_*``'s internal
        ``E`` (the issue's suggested "rename to E" workaround is itself a
        collision)."""
        _check_ok(
            "private forall<E> fn f(@Result<Int, Option<E>> -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ result_unwrap_or(@Result<Int, Option<E>>.0, 7) }\n"
        )

    def test_map_compound_user_K_V(self) -> None:
        """(c) ``map_size`` with ``@Map<K, Option<V>>`` under user
        ``forall<K, V>`` — the K/V collide with ``map_*``'s internal K/V."""
        _check_ok(
            "private forall<K, V> fn f(@Map<K, Option<V>> -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ map_size(@Map<K, Option<V>>.0) }\n"
        )

    def test_verify_result_compound_user_E(self) -> None:
        """(d) verify-path pin: the ``E``-collision compound shape must both
        *check* and *verify* clean under user ``forall<E>``, with a
        ``result_unwrap_or`` call inside an ``ensures`` clause.

        Today it fails ``check`` (E202) — which in the real ``vera verify``
        pipeline gates the verifier — so the whole check→verify path is
        broken; the byte-identical control name (``forall<Z>``) sails
        through.  The ``_check_ok`` assertion is what is RED today
        (``_verify`` drops check diagnostics, so ``_verify_ok`` alone would
        miss it); the ``_verify_ok`` then pins that the healed shape reaches
        the verifier and discharges without a new error or crash.
        """
        src = (
            "private forall<E> fn f(@Result<Int, Option<E>> -> @Int)\n"
            "  requires(true)\n"
            "  ensures(@Int.result == result_unwrap_or("
            "@Result<Int, Option<E>>.0, 7))\n"
            "  effects(pure)\n"
            "{ result_unwrap_or(@Result<Int, Option<E>>.0, 7) }\n"
        )
        _check_ok(src)   # RED today: E202 from the E/result_* collision.
        _verify_ok(src)  # And the healed shape verifies with no new error.


# =====================================================================
# The differential battery — collide-name variant vs control-name variant,
# otherwise byte-identical.  Reconstructed from the evidence comment on #970.
# After the fix EVERY pair MATCHES (both check clean); each compound-shape
# collide variant is RED (E202) today.
# =====================================================================

def _fn(forall: str, sig: str, body: str, *, req: str = "true",
        ens: str = "true", where: str = "") -> str:
    return (
        f"private forall<{forall}> fn f({sig})\n"
        f"  requires({req})\n"
        f"  ensures({ens})\n"
        f"  effects(pure)\n"
        f"{{ {body} }}\n"
        f"{where}"
    )


# Each entry: (id, source_using_var_names).  ``{a}`` / ``{b}`` are the type
# variable names; the collide row substitutes the built-in's internal names,
# the control row substitutes guaranteed-non-colliding ones.
_SHAPES: list[tuple[str, str]] = [
    # -- Compound element type: the LIVE defect (collide variant E202 today) --
    ("array_length",
     _fn("{a}", "@Array<Option<{a}>> -> @Int",
         "array_length(@Array<Option<{a}>>.0)")),
    ("array_concat",
     _fn("{a}", "@Array<Option<{a}>> -> @Array<Option<{a}>>",
         "array_concat(@Array<Option<{a}>>.0, @Array<Option<{a}>>.0)")),
    ("array_reverse",
     _fn("{a}", "@Array<Option<{a}>> -> @Array<Option<{a}>>",
         "array_reverse(@Array<Option<{a}>>.0)")),
    ("array_append",
     _fn("{a}", "@Array<Option<{a}>>, @Option<{a}> -> @Array<Option<{a}>>",
         "array_append(@Array<Option<{a}>>.0, @Option<{a}>.0)")),
    ("option_unwrap_or",
     _fn("{a}", "@Option<Option<{a}>>, @Option<{a}> -> @Option<{a}>",
         "option_unwrap_or(@Option<Option<{a}>>.0, @Option<{a}>.0)")),
    ("set_to_array",
     _fn("{a}", "@Set<Option<{a}>> -> @Array<Option<{a}>>",
         "set_to_array(@Set<Option<{a}>>.0)")),
    ("array_fold",  # built-in vars T, U
     _fn("{a}", "@Array<Option<{a}>> -> @Int",
         "array_fold(@Array<Option<{a}>>.0, 0, "
         "fn(@Int, @Option<{a}> -> @Int) effects(pure) { @Int.0 })")),
    # -- Contract-clause and where-helper positions (still compound) --
    ("requires_clause",
     _fn("{a}", "@Array<Option<{a}>> -> @Int",
         "array_length(@Array<Option<{a}>>.0)",
         req="array_length(@Array<Option<{a}>>.0) >= 0")),
    ("ensures_clause",
     _fn("{a}", "@Array<Option<{a}>> -> @Int",
         "array_length(@Array<Option<{a}>>.0)",
         ens="@Int.result == array_length(@Array<Option<{a}>>.0)")),
    ("where_helper",
     _fn("{a}", "@Array<Option<{a}>> -> @Int",
         "helper(@Array<Option<{a}>>.0)",
         where=(
             "where {\n"
             "  fn helper(@Array<Option<{a}>> -> @Int)\n"
             "    requires(true)\n"
             "    ensures(true)\n"
             "    effects(pure)\n"
             "  {{ array_length(@Array<Option<{a}>>.0) }}\n"
             "}\n"))),
    # -- Bare element type: MASKED today (both variants already clean); the
    #    fix must keep them clean. --
    ("array_length_bare",
     _fn("{a}", "@Array<{a}> -> @Int", "array_length(@Array<{a}>.0)")),
    ("set_size_bare",
     _fn("{a}", "@Set<{a}> -> @Int", "set_size(@Set<{a}>.0)")),
    # -- Deep non-fire boundary (MT1): user var NOT the immediate type-arg —
    #    guard never fired even pre-fix, both variants clean. --
    ("array_length_deep",
     _fn("{a}", "@Array<Option<Array<{a}>>> -> @Int",
         "array_length(@Array<Option<Array<{a}>>>.0)")),
]

# array_map uses built-in vars A, B — a *different* internal name than T.
_SHAPE_MAP_AB = (
    "array_map",
    _fn("{a}", "@Array<Option<{a}>> -> @Array<Bool>",
        "array_map(@Array<Option<{a}>>.0, "
        "fn(@Option<{a}> -> @Bool) effects(pure) { true })"),
)

# PR #982 review: two more collide rows keyed on the compound-arg shape of a
# *callback*'s own type — the callback ties the user var to the built-in's
# callback-return / accumulator internal var, not to the element var.

# array_map's callback RETURN var is B — a user forall<B> collides *there*
# (the callback returns @Option<B>, whose immediate type-arg is the user B).
_SHAPE_MAP_CALLBACK_B = (
    "array_map_callback_B",
    _fn("{a}", "@Array<Int> -> @Array<Option<{a}>>",
        "array_map(@Array<Int>.0, "
        "fn(@Int -> @Option<{a}>) effects(pure) { None })"),
)

# array_fold's ACCUMULATOR var is U — a user forall<U> collides there (the
# accumulator @Option<U> and the callback's @Option<U> params/return carry U
# as their immediate type-arg).
_SHAPE_FOLD_ACC_U = (
    "array_fold_accumulator_U",
    _fn("{a}", "@Array<Int>, @Option<{a}> -> @Option<{a}>",
        "array_fold(@Array<Int>.0, @Option<{a}>.0, "
        "fn(@Option<{a}>, @Int -> @Option<{a}>) effects(pure) "
        "{ @Option<{a}>.0 })"),
)

# Two-parameter Map shapes — collide on K and V, control on X and Y.
_SHAPE_MAP_KV = (
    "map_size_kv",
    _fn("{a}, {b}", "@Map<{a}, Option<{b}>> -> @Int",
        "map_size(@Map<{a}, Option<{b}>>.0)"),
)
_SHAPE_MAP_KV2 = (
    "map_size_vk",
    _fn("{a}, {b}", "@Map<Option<{a}>, {b}> -> @Int",
        "map_size(@Map<Option<{a}>, {b}>.0)"),
)

# result_* collide on E, control on Z.
_SHAPE_RESULT_E = (
    "result_unwrap_or",
    _fn("{a}", "@Result<Int, Option<{a}>> -> @Int",
        "result_unwrap_or(@Result<Int, Option<{a}>>.0, 7)"),
)


def _pairs() -> list[tuple[str, str, str]]:
    """Yield (id, collide_source, control_source) for the whole battery."""
    out: list[tuple[str, str, str]] = []
    # Single-var families keyed on T (control: Z).
    for name, tmpl in _SHAPES:
        out.append((name,
                    tmpl.replace("{a}", "T"),
                    tmpl.replace("{a}", "Z")))
    # array_map keyed on A (control: Z) — a non-T internal name.
    name, tmpl = _SHAPE_MAP_AB
    out.append((name, tmpl.replace("{a}", "A"), tmpl.replace("{a}", "Z")))
    # array_map keyed on B — the callback-RETURN internal var (control: Z).
    name, tmpl = _SHAPE_MAP_CALLBACK_B
    out.append((name, tmpl.replace("{a}", "B"), tmpl.replace("{a}", "Z")))
    # array_fold keyed on U — the accumulator internal var (control: Z).
    name, tmpl = _SHAPE_FOLD_ACC_U
    out.append((name, tmpl.replace("{a}", "U"), tmpl.replace("{a}", "Z")))
    # result_* keyed on E (control: Z).
    name, tmpl = _SHAPE_RESULT_E
    out.append((name, tmpl.replace("{a}", "E"), tmpl.replace("{a}", "Z")))
    # Map families keyed on K, V (control: X, Y).
    for name, tmpl in (_SHAPE_MAP_KV, _SHAPE_MAP_KV2):
        collide = tmpl.replace("{a}", "K").replace("{b}", "V")
        control = tmpl.replace("{a}", "X").replace("{b}", "Y")
        out.append((name, collide, control))
    return out


_BATTERY = _pairs()


@pytest.mark.parametrize("case", _BATTERY, ids=[c[0] for c in _BATTERY])
def test_battery_collide_matches_control(case: tuple[str, str, str]) -> None:
    """Collide-name and control-name variants must check identically (both
    clean).  RED today for every compound-shape collide variant (E202)."""
    _name, collide_src, control_src = case
    control_errs = _errors(control_src)
    assert control_errs == [], (
        "control variant should always check clean, got: "
        f"{[e.description for e in control_errs]}"
    )
    collide_errs = _errors(collide_src)
    assert collide_errs == [], (
        "collide-name variant must match the control (no spurious E202), "
        f"got: {[e.description for e in collide_errs]}"
    )


# =====================================================================
# PR #982 review round — the namespacing marker must never surface in a
# user-facing diagnostic, the registry must stay self-consistent, and the
# dual completeness gap is pinned in BOTH argument orders.
# =====================================================================

def _no_marker_anywhere(diag: object) -> None:
    """Assert the built-in namespacing marker leaks into NO string field."""
    for field in dataclasses.fields(diag):
        value = getattr(diag, field.name)
        if isinstance(value, str):
            assert "#b" not in value, (
                f"marker leaked into {field.name}={value!r}"
            )


class TestMarkerNeverLeaks982:
    """The ``#b`` namespacing marker (#970) is an internal, parser-unwritable
    form; it must never reach a user-facing diagnostic field."""

    def test_e205_conflict_message_strips_marker(self) -> None:
        """E205 marker-leak pin.  ``array_concat`` (internal var ``T``) called
        with ``[Some(1)]`` and ``[Some(true)]`` fixes its ``T`` to both
        ``Option<Int>`` and ``Option<Bool>`` — a genuine E205 conflict whose
        message names the parameter.

        RED before the strip (``calls.py``): the description reads
        ``... parameter(s) T#b ...`` and ``#b`` leaks into a user-facing
        field.
        """
        errs = _errors(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Array<Option<Int>> = "
            "array_concat([Some(1)], [Some(true)]);\n"
            "  0\n"
            "}\n"
        )
        e205 = [e for e in errs if e.error_code == "E205"]
        assert e205, (
            f"expected an E205 conflict, got {[e.error_code for e in errs]}"
        )
        # The parameter is named T, not T#b.
        assert "parameter(s) T of" in e205[0].description, e205[0].description
        for e in errs:
            _no_marker_anywhere(e)

    def test_e202_expected_type_strips_marker(self) -> None:
        """``pretty_type`` strip pin.  An E202 argument-type-mismatch against a
        built-in generic renders the expected type with the marker stripped —
        ``Array<T>``, not ``Array<T#b>``.  ``array_length`` expects
        ``@Array<T>``; passing ``@Int.0`` mismatches.

        RED: revert ``pretty_type``'s ``TypeVar`` arm to ``ty.name`` — the
        expected type then prints ``Array<T#b>``.
        """
        errs = _errors(
            "public fn f(@Int -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ array_length(@Int.0) }\n"
        )
        e202 = [e for e in errs if e.error_code == "E202"]
        assert e202, f"expected an E202, got {[e.error_code for e in errs]}"
        assert "Array<T>" in e202[0].description, e202[0].description
        for e in errs:
            _no_marker_anywhere(e)


def test_registry_constraint_typevars_are_forall_members() -> None:
    """Registry-consistency pin.  After the #970 namespacing rename, every
    built-in signature's ability-constraint ``type_var`` must still be a
    member of that signature's ``forall_vars``.

    RED before the constraint rename (``environment.py``): the ``map_*`` /
    ``set_*`` families carry ``forall_vars=('K#b','V#b')`` while their
    constraints still read ``[('Eq','K'),('Hash','K')]`` — the pre-rename
    name — so ``type_var`` is no longer a member (a latent unsound
    constraint-skip trap).
    """
    env = TypeEnv()
    offenders: list[tuple[str, str, str, tuple[str, ...]]] = []
    for name, info in env.functions.items():
        if not info.forall_vars:
            continue
        members = set(info.forall_vars)
        for c in info.forall_constraints:
            if isinstance(c, AbilityConstraint) and c.type_var not in members:
                offenders.append(
                    (name, c.ability_name, c.type_var, info.forall_vars)
                )
    assert offenders == [], (
        "a constraint type_var is not a member of its signature's "
        f"forall_vars: {offenders}"
    )


class TestDualGapBothOrders982:
    """The dual completeness gap — a concrete argument resolving a bare type
    variable that leaked unresolved from a nested generic call — pinned in
    BOTH argument orders."""

    def test_dual_gap_leak_first(self) -> None:
        """(a) leak-first — the leaked bare var arrives BEFORE the concrete.

        A user-defined ``forall<T> fn n(@Unit -> @Option<T>) { None }`` leaves
        ``T`` unresolved, so ``option_unwrap_or(n(()), 11)`` binds the callee's
        parameter to ``n``'s escaped ``T`` first, then ``11`` pins it to
        ``Int``.  The concrete-wins ``elif`` in ``_unify_for_inference``
        (``vera/checker/resolution.py``) resolves it.

        RED: delete that ``elif`` and this program is rejected with ``E170``
        (`Let binding expects Int, value has type T`) — confirmed by
        hand-mutation during the #982 review.
        """
        _check_ok(
            "private forall<T> fn n(@Unit -> @Option<T>)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ None }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Int = option_unwrap_or(n(()), 11);\n"
            "  @Int.0\n"
            "}\n"
        )

    def test_dual_gap_concrete_first(self) -> None:
        """(b) concrete-first — the concrete arrives BEFORE the leaked bare var.

        ``array_concat([1, 2, 3], empty_arr(()))`` pins the callee's ``T`` to
        ``Int`` from ``[1, 2, 3]`` first, then meets the escaped ``T`` of a
        user-defined ``forall<T> fn empty_arr(@Unit -> @Array<T>) { [] }``.

        This order is healed by the **#898 merge branch** (position-wise merge
        of a concrete against a bare var), NOT by the #970 concrete-wins
        ``elif`` — deleting that ``elif`` leaves this case GREEN.  It therefore
        pins order-agreement (both orders accept), not the ``elif`` itself.
        """
        _check_ok(
            "private forall<T> fn empty_arr(@Unit -> @Array<T>)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{ [] }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            "{\n"
            "  let @Array<Int> = array_concat([1, 2, 3], empty_arr(()));\n"
            "  array_length(@Array<Int>.0)\n"
            "}\n"
        )


def test_a12_result_bare_tier_split_matches_control() -> None:
    """A12 tier pin.  A bare ``@Result<Int, E>`` under a user ``forall<E>``
    (colliding with ``result_*``'s internal ``E``) must reach the verifier
    with the SAME tier split as the control ``forall<Z>`` — the #970 rename
    must not perturb which obligations discharge at Tier 1.

    Bare-element shapes were already masked pre-fix (both variants check
    clean), so this pins tier-split *equality* against a future re-divergence
    rather than the rename itself.  Both sides are equal today
    (``tier1=2, tier3=0``); a divergence on either side fails the assert.
    """
    def src(v: str) -> str:
        return (
            f"private forall<{v}> fn f(@Result<Int, {v}> -> @Int)\n"
            "  requires(true)\n"
            "  ensures(true)\n"
            "  effects(pure)\n"
            f"{{ result_unwrap_or(@Result<Int, {v}>.0, 7) }}\n"
        )

    collide = _verify(src("E")).summary
    control = _verify(src("Z")).summary
    assert (collide.tier1_verified, collide.tier3_runtime) == (
        control.tier1_verified, control.tier3_runtime
    ), f"tier split diverged: collide={collide} control={control}"


# =====================================================================
# #1069 — the STRIPPED marker still leaks a bare type var into a mismatch
# message.  #982 stopped the raw ``#b`` marker from surfacing; but a built-in
# generic var that inference never substituted (``map_values``'s element var
# ``V#b`` over a ``map_new()`` nothing fixes) is stripped to a bare ``V``
# and printed as if it were a real, user-meaningful type ("body has type V").
# The fix renders such a leaked internal placeholder as ``?`` at the
# *actual*-type slot of every mismatch message, while leaving a genuine user
# ``forall`` var (plain ``T``) and a built-in's unsubstituted *expected*
# signature (``Array<T>`` — TestMarkerNeverLeaks982) untouched.
# =====================================================================

# The leak vehicle: ``map_values(map_new())`` is ``Array<V#b>``, a type
# nothing determines (no argument and no context fixes ``map_new()``'s
# ``V``), so indexing it yields the bare, unsubstituted ``V#b``.  It was
# ``map_values(@M.0)`` over the refinement alias below until #1688's fix,
# which binds ``V`` from the refinement's base, ``Int``: read through the
# alias the variable was never undetermined, and that leak was #1688 itself
# (``get_val(@M -> @Int) { map_values(@M.0)[0] }``, a correct program, was
# refused with E121; tests/test_fits_one_variable_one_type_1684.py's #1688
# cells pin the fix).  The alias stays because the cells' signatures take an
# ``@M``.
_M_ALIAS = (
    "type M = { @Map<String, Int> | map_size(@Map<String, Int>.0) >= 0 };\n"
)


def _diag(source: str, code: str) -> str:
    """Return the description of the first diagnostic with ``error_code``."""
    errs = _errors(source)
    hits = [e for e in errs if e.error_code == code]
    assert hits, (
        f"expected a {code}, got "
        f"{[(e.error_code, e.description) for e in errs]}"
    )
    return hits[0].description


class TestLeakedTypevarMessage1069:
    """Every reachable mismatch site renders a leaked built-in placeholder var
    as ``?`` rather than a bare stripped letter.

    RED on the pre-fix compiler: each ``has type ?`` assertion fails because
    the message reads ``has type V`` (``pretty_type`` stripped ``V#b`` to
    ``V``).  ``Int``/``Bool`` (expected) and ``?`` (corrected actual) and
    ``V`` (leaked) are mutually distinct in every shape, so the assertions
    cannot pass by coincidence.
    """

    def test_e121_function_body(self) -> None:
        """E121 — the reported repro.  Body ``map_values(map_new())[0]`` is a bare
        leaked ``V``; the declared return is ``Int``."""
        desc = _diag(
            _M_ALIAS
            + "public fn get_val(@M -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ map_values(map_new())[0] }\n",
            "E121",
        )
        assert "body has type ?, expected Int" in desc, desc
        assert "type V" not in desc, desc

    def test_e170_let_value_nested(self) -> None:
        """E170 — a NESTED leak (``Array<V>``) proves the substitution recurses
        into type arguments: the corrected render is ``Array<?>``."""
        desc = _diag(
            _M_ALIAS
            + "public fn f(@M -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ let @Bool = map_values(map_new()); @Bool.0 }\n",
            "E170",
        )
        assert "value has type Array<?>" in desc, desc
        assert "Array<V>" not in desc, desc

    def test_e171_anonymous_function_body(self) -> None:
        """E171 — a leaked ``V`` at a closure's body position."""
        desc = _diag(
            _M_ALIAS
            + "public fn f(@M -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ apply_fn(fn(@M -> @Bool) effects(pure) "
            "{ map_values(map_new())[0] }, @M.0) }\n",
            "E171",
        )
        assert "body has type ?, expected Bool" in desc, desc
        assert "type V" not in desc, desc

    def test_e213_constructor_field(self) -> None:
        """E213 — a leaked ``V`` at a constructor-argument position."""
        desc = _diag(
            "private data Box { MkBox(Bool) }\n"
            + _M_ALIAS
            + "public fn f(@M -> @Box)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ MkBox(map_values(map_new())[0]) }\n",
            "E213",
        )
        assert "field 0 has type ?, expected Bool" in desc, desc
        assert "type V" not in desc, desc

    def test_e204_effect_operation_argument(self) -> None:
        """E204 — a leaked ``V`` at an effect-operation argument position."""
        desc = _diag(
            "effect Sig { op emit(Bool -> Unit); }\n"
            + _M_ALIAS
            + "private fn f(@M -> @Unit)\n"
            "  requires(true) ensures(true) effects(<Sig>)\n"
            "{ emit(map_values(map_new())[0]) }\n",
            "E204",
        )
        assert "has type ?, expected Bool" in desc, desc
        assert "type V" not in desc, desc

    def test_e241_ability_operation_argument(self) -> None:
        """E241 — a leaked ``V`` at an ability-operation argument position
        (the structural twin of the effect-operation arm)."""
        desc = _diag(
            "ability Emitter<T> { op emit(Bool -> Unit); }\n"
            + _M_ALIAS
            + "private forall<T where Emitter<T>> fn f(@T, @M -> @Unit)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ emit(map_values(map_new())[0]) }\n",
            "E241",
        )
        assert "has type ?, expected Bool" in desc, desc
        assert "type V" not in desc, desc

    def test_e202_apply_fn_argument(self) -> None:
        """E202 — a leaked ``V`` at an ``apply_fn`` trailing-argument position
        (the direct-call arm resolves the var by unifying it with the expected
        parameter, so the leak only surfaces through ``apply_fn``)."""
        desc = _diag(
            "type BoolToInt = fn(Bool -> Int) effects(pure);\n"
            + _M_ALIAS
            + "public fn f(@BoolToInt, @M -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ apply_fn(@BoolToInt.0, map_values(map_new())[0]) }\n",
            "E202",
        )
        assert "has type ?, expected Bool" in desc, desc
        assert "type V" not in desc, desc

    def test_e331_handler_state_init(self) -> None:
        """E331 — a leaked ``V`` at a handler's initial-state position."""
        desc = _diag(
            _M_ALIAS
            + "public fn probe(@M -> @Bool)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  handle[State<Bool>](@Bool = map_values(map_new())[0]) {\n"
            "    get(@Unit) -> { resume(@Bool.0) },\n"
            "    put(@Bool) -> { resume(()) }\n"
            "  } in { get(()) }\n"
            "}\n",
            "E331",
        )
        assert "initial value has type ?, expected Bool" in desc, desc
        assert "type V" not in desc, desc

    def test_e335_handler_state_update(self) -> None:
        """E335 — a leaked ``V`` at a ``with`` state-update position."""
        desc = _diag(
            _M_ALIAS
            + "public fn probe(@M -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{\n"
            "  handle[State<Int>](@Int = 0) {\n"
            "    get(@Unit) -> { resume(@Int.0) },\n"
            "    put(@Int) -> { resume(()) } with @Int = map_values(map_new())[0]\n"
            "  } in { get(()) }\n"
            "}\n",
            "E335",
        )
        assert "has type ?, expected Int" in desc, desc
        assert "type V" not in desc, desc

    def test_genuine_user_forall_var_is_preserved(self) -> None:
        """Guard against over-broadening: a genuine *user* ``forall<T>`` var is
        the spelling the programmer wrote, so it stays ``T`` — only namespaced
        built-in (``#b``) and fresh (``$``) placeholders become ``?``.

        Green both before and after the fix (a regression guard, not a
        RED→GREEN): the fix must not touch this message."""
        desc = _diag(
            "private forall<T> fn f(@T -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @T.0 }\n",
            "E121",
        )
        assert "body has type T, expected Int" in desc, desc
        assert "?" not in desc, desc


_V = "map_values(map_new())[0]"

_PURE_FN = (
    "public fn f(@M -> @{ret})\n"
    "  requires(true) ensures(true) effects(pure)\n"
    "{{ {body} }}\n"
)


def _fn(ret: str, body: str) -> str:
    return _M_ALIAS + _PURE_FN.format(ret=ret, body=body)


# An `if` fills a built-in's variable that no parameter mentions from its
# other branch (#1668's join), so ``map_values(map_new())`` makes no E301.
# The E301 rows take a variable a parameter mentions and the arguments
# leave unbound: ``array_map``'s ``B`` beside a refinement of a function
# type, which its function-typed parameter does not unify through (an E202
# of its own sits beside each, an instance of #1684's class).
_FOO_ALIAS = "type Foo = { @fn(Int -> Int) effects(pure) | true };\n"
_LOST = "array_map([1], @Foo.0)[0]"


def _fn_lost(ret: str, body: str) -> str:
    return _FOO_ALIAS + _PURE_FN.replace("@M", "@Foo").format(
        ret=ret, body=body)


# One row per converted render slot: (error code, source, corrected
# fragment that must appear, leaked fragment that must not).  The two-slot
# operator messages (E140/E142/E143/E301) get one row per slot — leak on
# the left and leak on the right pin each operand's render independently.
_SIBLING_SITES = [
    pytest.param(
        "E140", _fn("Int", f"{_V} + 1"),
        "found ? and Int", "found V and", id="E140-arith-left"),
    pytest.param(
        "E140", _fn("Int", f"1 + {_V}"),
        "found Int and ?", "and V.", id="E140-arith-right"),
    pytest.param(
        "E142", _fn("Bool", f"{_V} == 1"),
        "Cannot compare ? with Int", "compare V with", id="E142-eq-left"),
    pytest.param(
        "E142", _fn("Bool", f"1 == {_V}"),
        "Cannot compare Int with ?", "with V.", id="E142-eq-right"),
    pytest.param(
        "E143", _fn("Bool", f"{_V} < 1"),
        "found ? and Int", "found V and", id="E143-ord-left"),
    pytest.param(
        "E143", _fn("Bool", f"1 < {_V}"),
        "found Int and ?", "and V.", id="E143-ord-right"),
    pytest.param(
        "E144", _fn("Bool", f"{_V} && true"),
        "must be Bool, found ?", "found V.", id="E144-logical-left"),
    pytest.param(
        "E145", _fn("Bool", f"true && {_V}"),
        "must be Bool, found ?", "found V.", id="E145-logical-right"),
    pytest.param(
        "E146", _fn("Bool", f"!{_V}"),
        "requires Bool operand, found ?", "found V.", id="E146-not"),
    pytest.param(
        "E147", _fn("Int", f"-{_V}"),
        "requires numeric operand, found ?", "found V.", id="E147-neg"),
    pytest.param(
        "E148", _fn("String", f'"x \\({_V})"'),
        "Type '?' cannot be automatically converted",
        "Type 'V'", id="E148-interpolation"),
    pytest.param(
        "E160",
        _M_ALIAS
        + "public fn f(@Array<Int>, @M -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ @Array<Int>.0[{_V}] }}\n",
        "must be Int or Nat, found ?", "found V.", id="E160-index-type"),
    pytest.param(
        "E161", _fn("Int", f"{_V}[0]"),
        "Cannot index ?:", "Cannot index V:", id="E161-cannot-index"),
    pytest.param(
        "E172", _fn("Bool", f"assert({_V}); true"),
        "assert() requires Bool, found ?", "found V.", id="E172-assert"),
    pytest.param(
        "E173", _fn("Bool", f"assume({_V}); true"),
        "assume() requires Bool, found ?", "found V.", id="E173-assume"),
    pytest.param(
        "E300", _fn("Int", f"if {_V} then {{ 1 }} else {{ 2 }}"),
        "If condition must be Bool, found ?", "found V.", id="E300-if-cond"),
    pytest.param(
        "E301", _fn_lost("Int", f"if true then {{ {_LOST} }} else {{ 2 }}"),
        "then-branch is ?, else-branch is Int",
        "then-branch is V", id="E301-then-branch"),
    pytest.param(
        "E301", _fn_lost("Int", f"if true then {{ 2 }} else {{ {_LOST} }}"),
        "then-branch is Int, else-branch is ?",
        "else-branch is V", id="E301-else-branch"),
    pytest.param(
        "E123",
        _M_ALIAS
        + "public fn f(@M -> @Int)\n"
        f"  requires({_V}) ensures(true) effects(pure)\n"
        "{ 1 }\n",
        "requires() predicate must be Bool, found ?",
        "found V.", id="E123-requires"),
    pytest.param(
        "E124",
        _M_ALIAS
        + "public fn f(@M -> @Int)\n"
        f"  requires(true) ensures({_V}) effects(pure)\n"
        "{ 1 }\n",
        "ensures() predicate must be Bool, found ?",
        "found V.", id="E124-ensures"),
    pytest.param(
        "E126",
        _M_ALIAS
        + f"type Z = {{ @M | {_V} }};\n"
        "public fn f(@Z -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 1 }\n",
        "Refinement predicate must be Bool, found ?",
        "found V.", id="E126-refinement-pred"),
]


class TestLeakedTypevarSiblingSites1069:
    """PR #1088's adversarial review: the same leaked-placeholder masquerade
    survived at the operator / unary / index / interpolation / assert /
    if-and-branch / contract-and-refinement-predicate actual-type slots.
    Every reachable slot renders ``?``, exactly like the mismatch sites.

    RED on the pre-round compiler: each corrected fragment fails because the
    message spells the leak as a bare ``V``.  Sites a leaked var provably
    cannot reach keep plain ``pretty_type`` and are NOT pinned here: E141 /
    the E142 ordering-compatibility arm (operands proven numeric/orderable
    first), E302 (``is_subtype`` accepts a TypeVar arm), the ``==`` Eq-ability
    message (``contains_typevar`` early-return), apply_fn's arity message
    (fn value proven a FunctionType), and the data-invariant message
    (``invariant`` in ``data`` is grammar-rejected, #686).
    """

    @pytest.mark.parametrize(("code", "src", "good", "bad"), _SIBLING_SITES)
    def test_leaked_var_renders_unknown(
            self, code: str, src: str, good: str, bad: str) -> None:
        desc = _diag(src, code)
        assert good in desc, desc
        assert bad not in desc, desc

    def test_e301_fix_text_renders_unknown(self) -> None:
        """E301's fix field interpolates the else-branch's inferred type; a
        leaked var there masquerades the same way the description did."""
        errs = _errors(_fn_lost(
            "Int", f"if true then {{ 2 }} else {{ {_LOST} }}"))
        fixes = [e.fix for e in errs if e.error_code == "E301"]
        assert fixes and fixes[0] is not None, errs
        assert "convert one branch to ?" in fixes[0], fixes[0]
        assert "branch to V" not in fixes[0], fixes[0]
