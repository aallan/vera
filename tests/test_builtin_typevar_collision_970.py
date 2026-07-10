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
