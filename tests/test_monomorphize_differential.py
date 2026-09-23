"""#732 differential soundness test for per-monomorphization verification.

Per-monomorphization static verification is sound only if the verifier checks
EVERY concrete instantiation codegen actually emits.  If the verifier's
instantiation discovery missed one, a monomorphized clone would run at runtime
whose contract was never statically checked — a false Tier-1, the forbidden
silent failure.

This test runs BOTH discoveries on the same programs and asserts the verifier's
set covers codegen's:

* name coverage — every generic codegen emits at least one instantiation of is
  also discovered by the verifier (catches a missed prelude generic, the #1
  parity risk);
* per-instantiation coverage — every concrete ``(name, types)`` codegen emits is
  discovered by the verifier (after normalizing the verifier's more-precise
  scalars through codegen's WAT collapse), so the right COUNT with the wrong
  tuples can't false-pass.

The verifier deliberately uses MORE precise type names than codegen (``Nat``
where codegen WAT-collapses to ``Int``), so it may *split* a codegen
instantiation into several — never merge — which is why coverage is one-directional
(verifier ⊇ codegen) rather than exact equality.  That extra precision is sound:
the verifier checks each body under the type the checker proved actually flows.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

from vera.codegen.core import CodeGenerator
from vera.monomorphize import Monomorphizer
from vera.parser import parse_file
from vera.resolver import ModuleResolver
from vera.transform import transform
from vera.verifier import ContractVerifier

from tests.module_fixture_helpers import resolved_module as _resolved_module

_REPO_ROOT = Path(__file__).resolve().parent.parent

# Real, known-good programs that already compile + verify.  Exercise multi
# type-var generics (const<A, B>), ADT-param generics (is_some<T> over Option),
# and ability-constrained generics (ch09).
_REPO_CORPUS = [
    "tests/conformance/ch02_generics.vera",
    "tests/conformance/ch09_abilities.vera",
    "examples/generics.vera",
]

# Targeted cases for the soundness-critical scenarios.
_INLINE_CORPUS = {
    # #1223: a generic `where`-helper under a GENERIC parent, whose own body
    # calls a TOP-LEVEL generic (`gug_pick`) and a SIBLING generic helper.
    # Neither instantiation exists until the helper itself is monomorphized —
    # in its still-generic spelling the argument's type is the enclosing type
    # VARIABLE — so both sides had to grow the same rescan.  This entry is
    # what makes the two halves land together: the codegen half alone makes
    # `gug_pick<Bool>` an emitted instantiation the verifier does not
    # discover, which is a false Tier-1 and turns this check red.
    "generic_under_generic_callees_1223": """
private forall<W> fn gug_pick(@W, @W -> @W)
  requires(true)
  ensures(true)
  effects(pure)
{
  @W.0
}

private forall<T> fn gug_parent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if gug_outer(true, false) then { 7 } else { 3 }
}
where {
  forall<U> fn gug_outer(@U, @U -> @U)
    requires(true)
    ensures(true)
    effects(pure)
  {
    gug_inner(@U.1, @U.0)
  }
  forall<V> fn gug_inner(@V, @V -> @V)
    requires(true)
    ensures(true)
    effects(pure)
  {
    gug_pick(@V.1, @V.0)
  }
}

public fn use_gug(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  gug_parent(1)
}
""",
    # Two type vars collapse to the same concrete type (A=B=Int) — exercises
    # the De Bruijn reindex inside _monomorphize_fn during discovery.
    "collapsed_typevars": """
private forall<A, B> fn pick_first(@A, @B -> @A)
  requires(true)
  ensures(@A.result == @A.0)
  effects(pure)
{
  @A.0
}

public fn use_collapsed(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick_first(@Int.1, @Int.0)
}
""",
    # Instantiates a PRELUDE generic (option_map).  Codegen emits
    # option_map$Int_JInt; the verifier must discover it via prelude injection.
    # This is the #1 parity risk — verify the verifier doesn't miss it.
    "prelude_option_map": """
public fn use_option_map(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_map(Some(@Int.0), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 })
}
""",
    # A generic whose body calls another generic — the instantiation of `wrap`
    # is only reachable transitively, through the monomorphized body of
    # `wrap_twice`.  Exercises the transitive worklist.
    "transitive_generic": """
private forall<T> fn wrap(@T -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@T.0)
}

private forall<T> fn wrap_twice(@T -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@T.0)
}

public fn use_transitive(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap_twice(@Int.0)
}
""",
    # #769 gap 1: a PARAMETERIZED-return builtin (string_chars → Array<String>)
    # in generic-arg position — both discoveries must bind T=String from the
    # shared _BUILTIN_PARAMETERIZED_RETURNS table, never the Bool phantom.
    "builtin_param_return_769": """
private forall<T> fn first769(@Array<T> -> @T)
  requires(array_length(@Array<T>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<T>.0[0]
}

public fn use_first769(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  first769(string_chars("abc"))
}
""",
    # #769 gap 2: nested type-argument unification — E binds at depth 2 from
    # Array<Array<Int>> on both sides via the shared _unify_type_arg_pair.
    "nested_unify_769": """
private forall<E> fn head_head769(@Array<Array<E>> -> @E)
  requires(
    array_length(@Array<Array<E>>.0) > 0
      && array_length(@Array<Array<E>>.0[0]) > 0
  )
  ensures(true)
  effects(pure)
{
  @Array<Array<E>>.0[0][0]
}

public fn use_head_head769(@Array<Array<Int>> -> @Int)
  requires(
    array_length(@Array<Array<Int>>.0) > 0
      && array_length(@Array<Array<Int>>.0[0]) > 0
  )
  ensures(true)
  effects(pure)
{
  head_head769(@Array<Array<Int>>.0)
}
""",
    # #769 logic-arm parity: apply_fn / async / await returns binding a bare
    # @T — the verifier's discovery must reach the same instantiations
    # (ident769$Int, ident769$Future<Int>) codegen emits.
    "logic_arm_returns_769": """
private forall<T> fn ident769(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private fn work769(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public fn use_logic_arms769(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<Async>)
{
  let @Int = ident769(apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, 21));
  let @Int = await(ident769(async(work769(@Int.0))));
  ident769(await(async(work769(@Int.1))))
}
""",
    # #898: cross-argument type-argument merge — the verifier's discovery
    # (`_collect_instantiations`, which shares `_infer_type_args_from_args` with
    # codegen) must merge the two sparse constructor arguments into the same
    # `eq2$Res<String, Int>` clone codegen emits, or the verifier⊇codegen
    # invariant breaks (a clone codegen emits that the verifier never proves).
    "cross_arg_merge_eq": """
private data Res<A, B> { MkOk(A), MkErr(B) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq(@T.1, @T.0)
}

public fn use_cross_arg(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  eq2(MkErr(5), MkOk("x"))
}
""",
    # #990: a forall<T> where-helper under a NON-generic parent is a mono base
    # — codegen emits its concrete clones (`gid$Int`, `gid$Bool`), so the
    # verifier's discovery must collect nested generics identically or the
    # clones run with contracts the verifier never proved (verifier⊇codegen
    # breaks).  Two instantiations, one reached from the parent body and one
    # from a sibling plain helper, so both discovery walks are exercised.
    "nested_generic_where_helper": """
private fn parent(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if flag(true) then { gid(@Int.0) + 5 } else { 0 }
}
where {
  forall<T> fn gid(@T -> @T)
    requires(true)
    ensures(@T.result == @T.0)
    effects(pure)
  {
    @T.0
  }
  fn flag(@Bool -> @Bool)
    requires(true)
    ensures(true)
    effects(pure)
  {
    gid(@Bool.0)
  }
}

public fn use_nested(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(10)
}
""",
    # #990 + PR #1001 review: a nested generic reached ONLY from contract
    # clauses (requires/ensures, never a body).  Contract reachability flows
    # through the same shared node-level walk, and Vera lowers contracts to
    # runtime checks — so codegen must emit the clone and the verifier must
    # discover the identical instantiation set.
    "nested_generic_contract_only": """
private fn parent(@Int -> @Int)
  requires(gok(@Int.0))
  ensures(gok(@Int.result))
  effects(pure)
{
  @Int.0 + 5
}
where {
  forall<T> fn gok(@T -> @Bool)
    requires(true)
    ensures(true)
    effects(pure)
  {
    true
  }
}

public fn use_contract_only(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(10)
}
""",
    # #1014: two same-named `forall` where-helpers under DIFFERENT non-generic
    # parents.  Qualification keys them `a$where$g` / `b$where$g`, so codegen
    # emits (and the verifier discovers) two distinct nested generic bases — a
    # bare-name key would collapse both onto the first parent's clone.
    "two_parents_same_named_generic_helper_1014": """
public fn a(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ g(@Int.0) }
where {
  forall<T> fn g(@T -> @Int) requires(true) ensures(true) effects(pure)
  { 1 }
}

public fn b(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ g(@Int.0) }
where {
  forall<T> fn g(@T -> @Int) requires(true) ensures(true) effects(pure)
  { 2 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ a(0) * 10 + b(0) }
""",
    # #1002: a `forall` helper under a GENERIC ancestor.  Codegen instantiates
    # the nested helper per parent-clone (`parent$where$outer$where$ginner`), and
    # the verifier discovers the SAME concrete-free chain key by recursing into
    # each clone's substituted subtree — both sides keyed identically so the
    # differential covers the nested clone (pre-fix it dangled `unknown func` at
    # run and fell to E520 at verify).
    "generic_helper_under_generic_ancestor_1002": """
private fn parent(@Int -> @Int)
  requires(true) ensures(@Int.result == @Int.0 + 5) effects(pure)
{ outer(@Int.0) + (if outer(false) then { 50 } else { 5 }) }
where {
  forall<T> fn outer(@T -> @T) requires(true) ensures(@T.result == @T.0) effects(pure)
  { ginner(@T.0) }
  where {
    forall<U> fn ginner(@U -> @U) requires(true) ensures(@U.result == @U.0) effects(pure)
    { @U.0 }
  }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(@Int.result == 15) effects(pure)
{ parent(10) }
""",
}


def _codegen_emitted(
    program: object, source: str, path: str,
) -> set[tuple[str, tuple[str, ...]]]:
    """The (generic name, concrete types) set codegen actually monomorphizes."""
    gen = CodeGenerator(source=source, file=path)
    gen.compile_program(program)  # type: ignore[arg-type]
    return getattr(gen, "_emitted_instances", set())


def _verifier_discovered(
    program: object, source: str, path: str,
) -> set[tuple[str, tuple[str, ...]]]:
    """The (generic name, concrete types) set the verifier discovers.

    Reads the registered ``_instances`` (which ``register_program`` populates via
    ``_collect_instantiations`` and per-monomorphization verification actually
    consumes) rather than recomputing — so a regression in the registration seam
    surfaces here instead of being masked (PR #767 review).
    """
    verifier = ContractVerifier(source=source, file=path)
    verifier.register_program(program)  # type: ignore[arg-type]
    result = verifier._instances
    return {(name, ct) for name, cts in result.items() for ct in cts}




def _discovery_scopes(
    program: object, source: str, path: str, modules: list[object] | None = None,
) -> tuple[dict[str, set[frozenset[str]]], dict[str, set[frozenset[str]]]]:
    """``(codegen, verifier)`` per-declaration discovery scopes (#1299).

    Records, for every declaration each side's instantiation-discovery walk
    enters, the set of bare names that walk resolves against.  That set is the
    input to the ownership predicate discovery asks to decide whether a bare
    ``get`` is an effect operation — so if the two sides compute it
    differently they can name different clones from the same source, which is
    the shape a coverage-only differential cannot see (both sides can be
    wrong together and still be equal).
    """
    # name -> the SET of distinct NAMESPACE scopes that declaration was walked
    # under.  Two refinements, each for a difference that is real but not the
    # one under test:
    #
    # * a SET, not a single value — two modules' same-named generics reach
    #   the walk under one pre-rename clone name (`gen$Bool`), so keeping
    #   only the first would compare `mid1`'s scope on one side against
    #   `base`'s on the other and call an ordering artefact a divergence;
    # * the walked declaration's own `where` helpers are subtracted, because
    #   codegen walks a clone both before and after `_hoist_clone_where_fns`
    #   strips them while the verifier walks it once.  Those two scopes
    #   differ by exactly the helper names, and both are right for what they
    #   walk.  The helper accumulation is pinned on its own by
    #   ``TestDiscoveryWalkContract``; what is compared here is the part that
    #   comes from the namespace tables and the namespace SELECTION.
    captured: dict[str, set[frozenset[str]]] = {}
    original = Monomorphizer._collect_calls_in_node_scoped

    def recording(inner, fn, *a):  # type: ignore[no-untyped-def]
        if inner._scope_fn_names is not None:
            own_helpers = {wfn.name for wfn in (fn.where_fns or ())}
            captured.setdefault(fn.name, set()).add(
                frozenset(inner._scope_fn_names) - own_helpers,
            )
        return original(inner, fn, *a)

    Monomorphizer._collect_calls_in_node_scoped = recording  # type: ignore[method-assign]
    try:
        gen = CodeGenerator(
            source=source, file=path, resolved_modules=modules or [],
        )
        gen.compile_program(program)  # type: ignore[arg-type]
        codegen_scopes = dict(captured)

        captured.clear()
        verifier = ContractVerifier(
            source=source, file=path, resolved_modules=modules or [],
        )
        verifier.register_program(program)  # type: ignore[arg-type]
        verifier_scopes = dict(captured)
    finally:
        Monomorphizer._collect_calls_in_node_scoped = original  # type: ignore[method-assign]
    return codegen_scopes, verifier_scopes


def _assert_scopes_agree(
    label: str,
    codegen_scopes: dict[str, set[frozenset[str]]],
    verifier_scopes: dict[str, set[frozenset[str]]],
) -> None:
    """Both sides resolved every shared declaration against the same names."""
    shared = sorted(set(codegen_scopes) & set(verifier_scopes))
    assert shared, (
        f"[{label}] neither side entered a discovery scope for any shared "
        f"declaration — the comparison would pass vacuously "
        f"(codegen={sorted(codegen_scopes)}, verifier={sorted(verifier_scopes)})"
    )
    for name in shared:
        cg, ver = codegen_scopes[name], verifier_scopes[name]
        if cg == ver:
            continue
        cg_only = sorted(sorted(s) for s in cg - ver)
        ver_only = sorted(sorted(s) for s in ver - cg)
        raise AssertionError(
            f"[{label}] discovery scopes disagree at the first divergent "
            f"declaration {name!r}:\n"
            f"  codegen-only scopes  = {cg_only}\n"
            f"  verifier-only scopes = {ver_only}"
        )


def _cross_module_sets(
    main_src: str, modules: list[object],
) -> tuple[set[tuple[str, tuple[str, ...]]], set[tuple[str, tuple[str, ...]]]]:
    """Return ``(codegen_emitted, verifier_discovered)`` for ``main_src`` compiled
    and registered against ``modules`` — the shared codegen↔verifier differential
    harness for the cross-module generic tests.  Reads the verifier's registered
    ``_instances`` (what per-monomorphization verification actually consumes), not
    a fresh recompute, so a registration-seam regression surfaces here."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        f.flush()
        mp = f.name
    try:
        prog = transform(parse_file(mp))
        gen = CodeGenerator(source=main_src, file=mp, resolved_modules=modules)
        gen.compile_program(prog)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=main_src, file=mp, resolved_modules=modules,
        )
        verifier.register_program(prog)  # type: ignore[arg-type]
        verifier_set = {
            (n, ct)
            for n, cts in verifier._instances.items()
            for ct in cts
        }
    finally:
        os.unlink(mp)
    return codegen_set, verifier_set


def _assert_covers(
    program: object, source: str, path: str, label: str,
) -> None:
    codegen_set = _codegen_emitted(program, source, path)
    verifier_set = _verifier_discovered(program, source, path)

    # Guard against a vacuous pass: every corpus entry instantiates generics, so
    # an empty codegen set means the harness silently stopped exercising them.
    assert codegen_set, (
        f"[{label}] codegen emitted no instantiations — the differential "
        f"check would pass vacuously; corpus entry no longer exercises generics"
    )

    codegen_names = {n for (n, _) in codegen_set}
    verifier_names = {n for (n, _) in verifier_set}
    missing = codegen_names - verifier_names
    assert not missing, (
        f"[{label}] verifier missed generic(s) codegen emits: {sorted(missing)}\n"
        f"  codegen  = {sorted(codegen_set)}\n"
        f"  verifier = {sorted(verifier_set)}"
    )

    # Per-instantiation coverage (stronger than per-generic counts, which could
    # pass with the right COUNT but the wrong concrete tuples): every (name,
    # types) codegen emits must actually be discovered by the verifier.  The
    # verifier may infer MORE precise scalar types than codegen's WAT collapse
    # (Nat vs Int, Byte vs Bool — sound, it checks the type the value really
    # has), so normalize the verifier's set through that collapse before the
    # subset check.  (If a future corpus program diverges beyond scalars, this
    # fails loudly rather than silently passing on a wrong tuple.)
    collapse = {"Nat": "Int", "Byte": "Bool"}

    def _norm(types: tuple[str, ...]) -> tuple[str, ...]:
        return tuple(collapse.get(t, t) for t in types)

    verifier_norm = {(n, _norm(ct)) for (n, ct) in verifier_set}
    uncovered = {
        (n, ct) for (n, ct) in codegen_set if (n, _norm(ct)) not in verifier_norm
    }
    assert not uncovered, (
        f"[{label}] verifier did not cover instantiation(s) codegen emits: "
        f"{sorted(uncovered)}\n"
        f"  codegen  = {sorted(codegen_set)}\n"
        f"  verifier = {sorted(verifier_set)}"
    )


# =====================================================================
# Third consultor: call-rewrite ↔ emitted-clone agreement (#899)
# =====================================================================
# The verifier⊇codegen differential above covers TWO of the three
# monomorphization consultors: instantiation DISCOVERY (which clones get
# emitted) and the VERIFIER's discovery.  It does NOT exercise the WASM
# CALL-REWRITE (`_resolve_generic_call` / `_infer_fncall_vera_type`), which
# independently re-derives the mangled name each generic call site references.
# When call-rewrite and discovery disagree on a clone name, the call site
# references a symbol Pass 1.5 never emitted — a check-green / verify-green
# program whose `main` is dropped at `vera run` (#878's own failure class,
# reintroduced by PR #899's one-sided consultor edits).  These corpus entries
# exercise exactly the user-fn-return-into-generic-arg shapes that slipped.

_CALL_REWRITE_CORPUS: dict[str, str] = {
    # Issue 1: non-generic user fn returning a PARAMETERIZED type in
    # `Option<T>` position — call-rewrite recovers `Decimal`, discovery must too.
    "param_user_fn_return": """
private fn maybe(@Int -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ Some(decimal_from_int(@Int.0)) }

private forall<T> fn first_opt(@Option<T>, @Int -> @Option<T>)
  requires(true) ensures(true) effects(pure)
{ @Option<T>.0 }

public fn main(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ first_opt(maybe(3), 0) }
""",
    # Issue 1 variant: Result<Decimal, String> return.
    "param_user_fn_result_return": """
private fn tryit(@Int -> @Result<Decimal, String>)
  requires(true) ensures(true) effects(pure)
{ Ok(decimal_from_int(@Int.0)) }

private forall<T> fn first_res(@Result<T, String>, @Int -> @Result<T, String>)
  requires(true) ensures(true) effects(pure)
{ @Result<T, String>.0 }

public fn main(@Unit -> @Result<Decimal, String>)
  requires(true) ensures(true) effects(pure)
{ first_res(tryit(5), 0) }
""",
    # Issue 2: user fn returning a scalar-resolving alias in bare `@T` position
    # — discovery/verifier key on the RAW name `Age`, call-rewrite must too.
    "alias_scalar_return": """
type Age = Int;

private fn getage(@Int -> @Age)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private forall<T> fn pick_last(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick_last(getage(1), getage(2)) }
""",
    # Issue 2 variant: named refinement of a scalar.
    "refinement_scalar_return": """
type PosInt = { @Int | @Int.0 > 0 };

private fn getpos(@Int -> @PosInt)
  requires(@Int.0 > 0) ensures(true) effects(pure)
{ @Int.0 }

private forall<T> fn pick_last(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ pick_last(getpos(1), getpos(2)) }
""",
    # Issue 3 (#899 round 3, a NET regression vs base): a NON-generic user fn
    # returning a LITERAL PARAMETERIZED type (`Option<…>`/`Result<…>`/`Box<…>`)
    # bound to a generic's BARE `@T`.  Discovery keys the clone on the base
    # name (`pick_last$Option`); pre-fix the call-rewrite's `not ret_te.type_args`
    # gate bailed and fell through to the i32→`Bool` collapse → `pick_last$Bool`,
    # never emitted.  (`_call_rewrite_desync` on the repro shows
    # `emitted=['pick_last$Option'], dangling=['pick_last$Bool']`.)
    # #769 gap 1b: builtin SIMPLE-name returns in bare `@T` position — the
    # completed _BUILTIN_VERA_RETURN_TYPES dict is consulted by BOTH sides;
    # pre-fix discovery phantom-defaulted (ident$Bool) while the rewrite
    # chain mangled ident$String / ident$Array — dangling, main dropped.
    "builtin_simple_return_769": """
private forall<T> fn ident769(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @String = ident769(int_to_string(42));
  array_length(ident769(string_chars(@String.0)))
}
""",
    # #769 generic-return parity: a generic call's i32-handle / declared-Nat
    # return in generic-arg position — the rewrite's generic branch now
    # substitutes the DECLARED return (pass769$Option / natret769$Nat) exactly
    # as discovery does, instead of WAT-collapsing to Bool / Int.
    "generic_return_into_bare_typevar_769": """
private forall<T> fn ident769(@T, @T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

private forall<U> fn pass769(@U -> @U)
  requires(true) ensures(true) effects(pure)
{ @U.0 }

private forall<U> fn natret769(@U -> @Nat)
  requires(true) ensures(true) effects(pure)
{ 7 }

public fn main(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{
  let @Option<Int> = ident769(pass769(Some(42)), pass769(Some(1)));
  natret769(ident769(natret769(1), natret769(2)))
}
""",
    # #769 logic-arm parity: apply_fn closure return in bare `@T` position —
    # discovery's new _closure_arg_return_te arm mirrors the rewrite chain.
    "apply_fn_return_769": """
private forall<T> fn ident769(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ ident769(apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }, 21)) }
""",
    "param_return_into_bare_typevar": """
private fn mk(@Int -> @Option<Option<Decimal>>)
  requires(true) ensures(true) effects(pure)
{ Some(Some(decimal_from_int(@Int.0))) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match pick_last(mk(1), mk(2)) { Some(@Option<Decimal>) -> 0, None -> 1 } }
""",
    "result_return_into_bare_typevar": """
private fn mkr(@Int -> @Result<Option<Decimal>, String>)
  requires(true) ensures(true) effects(pure)
{ Ok(Some(decimal_from_int(@Int.0))) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match pick_last(mkr(1), mkr(2)) { Ok(@Option<Decimal>) -> 0, Err(@String) -> 1 } }
""",
    "adt_return_into_bare_typevar": """
private data Box<T> { MkBox(T) }

private fn mkb(@Int -> @Box<Decimal>)
  requires(true) ensures(true) effects(pure)
{ MkBox(decimal_from_int(@Int.0)) }

private forall<VeraT> fn pick_last(@VeraT, @VeraT -> @VeraT)
  requires(true) ensures(true) effects(pure)
{ @VeraT.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ match pick_last(mkb(1), mkb(2)) { MkBox(@Decimal) -> 0 } }
""",
    # #898: CROSS-ARGUMENT type-argument merge.  `eq2(MkErr(5), MkOk("x"))`
    # over `data Res<A, B> { MkOk(A), MkErr(B) }` — the first argument fixes
    # `B = Int`, the second fixes `A = String` — so discovery, the verifier, AND
    # the call-rewrite must all merge the two partial recoveries into the ONE
    # clone `eq2$Res<String, Int>`.  A one-sided merge (call-rewrite resolves
    # the bare `eq2$Res` while discovery emits `eq2$Res<String, Int>`, or vice
    # versa) drops `main` with an `unknown func` — exactly what this differential
    # exists to catch.  This is the entry that was MISSING when the merge landed.
    "cross_arg_merge_eq": """
private data Res<A, B> { MkOk(A), MkErr(B) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.1, @T.0) }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq2(MkErr(5), MkOk("x")) }
""",
    # #898: cross-argument merge, REVERSED argument order — the merge must be
    # order-independent (arg 0 fixes `A`, arg 1 fixes `B`), and all three
    # consultors must still agree on the ONE `eq2$Res<String, Int>` clone.  A
    # first-argument-wins consultor would key `eq2$Res<String, ?>` here vs the
    # `eq2$Res<?, Int>` of the non-reversed entry, so pairing the two orders
    # pins that the merged name is stable regardless of which argument arrives
    # first.
    "cross_arg_merge_eq_reversed": """
private data Res<A, B> { MkOk(A), MkErr(B) }

private forall<T where Eq<T>> fn eq2(@T, @T -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq(@T.1, @T.0) }

public fn main(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ eq2(MkOk("x"), MkErr(5)) }
""",
}

def _mangle(name: str, types: tuple[str, ...]) -> str:
    """The mono-clone symbol for ``(name, types)`` — the shared injective
    mangler both discovery (clone emission) and call-rewrite use."""
    from vera.monomorphize import Monomorphizer

    return Monomorphizer._mangle_fn_name(name, types)


def _call_rewrite_desync(source: str) -> tuple[set[str], list[str]]:
    """Compile ``source`` in a FRESH CodeGenerator, capturing every mono-clone
    symbol the WASM CALL-REWRITE (`_resolve_generic_call`) resolves to, and
    return ``(emitted_clone_symbols, dangling_targets)``.

    A dangling target is a symbol a generic call site references but that
    discovery never emitted — the exact call-rewrite↔discovery desync #899
    caught.  Captured at the consultor level (a monkeypatch on
    `_resolve_generic_call`) rather than by scraping the WAT, because a desync
    causes the CALLING function to be SKIPPED (E602), which elides its body —
    and with it the dangling `call` — from the WAT entirely, so a WAT scan
    can't see the very evidence it needs (the mistake this test was first
    written with).  Each call builds its own compile pipeline so
    `_emitted_instances` never cross-contaminates across corpus entries.
    """
    from vera.wasm.calls import CallsMixin

    captured: list[str | None] = []
    orig = CallsMixin._resolve_generic_call

    def _spy(self: object, call: object) -> object:
        result = orig(self, call)  # type: ignore[arg-type]
        captured.append(result)  # type: ignore[arg-type]
        return result

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        gen = CodeGenerator(source=source, file=path)
        CallsMixin._resolve_generic_call = _spy  # type: ignore[assignment]
        try:
            gen.compile_program(program)  # type: ignore[arg-type]
        finally:
            CallsMixin._resolve_generic_call = orig  # type: ignore[assignment]
        emitted = {
            _mangle(name, types)
            for (name, types) in getattr(gen, "_emitted_instances", set())
        }
    finally:
        os.unlink(path)
    targets = {t for t in captured if t is not None}
    dangling = sorted(targets - emitted)
    return emitted, dangling


@pytest.mark.parametrize("label", sorted(_CALL_REWRITE_CORPUS))
def test_call_rewrite_matches_emitted_clones(label: str) -> None:
    """Every mono-clone a generic call site references must be an emitted
    clone — the call-rewrite consultor must pick the same name discovery /
    the verifier did.  A dangling target is the #899 desync (`main` dropped
    at run on a check-green program)."""
    source = _CALL_REWRITE_CORPUS[label]
    emitted, dangling = _call_rewrite_desync(source)
    assert emitted, (
        f"[{label}] no mono clones emitted — corpus entry no longer exercises "
        f"generic instantiation, the check would pass vacuously"
    )
    assert not dangling, (
        f"[{label}] call site references clone(s) never emitted (call-rewrite "
        f"↔ discovery desync, #899): {dangling}\n  emitted = {sorted(emitted)}"
    )


@pytest.mark.parametrize("rel", _REPO_CORPUS)
def test_verifier_covers_codegen_repo(rel: str) -> None:
    path = str(_REPO_ROOT / rel)
    program = transform(parse_file(path))
    source = Path(path).read_text(encoding="utf-8")
    _assert_covers(program, source, path, rel)


@pytest.mark.parametrize("label", sorted(_INLINE_CORPUS))
def test_verifier_covers_codegen_inline(label: str) -> None:
    source = _INLINE_CORPUS[label]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        _assert_covers(program, source, path, label)
    finally:
        os.unlink(path)


@pytest.mark.parametrize("call_form", ["bare", "qualified"])
def test_imported_generic_symmetric_between_codegen_and_verifier(
    call_form: str,
) -> None:
    """A generic imported from another module and instantiated by the importer
    is monomorphized by BOTH codegen and the verifier at the SAME concrete type
    (#774).  The importer discovers the instantiation from its own call site and
    emits the clone into its own flat module; the verifier's discovery merges the
    imported (unshadowed) generic identically, so the differential invariant
    (verifier covers exactly codegen's emitted set) holds with equality — no
    false Tier-1 from cross-module generics.

    Both the bare call ``ext_id(42)`` and the module-qualified ``a::ext_id(42)``
    (an ``ast.ModuleCall`` that the shared discovery now walks, and that desugars
    to the bare target at codegen) must produce the SAME single ``ext_id<Int>``
    instantiation on both sides — a divergence between the two forms, or between
    codegen and the verifier, would reintroduce the gap this pins.

    Flips the pre-#774 tripwire: this test previously asserted NEITHER side
    monomorphized (both empty).  Now both monomorphize; the equality assertion is
    the lockstep the #732 differential demands.
    """
    a_src = (
        "public forall<T> fn ext_id(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    )
    call = "ext_id(42)" if call_form == "bare" else "a::ext_id(42)"
    b_src = (
        "import a;\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        f"{{ {call} }}\n"
    )

    mod_a = _resolved_module(("a",), a_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(b_src)
        f.flush()
        bp = f.name
    try:
        prog_b = transform(parse_file(bp))
        gen = CodeGenerator(source=b_src, file=bp, resolved_modules=[mod_a])
        gen.compile_program(prog_b)  # type: ignore[arg-type]
        codegen_set = getattr(gen, "_emitted_instances", set())
        verifier = ContractVerifier(
            source=b_src, file=bp, resolved_modules=[mod_a],
        )
        verifier.register_program(prog_b)  # type: ignore[arg-type]
        # Read the registered ``_instances`` that per-monomorphization verification
        # actually consumes, not a fresh recompute — so a regression in the
        # registration seam surfaces here rather than being masked (PR #767 review).
        verifier_set = {
            (n, ct)
            for n, cts in verifier._instances.items()
            for ct in cts
        }
    finally:
        os.unlink(bp)

    # Both sides monomorphize the imported generic at exactly ext_id<Int>.
    assert ("ext_id", ("Int",)) in codegen_set, (
        f"codegen must emit ext_id<Int> for the {call_form} call, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — cross-module generic lockstep"
    )


def test_imported_fn_nested_generic_symmetric_between_codegen_and_verifier(
) -> None:
    """`#999`: an imported NON-generic fn (`compute`) whose body calls its own
    nested `forall` where-helper (`gid`) must have that helper's instantiation
    discovered by BOTH sides at the SAME qualified key.

    Both sides give the module program the shared #1014 nested-generic
    qualification (``gid`` → ``compute$where$gid``), harvest it as an imported
    mono base, and seed its instantiation from the module BODY's
    ``compute$where$gid(@Int.0)`` call — codegen emits the clone, the verifier
    verifies it.  A desync (only one side walks the module body) drops the clone
    from one set: codegen would emit a clone the verifier never proved (a false
    Tier-1) or reference a symbol never emitted (`main` dropped at run).  Pins
    the equality both ways.
    """
    mod = _resolved_module(("lib_nested",), (
        "public fn compute(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ gid(@Int.0) + 1 }\n"
        "where {\n"
        "  forall<T> fn gid(@T -> @T)\n"
        "    requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "  { @T.0 }\n"
        "}\n"
    ))
    main_src = (
        "import lib_nested(compute);\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ compute(10) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    # #1029: the imported nested generic's base is namespaced by the module path
    # (``mod$lib_nested$compute$where$gid``), byte-identical to
    # ``_module_qualified_wasm_name`` — so two imported modules' same-named nested
    # generics stay distinct instead of collapsing first-seen-wins.
    assert ("mod$lib_nested$compute$where$gid", ("Int",)) in codegen_set, (
        f"codegen must emit the imported nested generic's clone under its "
        f"module-qualified base, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — imported nested-generic "
        f"lockstep (#999); a miss is a false Tier-1"
    )


def test_shadowed_imported_generic_symmetric_between_codegen_and_verifier(
) -> None:
    """`#814` asymmetric variant: an imported generic (`gen`) shadowed by a
    LOCAL non-generic AND module-qualified called (`g::gen`) is monomorphized by
    codegen under a ``mod$…`` name and recorded in ``_emitted_instances`` under
    that ``mod$g$gen`` base (NOT the bare `gen`, which a same-named local owns —
    CR 3519156263), so the verifier must discover the SAME qualified
    instantiation under the SAME base — else the pre-fix false Tier-1 returns
    (verify resolved the module generic's contract while codegen ran the local
    shadow).

    Pins the shadowed-side lockstep: the differential must catch a desync where
    only one of the two discovers the qualified `mod$g$gen<Int>` instantiation.
    """
    mod_a = _resolved_module(("g",), (
        "public forall<T> fn gen(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    ))
    b_src = (
        "import g;\n\n"
        "private fn gen(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        "public fn probe(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::gen(5) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(b_src, [mod_a])

    assert ("mod$g$gen", ("Int",)) in codegen_set, (
        f"codegen must emit the shadowed generic's clone under its mod$… base, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — shadowed cross-module generic "
        f"lockstep (the #814 false-Tier-1 guard)"
    )


@pytest.mark.parametrize("inner_shadowed", [False, True])
def test_transitive_shadowed_generic_symmetric(inner_shadowed: bool) -> None:
    """`#774` review (CR 3518737014): a SHADOWED imported generic whose body
    calls ANOTHER generic emits that TRANSITIVE clone — codegen and the verifier
    must discover the SAME transitive set, or a cross-module transitive clone
    runs unverified (a new false Tier-1).

    `outer<T>` (shadowed, calls `inner(@T.0)`) → `inner<T>`.  The parametrization
    covers `inner` unshadowed (a normal clone keyed `inner`) and `inner` ALSO
    shadowed (a same-module sibling keyed `mod$g$inner` — CR 3519156263: a
    shadowed clone is namespaced by its `mod$…` base so it never collides with a
    same-named local generic).  Both must appear on both sides — a desync of the
    transitive scan (codegen or verifier) flips the equality.
    """
    mod_a = _resolved_module(("g",), (
        "public forall<T> fn inner(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
        "public forall<T> fn outer(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ inner(@T.0) }\n"
    ))
    inner_local = (
        "private fn inner(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 200 }\n\n"
    ) if inner_shadowed else ""
    b_src = (
        "import g;\n\n"
        "private fn outer(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        f"{inner_local}"
        "public fn probe(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::outer(7) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(b_src, [mod_a])

    # The shadowed outer is keyed under its mod$… base; the transitive inner is
    # keyed `mod$g$inner` when a local shadows it, else the bare `inner`.
    inner_key = ("mod$g$inner", ("Int",)) if inner_shadowed else (
        ("inner", ("Int",))
    )
    assert ("mod$g$outer", ("Int",)) in codegen_set and (
        inner_key in codegen_set
    ), (
        f"codegen must emit mod$g$outer<Int> and its transitive {inner_key[0]}"
        f"<Int>, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — transitive shadowed generic "
        f"lockstep; a missing transitive clone is a new false Tier-1"
    )


def test_unshadowed_generic_calling_shadowed_sibling_symmetric() -> None:
    """`#774` review (CR 3519063445): an UNSHADOWED generic `caller<T>` whose
    body qualified-calls a SHADOWED `g::gen` reaches that shadowed generic only
    through its clone (`caller$Int`) — codegen scans the emitted normal clones
    for shadowed ModuleCalls, and the verifier must mirror that scan, or it
    discovers a strict subset (the `mod$g$gen<Int>` clone runs unverified: a
    false Tier-1).
    """
    mod_a = _resolved_module(("g",), (
        "public forall<T> fn gen(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
    ))
    b_src = (
        "import g;\n\n"
        "private fn gen(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        "private forall<T> fn caller(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::gen(@T.0) }\n\n"
        "public fn probe(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ caller(5) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(b_src, [mod_a])

    assert ("caller", ("Int",)) in codegen_set and (
        ("mod$g$gen", ("Int",)) in codegen_set
    ), (
        f"codegen must emit caller<Int> and the shadowed mod$g$gen<Int> it "
        f"reaches, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — an unshadowed generic reaching "
        f"a shadowed sibling; a miss is a new false Tier-1"
    )


def test_private_module_generic_symmetric_between_codegen_and_verifier() -> None:
    """`#1000`: a PRIVATE module generic (`inner`) reached transitively by a
    PUBLIC imported generic (`outer`) must be discovered by BOTH sides under the
    SAME module-qualified key (`mod$lib_priv$inner`), NEVER a bare `inner`.

    Codegen harvests the private generic into the shadowed-generic machinery and
    reroutes `outer`'s clone body call onto the module-qualified base; the
    verifier mirrors the harvest + reroute so it discovers the identical
    `mod$lib_priv$inner<Int>` instantiation and verifies it (a lying private
    contract must E500 at the importer).  A bare-name key would hijack a
    same-named local fn and collapse two modules' private generics — the exact
    #1000 trap this equality pins.
    """
    mod = _resolved_module(("lib_priv",), (
        "private forall<T> fn inner(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
        "public forall<T> fn outer(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ inner(@T.0) }\n"
    ))
    main_src = (
        "import lib_priv(outer);\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ outer(7) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("outer", ("Int",)) in codegen_set and (
        ("mod$lib_priv$inner", ("Int",)) in codegen_set
    ), (
        f"codegen must emit outer<Int> and its transitive private "
        f"mod$lib_priv$inner<Int> under the module-qualified base, "
        f"got {sorted(codegen_set)}"
    )
    assert ("inner", ("Int",)) not in codegen_set, (
        f"the private generic must NOT be keyed bare (hijack risk), "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — private module generic reached "
        f"transitively (#1000); a miss leaves a lying private contract unverified"
    )


def test_local_shadowing_private_module_generic_symmetric() -> None:
    """`#1000` collision variant: a LOCAL non-generic `dup` and a same-named
    PRIVATE module generic `dup` reached transitively by a public imported
    `caller` must stay separate on both sides.

    The local `dup` keeps its bare identity (main's `dup(5)` runs it); the
    module's `dup` is keyed `mod$lib$dup` (caller's clone body reaches it).  A
    bare-name harvest would collapse the two — the draft-PR #1026 hijack this
    pins against.
    """
    mod = _resolved_module(("lib",), (
        "private forall<T> fn dup(@T -> @Int)"
        " requires(true) ensures(true) effects(pure) { 0 }\n"
        "public forall<T> fn caller(@T -> @Int)"
        " requires(true) ensures(true) effects(pure) { dup(@T.0) }\n"
    ))
    main_src = (
        "import lib(caller);\n"
        "private fn dup(@Int -> @Int)"
        " requires(true) ensures(@Int.result == @Int.0 + 100) effects(pure)"
        " { @Int.0 + 100 }\n"
        "public fn main(@Unit -> @Int)"
        " requires(true) ensures(true) effects(pure)"
        " { dup(5) * 1000 + caller(3) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("caller", ("Int",)) in codegen_set and (
        ("mod$lib$dup", ("Int",)) in codegen_set
    ), (
        f"codegen must emit caller<Int> and the module's private "
        f"mod$lib$dup<Int>, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — local/private-generic collision "
        f"(#1000); the module's dup stays under its mod$… key, distinct from the "
        f"bare local dup"
    )


def test_nongeneric_caller_of_private_generic_symmetric_1029() -> None:
    """`#1029` (R1): a NON-generic imported fn (`use_it`) that calls a PRIVATE
    module generic (`inner`) must have `inner`'s instantiation discovered by BOTH
    sides under the module-qualified base `mod$lib$inner`.

    Pre-fix only the PUBLIC-generic branch rerouted private-generic calls, so
    `use_it`'s bare `inner(@Int.0)` kept a bare name: codegen emitted `use_it`'s
    body with a `call $inner` that dangled at run (`unknown func`), and neither
    side seeded `mod$lib$inner<Int>`.  The loop-top reroute (codegen) + the
    non-generic-body seed (`_monomorphize_shadowed_module_generics`) / the
    module-body reroute (verifier discovery) make both discover the identical
    instantiation — a lockstep that also proves the clone codegen now emits IS
    verified.
    """
    mod = _resolved_module(("lib",), (
        "private forall<T> fn inner(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n"
        "public fn use_it(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ inner(@Int.0) + 1 }\n"
    ))
    main_src = (
        "import lib(use_it);\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ use_it(4) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("mod$lib$inner", ("Int",)) in codegen_set, (
        f"codegen must emit the private generic's clone reached from a "
        f"non-generic caller under its mod$… base, got {sorted(codegen_set)}"
    )
    assert ("inner", ("Int",)) not in codegen_set, (
        f"the private generic must NOT be keyed bare (hijack risk), "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — a non-generic caller of a "
        f"private generic (#1029); a miss dangles the clone at run"
    )


def test_shadowed_generic_private_sibling_symmetric_1029() -> None:
    """`#1029` (R4): a locally-shadowed PUBLIC generic (`g::gen`) whose body calls
    a PRIVATE sibling generic (`sib`) must have BOTH clones discovered on both
    sides — `mod$g$gen<Int>` and its transitive `mod$g$sib<Int>`.

    Codegen harvests both into the shadowed-generic machinery and reaches `sib`
    through `gen`'s rerouted clone body; pre-fix the verifier built its shadowed
    map from PUBLIC-shadowed generics only, so `sib` had no base in the
    transitive scan and `mod$g$sib<Int>` ran unverified (a false Tier-1).  The
    equality pins that the verifier now discovers the private sibling too.
    """
    mod = _resolved_module(("g",), (
        "private forall<T> fn sib(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 11 }\n"
        "public forall<T> fn gen(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ sib(@T.0) }\n"
    ))
    main_src = (
        "import g;\n\n"
        "private fn gen(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 + 100 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ g::gen(5) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("mod$g$gen", ("Int",)) in codegen_set and (
        ("mod$g$sib", ("Int",)) in codegen_set
    ), (
        f"codegen must emit the shadowed generic AND its private sibling under "
        f"their mod$… bases, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — shadowed generic's private "
        f"sibling (#1029, R4); a miss leaves the sibling's clone a false Tier-1"
    )


def test_nested_generic_under_private_generic_symmetric_1029() -> None:
    """`#1029` (R3/R5): a nested `forall` where-helper (`ginner`) under a PRIVATE
    module generic (`priv_outer`) reached through a public entry must be keyed by
    the SAME concrete-FREE, module-qualified lexical chain on both sides —
    `mod$lib1$priv_outer$where$ginner`.

    This is the canonical-key lockstep: codegen's emitted WASM clone carries a
    per-instantiation concrete-INCLUDING name
    (`mod$lib1$priv_outer$Int$where$ginner$Int`), but its `_emitted_instances`
    key must be the concrete-FREE chain — which the R3 `_clone_base_chain`
    population on the shadowed path produces, and which the verifier's discovery
    (`record_nested`) and enclosing-chain reconstruction rebuild identically.  A
    desync (codegen concrete-including vs verifier concrete-free) left the lying
    nested contract on the uninstantiated E520 path: a false Tier-1.
    """
    mod = _resolved_module(("lib1",), (
        "private forall<T> fn priv_outer(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ ginner(@T.0) }\n"
        "where {\n"
        "  forall<U> fn ginner(@U -> @Int)\n"
        "    requires(true) ensures(true) effects(pure)\n"
        "  { 1 }\n"
        "}\n"
        "public forall<T> fn pub_entry(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ priv_outer(@T.0) }\n"
    ))
    main_src = (
        "import lib1(pub_entry);\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ pub_entry(7) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("mod$lib1$priv_outer$where$ginner", ("Int",)) in codegen_set, (
        f"codegen must key the nested generic under the concrete-FREE, "
        f"module-qualified chain, got {sorted(codegen_set)}"
    )
    assert not any(
        "$Int$where$" in n for (n, _) in codegen_set
    ), (
        f"the _emitted_instances key must be concrete-FREE (no `$Int$where$`), "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — nested generic under a private "
        f"module generic (#1029, R3/R5); a key desync is a false Tier-1"
    )


def test_private_to_private_generic_chain_symmetric_1029() -> None:
    """`#1029` (R1): a public generic → private `aa` → private `bb` chain must
    have EVERY link discovered on both sides under its mod$… base
    (`mod$m$aa`, `mod$m$bb`).

    Pre-fix a private generic's own body was harvested RAW, so `aa`'s bare
    `bb(@T.0)` call was not rerouted onto `mod$m$bb`: the verifier discovered a
    strict subset (`bb`'s clone ran unverified).  The loop-top reroute of the
    private decls themselves closes the chain.
    """
    mod = _resolved_module(("m",), (
        "private forall<T> fn bb(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 11 }\n"
        "private forall<T> fn aa(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ bb(@T.0) }\n"
        "public forall<T> fn pub(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ aa(@T.0) }\n"
    ))
    main_src = (
        "import m(pub);\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ pub(7) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("mod$m$aa", ("Int",)) in codegen_set and (
        ("mod$m$bb", ("Int",)) in codegen_set
    ), (
        f"codegen must emit both private links of the chain under their mod$… "
        f"bases, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — private→private chain (#1029); "
        f"a missing link runs unverified"
    )


@pytest.mark.parametrize(
    ("gen_vis", "imports"),
    [
        ("public", "door"),        # public, outside the importer's filter
        ("public", "gen2, door"),  # public, inside it, but locally shadowed
        ("public", None),          # wildcard import, locally shadowed
        ("private", "door"),       # the #1000 family (regression half)
    ],
    ids=["out_of_filter", "in_filter_shadowed", "wildcard", "private"],
)
def test_module_generic_qualified_only_symmetric_1274(
    gen_vis: str, imports: str | None,
) -> None:
    """#1274: EVERY qualified-only module generic — the ones that do not own the
    importer's bare name — is emitted and discovered under the SAME
    ``mod$<path>$name`` base by both sides.

    Pre-fix only the PRIVATE family was routed that way, so codegen collapsed a
    public module generic's clone onto the importer's bare ``gen2$Bool`` while
    the verifier resolved the module's contract: the module ran the importer's
    body with a proved ``ensures`` (a false Tier-1), or dangled at
    ``unknown func`` where the importer declared no such name.  The per-module
    differential is what pins the two sides to one namespace: an asymmetry here
    is precisely a clone one side emits and the other never verifies.
    """
    mod = _resolved_module(("lib",), (
        "private fn v(@Unit -> @Int)\n"
        "  requires(true) ensures(@Int.result == 111) effects(pure)\n"
        "{ 111 }\n\n"
        f"{gen_vis} forall<T> fn gen2(@T -> @Int)\n"
        "  requires(true) ensures(@Int.result == 111) effects(pure)\n"
        "{ v(()) }\n\n"
        "public fn door(@Bool -> @Int)\n"
        "  requires(true) ensures(@Int.result == 111) effects(pure)\n"
        "{ gen2(@Bool.0) }\n"
    ))
    imp = "import lib;" if imports is None else f"import lib({imports});"
    main_src = (
        f"{imp}\n\n"
        "private forall<T> fn gen2(@T -> @Int)\n"
        "  requires(true) ensures(@Int.result == 999) effects(pure)\n"
        "{ 999 }\n\n"
        "public fn useLocal(@Unit -> @Int)\n"
        "  requires(true) ensures(@Int.result == 999) effects(pure)\n"
        "{ gen2(true) }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(@Int.result == 111) effects(pure)\n"
        "{ door(true) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("mod$lib$gen2", ("Bool",)) in codegen_set, (
        f"codegen must emit the module generic's clone under its owning "
        f"module's base, got {sorted(codegen_set)}"
    )
    assert ("gen2", ("Bool",)) in codegen_set, (
        f"the IMPORTER's own gen2<Bool> must still be emitted under the bare "
        f"name it owns, got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — the qualified-only module "
        f"generic namespace (#1274); a divergence is a false Tier-1"
    )


def test_module_generic_owning_bare_name_stays_unqualified_1274() -> None:
    """The complement: a module generic that DOES own the importer's bare name
    (public, in-filter, unshadowed) keeps that bare name on both sides.

    Without this the widened predicate would be a blanket rename, and #774's
    bare-call routing (`ext_id(42)` reaching the imported generic) would break
    silently — the fix must move exactly the qualified-only families.
    """
    mod = _resolved_module(("lib",), (
        "public forall<T> fn gen2(@T -> @Int)\n"
        "  requires(true) ensures(@Int.result == 111) effects(pure)\n"
        "{ 111 }\n\n"
        "public fn door(@Bool -> @Int)\n"
        "  requires(true) ensures(@Int.result == 111) effects(pure)\n"
        "{ gen2(@Bool.0) }\n"
    ))
    main_src = (
        "import lib(gen2, door);\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(@Int.result == 222) effects(pure)\n"
        "{ door(true) + gen2(3) }\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("gen2", ("Bool",)) in codegen_set, (
        f"an unshadowed in-filter public module generic must keep the bare "
        f"clone name, got {sorted(codegen_set)}"
    )
    assert not any(n.startswith("mod$lib$gen2") for n, _ in codegen_set), (
        f"it must NOT be renamed — it owns the importer's bare name, "
        f"got {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)})"
    )


def test_generic_typearg_from_where_helper_return_is_discovered() -> None:
    """A generic whose type arg is fixed ONLY by a where-helper's return must be
    discovered by the verifier at the same concrete type codegen emits.

    Codegen registers every where-helper's WAT signature in ``_fn_sigs``
    (bare-name keyed), so it resolves ``wrap(scale(@Int.0))`` to ``wrap<Float64>``
    from ``scale``'s return.  If the verifier's discovery omits where-helper
    return types, the unresolved type var falls to the ``"Bool"`` phantom-var
    default in ``_infer_type_args_from_call`` and the verifier discovers
    ``wrap<Bool>`` — MISSING codegen's ``wrap<Float64>`` clone, a false Tier-1.

    The helper deliberately returns ``Float64`` (not ``Bool``) so the phantom
    default cannot coincide with the real type and mask the bug — the exact gap
    a ``Bool``-returning helper let slip through earlier (PR #767 review).
    """
    src = (
        "private forall<T>\n"
        "fn wrap(@T -> @Option<T>)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ Some(@T.0) }\n\n"
        "private fn caller(@Int -> @Option<Float64>)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ wrap(scale(@Int.0)) }\n"
        "where {\n"
        "  fn scale(@Int -> @Float64)\n"
        "    requires(true) ensures(true) effects(pure)\n"
        "  { 1.5 }\n"
        "}\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        codegen_set = _codegen_emitted(program, src, path)
        verifier_set = _verifier_discovered(program, src, path)
    finally:
        os.unlink(path)

    wrap_cg = {ct for (n, ct) in codegen_set if n == "wrap"}
    wrap_ver = {ct for (n, ct) in verifier_set if n == "wrap"}
    assert wrap_cg == {("Float64",)}, (
        f"codegen should emit wrap<Float64> from scale's return, got {wrap_cg}"
    )
    # The verifier must discover EXACTLY codegen's wrap<Float64> — no more, no
    # less.  Membership alone would pass even if a stale wrap<Bool> phantom were
    # ALSO discovered; exact-set equality fails on both a miss (false Tier-1) and
    # a phantom extra (the `"Bool"` default leaking through).
    assert wrap_ver == {("Float64",)}, (
        f"verifier must discover exactly wrap<Float64> (discovered {wrap_ver}) — "
        f"where-helper return-type discovery: a miss is a false Tier-1, a stale "
        f"wrap<Bool> extra means the phantom default leaked"
    )


def test_generic_typearg_from_imported_constructor_is_discovered() -> None:
    """A local generic whose type arg is inferred from an IMPORTED constructor
    must be discovered at the same type codegen emits.

    Codegen's monomorphizer context includes imported ADTs' constructors, so it
    resolves ``id2(MkBox(7))`` to ``id2<Box>`` from ``MkBox``'s owning ADT.  The
    verifier's ``_build_mono_context`` builds ``ctor_to_adt`` from
    ``env.data_types`` + local/prelude ``DataDecl``s only — imported public
    constructors live in ``_module_constructors`` instead.  If they are omitted,
    the verifier cannot map ``MkBox`` → ``Box``, the type var falls to the
    ``"Bool"`` phantom default, and it discovers ``id2<Bool>`` — MISSING
    codegen's ``id2<Box>`` clone, a false Tier-1 (PR #767 review).
    """
    a_src = "public data Box<T> {\n  MkBox(T)\n}\n"
    b_src = (
        "import a;\n\n"
        "private forall<T> fn id2(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Box<Int>)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id2(MkBox(7)) }\n"
    )

    mod_a = _resolved_module(("a",), a_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(b_src)
        f.flush()
        bp = f.name
    try:
        prog_b = transform(parse_file(bp))
        gen = CodeGenerator(source=b_src, file=bp, resolved_modules=[mod_a])
        gen.compile_program(prog_b)  # type: ignore[arg-type]
        cg = {ct for n, ct in getattr(gen, "_emitted_instances", set())
              if n == "id2"}
        verifier = ContractVerifier(
            source=b_src, file=bp, resolved_modules=[mod_a],
        )
        verifier.register_program(prog_b)  # type: ignore[arg-type]
        ver = {
            ct
            for n, cts in verifier._instances.items()
            for ct in cts
            if n == "id2"
        }
    finally:
        os.unlink(bp)

    assert cg == {("Box",)}, f"codegen should emit exactly id2<Box>, got {cg}"
    assert ver == {("Box",)}, (
        f"verifier should discover exactly id2<Box> (discovered {ver}) — "
        f"imported-constructor discovery gap, false Tier-1"
    )


def test_generic_typearg_from_imported_function_return_is_discovered() -> None:
    """A local generic whose type arg is inferred from an IMPORTED function's
    RETURN must be discovered at the same type codegen emits.

    Codegen's monomorphizer context seeds ``fn_ret_types`` from imported modules
    (``vera/codegen/modules.py`` ``setdefault`` over ``temp._fn_ret_type_exprs``),
    so it resolves ``id_g(make_int(...))`` to ``id_g<Int>`` from ``make_int``'s
    return type.  The verifier's ``_build_mono_context`` recorded return types
    from local/prelude declarations ONLY — imported public functions live in
    ``env.functions`` (injected by ``_register_modules``) but were never seeded
    into ``fn_ret_types``.  Without them the type var falls to the ``"Bool"``
    phantom default and the verifier discovers ``id_g<Bool>`` while codegen emits
    ``id_g<Int>``: an ASYMMETRIC miss = false Tier-1 (verified the wrong clone).
    Differentially confirmed (PR #767 review, CodeRabbit).
    """
    a_src = (
        "public fn make_int(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 7 }\n"
    )
    b_src = (
        "import a;\n\n"
        "private forall<T> fn id_g(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id_g(make_int(@Unit.0)) }\n"
    )

    mod_a = _resolved_module(("a",), a_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(b_src)
        f.flush()
        bp = f.name
    try:
        prog_b = transform(parse_file(bp))
        gen = CodeGenerator(source=b_src, file=bp, resolved_modules=[mod_a])
        gen.compile_program(prog_b)  # type: ignore[arg-type]
        cg = {ct for n, ct in getattr(gen, "_emitted_instances", set())
              if n == "id_g"}
        verifier = ContractVerifier(
            source=b_src, file=bp, resolved_modules=[mod_a],
        )
        verifier.register_program(prog_b)  # type: ignore[arg-type]
        ver = {
            ct
            for n, cts in verifier._instances.items()
            for ct in cts
            if n == "id_g"
        }
    finally:
        os.unlink(bp)

    assert cg == {("Int",)}, f"codegen should emit exactly id_g<Int>, got {cg}"
    assert ver == {("Int",)}, (
        f"verifier should discover exactly id_g<Int> (discovered {ver}) — "
        f"imported-function-return discovery gap, false Tier-1"
    )


def test_imported_private_shadow_fn_return_stays_symmetric() -> None:
    """Both sides key an imported function's return type by the SAME owner.

    Module ``a`` has a private ``mk -> Bool`` and module ``b`` a public
    ``mk -> Int``; the entry imports both and calls ``id_g(mk(()))``.  The
    entry's bare ``mk`` is ``b``'s — ``a``'s is private, so it does not own
    the entry's bare name (#1498) and is keyed under ``mod$a$mk`` on both
    sides.  Both therefore discover ``id_g<Int>``.

    Before #1498 both sides seeded every module function under its bare name,
    first-seen-wins, so ``a``'s private ``mk`` won the key and both discovered
    ``id_g<Bool>``: wrong, but SYMMETRICALLY wrong, which is what this cell
    was written to keep (PR #767 review) — a one-sided fix is exactly the
    asymmetry that lets a clone run unverified.  It asserts agreement rather
    than the concrete type, so it stays the guard against either side moving
    alone; ``test_a_module_generic_fed_by_a_qualified_only_function_agrees``
    below pins the renamed call that the shared keying also has to follow."""
    a_src = (
        "private fn mk(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ false }\n\n"
        "public fn a_thing(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 1 }\n"
    )
    b_src = (
        "public fn mk(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 7 }\n"
    )
    main_src = (
        "import a;\n"
        "import b;\n\n"
        "private forall<T> fn id_g(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ id_g(mk(@Unit.0)) }\n"
    )

    mods = [_resolved_module(("a",), a_src), _resolved_module(("b",), b_src)]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        f.flush()
        mp = f.name
    try:
        prog = transform(parse_file(mp))
        gen = CodeGenerator(source=main_src, file=mp, resolved_modules=mods)
        gen.compile_program(prog)  # type: ignore[arg-type]
        cg = {ct for n, ct in getattr(gen, "_emitted_instances", set())
              if n == "id_g"}
        verifier = ContractVerifier(
            source=main_src, file=mp, resolved_modules=mods,
        )
        verifier.register_program(prog)  # type: ignore[arg-type]
        ver = {
            ct
            for n, cts in verifier._instances.items()
            for ct in cts
            if n == "id_g"
        }
    finally:
        os.unlink(mp)

    assert len(cg) == 1 and cg == ver, (
        f"codegen ({cg}) and verifier ({ver}) must discover the SAME single "
        f"id_g instantiation — both key an imported function's return type "
        f"by the declaration that owns the bare name (#1498); keying it on one "
        f"side only would diverge into a false Tier-1 (PR #767 review)"
    )


def test_codegen_emits_generic_reached_only_via_contract_or_where_helper() -> None:
    """A generic called ONLY from a contract clause or a ``where`` helper body
    must be emitted by codegen.

    Vera lowers ``requires``/``ensures`` to a runtime contract check, and
    compiles ``where`` helper bodies, so such a generic is invoked at run time.
    Codegen's Pass 1.5 seeds from the shared node-level walk
    (``collect_calls_in_node`` = body + contracts + ``where_fns``), not just
    ``decl.body`` — walking only the body left the clone unemitted and produced
    a ``CodegenSkip`` (`call target 'is_ok$Int' not registered`) at run time,
    while the verifier (which walks contracts/helpers) discovered it: a discovery
    divergence (PR #767 review).
    """
    src = (
        "private forall<T> fn is_ok(@T -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure) { true }\n\n"
        "private forall<T> fn innerw(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure) { @T.0 }\n\n"
        "private fn checked(@Int -> @Int)\n"
        "  requires(is_ok(@Int.0)) ensures(true) effects(pure) { hw(@Int.0) }\n"
        "where {\n"
        "  fn hw(@Int -> @Int) requires(true) ensures(true) effects(pure)\n"
        "  { innerw(@Int.0) }\n"
        "}\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure) { checked(5) }\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(src)
        f.flush()
        path = f.name
    try:
        program = transform(parse_file(path))
        cg = _codegen_emitted(program, src, path)
        ver = _verifier_discovered(program, src, path)
    finally:
        os.unlink(path)

    # Codegen must emit exactly the contract-reachable (`is_ok`) and
    # where-helper-reachable (`innerw`) generics — nothing more, nothing less
    # (else a missing one is a CodegenSkip at run time).
    expected = {("is_ok", ("Int",)), ("innerw", ("Int",))}
    assert cg == expected, (
        f"codegen emitted {sorted(cg)}, expected {sorted(expected)}"
    )
    # Discovery is shared, so the verifier discovers exactly what codegen emits.
    assert ver == expected, (
        f"verifier discovery diverged from codegen: {sorted(ver)}"
    )


def test_mono_emission_order_is_deterministic(tmp_path: Path) -> None:
    """Monomorphized clone emission order must be stable across runs, so that
    ``vera compile --wat`` is byte-reproducible.

    The worklist that drives ``mono_decls.append`` (and hence WAT emission
    order) is seeded from ``set[tuple[str, ...]]`` instantiation sets; sorting
    them makes the order independent of ``PYTHONHASHSEED``.  Without the sort the
    three ``idg`` clones below emit in a hash-seed-dependent order and the WAT
    differs run-to-run (clone bodies identical, only their order) — bad for
    reproducible builds (PR #767 review).
    """
    src = (
        "private forall<T> fn idg(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n"
        "  let @Int = idg(1);\n"
        "  let @Bool = idg(true);\n"
        "  let @Float64 = idg(1.5);\n"
        "  @Int.0\n"
        "}\n"
    )
    f = tmp_path / "det.vera"
    f.write_text(src, encoding="utf-8")
    outputs = set()
    for seed in ("0", "1", "2", "3", "4"):
        proc = subprocess.run(
            [sys.executable, "-m", "vera.cli", "compile", "--wat", str(f)],
            capture_output=True, text=True, encoding="utf-8",
            env={**os.environ, "PYTHONHASHSEED": seed},
            timeout=120,  # bound each child: a mono hang fails fast here, not at the CI timeout
            check=False,
        )
        assert proc.returncode == 0, proc.stderr
        outputs.add(proc.stdout)
    assert len(outputs) == 1, (
        f"`vera compile --wat` not byte-stable across PYTHONHASHSEED: "
        f"{len(outputs)} distinct outputs"
    )


def test_invisible_import_does_not_name_a_clone_on_either_side() -> None:
    """`#1299`: an INVISIBLE module declaration must name no clone, on either
    side.

    Discovery's ``MonoContext.fn_names`` is the consumer's flat registry — it
    has to hold every symbol the guard rail resolves against, including an
    imported module's ``private fn get``.  Read flat, it claimed a bare
    ``get(())`` the checker had resolved to the ``State<Int>`` operation, and
    the argument's type was taken from that invisible declaration: both sides
    discovered ``idg<Bool>`` where the cell says ``idg<Int>``.

    Both sides moved together, which is the point of asserting it HERE rather
    than only on the runtime value.  Codegen and the verifier were WRONG
    SYMMETRICALLY before the fix, so an equality-only differential passed; had
    only one side been narrowed, the equality below would now fail and the
    other side would be verifying a clone nobody emits — a false Tier-1 with
    no runtime symptom at all.  The membership assertion is what distinguishes
    "both right" from "both wrong".
    """
    mod = _resolved_module(("lib_inv",), (
        "private fn get(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ true }\n"
        "public fn touch(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ get(()) }\n"
    ))
    main_src = (
        "import lib_inv(touch);\n"
        "private forall<T> fn idg(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @T.0 }\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{\n"
        "  handle[State<Int>](@Int = 42007) {\n"
        "    get(@Unit) -> { resume(@Int.0) },\n"
        "    put(@Int) -> { resume(()) }\n"
        "  } in {\n"
        "    idg(get(()))\n"
        "  }\n"
        "}\n"
    )
    codegen_set, verifier_set = _cross_module_sets(main_src, [mod])

    assert ("idg", ("Int",)) in codegen_set, (
        f"the cell's type must name the clone — the checker resolved the "
        f"operation, so `idg<Int>` is the instantiation; got "
        f"{sorted(codegen_set)}"
    )
    assert ("idg", ("Bool",)) not in codegen_set, (
        f"an invisible module declaration named the clone: {sorted(codegen_set)}"
    )
    assert verifier_set == codegen_set, (
        f"verifier ({sorted(verifier_set)}) must discover exactly codegen's "
        f"emitted set ({sorted(codegen_set)}) — narrowing one side's discovery "
        f"scope and not the other leaves a clone verified that nobody emits"
    )


# --- #1299: the two sides' discovery SCOPES, not just their results ---------

# Programs chosen so the comparison covers every input to the scope: the
# PRELUDE (injected into the entry namespace at a different pass on each
# side), CROSS-MODULE imports, the same-named-generic DIAMOND, and
# WHERE-nesting under a generic parent.
_SCOPE_REPO_CORPUS = [
    "tests/conformance/ch04_pipe_module_call.vera",
    "tests/conformance/ch08_cross_module_generic.vera",
    "tests/conformance/ch08_module_generic_diamond.vera",
    "tests/conformance/ch07_invisible_import_op_name.vera",
    "tests/conformance/ch09_generic_where_helper.vera",
]


@pytest.mark.parametrize("rel", _SCOPE_REPO_CORPUS)
def test_discovery_scopes_agree_between_the_two_sides(rel: str) -> None:
    """Codegen and the verifier narrow discovery to the SAME names (#1299).

    The coverage differentials above compare what each side DISCOVERS.  This
    compares what each side discovers it FROM, and the distinction is the
    point: two sides reading different scopes can agree on every clone for
    every program in the corpus and still disagree on the first program where
    a name is both a declaration and an operation — because being wrong
    together is invisible to an equality of results.

    Three inputs had to be made to agree for this to hold, and each was a
    real divergence measured on 22 of the 22 module-using conformance
    programs: the PRELUDE (the verifier builds its tables after
    ``inject_prelude`` and codegen before, so the entry namespace differed by
    the five combinators), and the per-declaration namespace of a CLONE (the
    two sides key their origin registries differently, so the same clone was
    walked in the entry's namespace on one side and its module's on the
    other).
    """
    path = _REPO_ROOT / rel
    source = path.read_text(encoding="utf-8")
    program = transform(parse_file(str(path)))
    resolved = ModuleResolver(_root=path.parent).resolve_imports(
        program, path,
    )
    cg, ver = _discovery_scopes(
        program, source, str(path), list(resolved),
    )
    _assert_scopes_agree(rel, cg, ver)


# Module shapes whose clones are reached by the SHADOWED-generic worklist and
# the nested-helper chase — walks the repo corpus above never enters, and each
# with its own namespace-selection site on both sides.
_SCOPE_MODULE_CASES: dict[str, tuple[str, str, tuple[str, ...]]] = {
    # A shadowed module generic whose body reaches a normal (unshadowed) one:
    # codegen's `_chase_normal_transitive` / the verifier's
    # `_chase_normal_from_clone`, rooted at the shadowed clone.
    "shadowed_reaching_normal": (
        "sh",
        "public forall<T> fn plain(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 1 }\n"
        "public forall<T> fn gen(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ plain(@T.0) }\n",
        # The local shadow is NON-generic on purpose.  It still makes the
        # module's `gen` qualified-only — `importer_occupied_bare_names`
        # counts every top-level name, generic or not — which is what routes
        # the clone through the shadowed worklist and its normal-closure
        # chase.  A generic shadow would ALSO mint a clone under the same
        # pre-rename name `gen$Int`, and the two sides' scope sets would then
        # differ for a reason that has nothing to do with which namespace
        # either picked.
        (
            "import sh;\n\n"
            "private fn gen(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 9 }\n\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ sh::gen(5) + gen(1) }\n"
        ),
    ),
    # A `forall` where-helper under a PRIVATE module generic: the nested-helper
    # clone walk, whose namespace comes from the recorded lexical CHAIN.
    "nested_helper_under_private_generic": (
        "nh",
        # `ginner` calls a module-PRIVATE function and a top-level generic:
        # the first makes the helper clone's scope observable (`onlyhere` is
        # in the module's namespace and in no other), the second drives
        # #1223's `pending_top` so the helper-clone walk actually runs.
        "private fn onlyhere(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 4 }\n"
        "public forall<T> fn topgen(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 5 }\n"
        "private forall<T> fn priv_outer(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ ginner(@T.0) }\n"
        "where {\n"
        "  forall<U> fn ginner(@U -> @Int)\n"
        "    requires(true) ensures(true) effects(pure)\n"
        "  { onlyhere(()) + topgen(true) }\n"
        "}\n"
        "public forall<T> fn pub_entry(@T -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ priv_outer(@T.0) }\n",
        (
            "import nh(pub_entry);\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ pub_entry(7) }\n"
        ),
    ),
}


@pytest.mark.parametrize("label", sorted(_SCOPE_MODULE_CASES))
def test_discovery_scopes_agree_on_module_clone_walks(label: str) -> None:
    """The same equality, over the clone walks the repo corpus never reaches.

    Both sides chase clones from THREE further places — the shadowed-generic
    worklist's normal-closure chase, and the nested generic-under-generic
    helper clone — and each picks the namespace by its own route: codegen
    from ``_mono_clone_origins`` keyed by clone name, the verifier from
    ``_origin_module_for_generic`` keyed by the base chain.  A shadowed clone
    reaches those walks under its PRE-rename name, which is in neither
    registry, so both sides take the path from the caller instead.
    """
    mod_name, mod_src, main_src = _SCOPE_MODULE_CASES[label]
    mod = _resolved_module((mod_name,), mod_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        mp = f.name
    try:
        program = transform(parse_file(mp))
        cg, ver = _discovery_scopes(program, main_src, mp, [mod])
    finally:
        os.unlink(mp)
    _assert_scopes_agree(label, cg, ver)


def test_nested_helper_clone_walks_in_its_chains_module() -> None:
    """The verifier's nested-helper clone walk enters the CHAIN's namespace.

    Asserted directly rather than through the equality above, because that
    comparison is keyed by declaration NAME and the two sides name this one
    clone differently by design: codegen hoists it per instantiation
    (``mod$nh$priv_outer$Int$where$ginner$Int``) while the verifier keeps the
    mangled bare name (``ginner$Int``).  Not a scope divergence — a naming
    scheme difference — so the equality cell cannot see this site, and it
    gets its own discriminator: ``onlyhere`` is module-PRIVATE, so it is in
    the walk's scope only if the walk entered ``nh``'s namespace.
    """
    mod_name, mod_src, main_src = _SCOPE_MODULE_CASES[
        "nested_helper_under_private_generic"
    ]
    mod = _resolved_module((mod_name,), mod_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        mp = f.name
    try:
        program = transform(parse_file(mp))
        _cg, ver = _discovery_scopes(program, main_src, mp, [mod])
    finally:
        os.unlink(mp)

    assert "ginner$Int" in ver, (
        f"the nested helper's clone was never walked in a discovery scope — "
        f"the assertion below would be vacuous; keys were {sorted(ver)}"
    )
    for scope in ver["ginner$Int"]:
        assert "onlyhere" in scope, (
            f"the nested helper's clone was walked in the wrong namespace: "
            f"its module's private `onlyhere` is not in scope {sorted(scope)}"
        )


def test_codegen_helper_family_leaf_walks_in_its_parents_module() -> None:
    """Codegen's twin of the assertion above, on the helper-family LEAF.

    ``collect_generic_helper_instances`` is the one walk both sides drive
    directly, and codegen hoists the clone it produces under a per-clone name
    (``mod$nh$priv_outer$Int$where$ginner$Int``) where the verifier keeps the
    mangled bare one — so the two are never a shared key and the equality
    cell cannot compare them.  Each side therefore gets a direct
    discriminator: ``onlyhere`` is module-private, in scope only if the leaf
    entered ``nh``'s namespace rather than the entry program's.
    """
    mod_name, mod_src, main_src = _SCOPE_MODULE_CASES[
        "nested_helper_under_private_generic"
    ]
    mod = _resolved_module((mod_name,), mod_src)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        mp = f.name
    try:
        program = transform(parse_file(mp))
        cg, _ver = _discovery_scopes(program, main_src, mp, [mod])
    finally:
        os.unlink(mp)

    walked = [n for n in cg if n.startswith("mod$nh$") and "$where$" in n]
    assert walked, (
        f"codegen walked no hoisted helper clone — the assertion would be "
        f"vacuous; keys were {sorted(cg)}"
    )
    for name in walked:
        for scope in cg[name]:
            assert "onlyhere" in scope, (
                f"{name} was walked in the wrong namespace: its module's "
                f"private `onlyhere` is not in scope {sorted(scope)}"
            )


def test_discovery_scope_includes_the_prelude() -> None:
    """A prelude combinator is a declaration every namespace can name.

    Its dispatch-side sibling (``test_prelude_names_stay_in_every_scope``)
    makes the same assertion about ``_scoped_fns``; without this one the
    discovery half could drop the prelude and nothing would notice, because
    no prelude name is spelled like an effect operation *yet*.
    """
    src = (
        "private forall<T> fn idg(@T -> @T)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ idg(7) }\n"
    )
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(src)
        mp = f.name
    try:
        program = transform(parse_file(mp))
        cg, ver = _discovery_scopes(program, src, mp)
    finally:
        os.unlink(mp)

    assert cg and ver, "no declaration was walked in a discovery scope"
    for label, scopes in (("codegen", cg), ("verifier", ver)):
        for scope in scopes["main"]:
            assert "option_map" in scope, (
                f"{label} dropped the prelude from the discovery scope: "
                f"{sorted(scope)}"
            )
    _assert_scopes_agree("prelude", cg, ver)


def test_a_module_generic_fed_by_a_qualified_only_function_agrees() -> None:
    """#1498: both sides bind a module body's call to its own qualified-only
    function before discovery, and key that function's return type the same.

    Module ``a``'s private ``mk -> Int`` does not own the entry's bare name
    (it is private, and the entry declares its own ``mk -> Bool``), so codegen
    emits it as ``mod$a$mk`` and renames ``door``'s call to it.  The private
    generic ``gid`` takes its type argument from that call alone.  The
    verifier's discovery copy has to see the same renamed call AND a return
    type keyed under the same symbol, or it types the call by the entry's
    ``mk`` and discovers ``gid<Bool>`` while codegen emits ``gid<Int>``: a
    clone that runs unverified.  ``Bool`` is also the phantom default, so the
    entry's ``mk -> Bool`` makes the wrong answer concrete rather than an
    accident of inference.
    """
    a_src = (
        "private fn mk(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ 7 }\n\n"
        "private forall<T> fn gid(@T -> @T)\n"
        "  requires(true) ensures(@T.result == @T.0) effects(pure)\n"
        "{ @T.0 }\n\n"
        "public fn door(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ gid(mk(@Unit.0)) }\n"
    )
    main_src = (
        "import a(door);\n\n"
        "private fn mk(@Unit -> @Bool)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ true }\n\n"
        "public fn main(@Unit -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ if mk(@Unit.0) then { door(@Unit.0) } else { 0 } }\n"
    )

    mods = [_resolved_module(("a",), a_src)]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(main_src)
        f.flush()
        mp = f.name
    try:
        prog = transform(parse_file(mp))
        gen = CodeGenerator(source=main_src, file=mp, resolved_modules=mods)
        gen.compile_program(prog)  # type: ignore[arg-type]
        cg = {
            (n, ct) for n, ct in getattr(gen, "_emitted_instances", set())
            if n.endswith("gid")
        }
        verifier = ContractVerifier(
            source=main_src, file=mp, resolved_modules=mods,
        )
        verifier.register_program(prog)  # type: ignore[arg-type]
        ver = {
            (n, ct)
            for n, cts in verifier._instances.items()
            for ct in cts
            if n.endswith("gid")
        }
    finally:
        os.unlink(mp)

    assert cg == {("mod$a$gid", ("Int",))}, cg
    assert cg <= ver, (
        f"codegen emits {cg} and the verifier discovers {ver}: a clone the "
        f"verifier does not discover runs unverified"
    )
