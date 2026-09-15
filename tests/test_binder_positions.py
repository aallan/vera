"""The binder-position registry is held to the AST, and to the guard table.

`vera/binders.py` exists because the set of positions Vera binds a slot in was
never written down: each was added to the guard table and to the two emitters
as review discovered it, and a position no walk visited was SILENT rather than
wrong.  A registry that can itself go stale would reproduce that one level up,
so this file is what keeps it honest.

Three properties, in increasing strength:

1. **Completeness against the AST.**  Every field of every `vera.ast` node
   class that carries a `TypeExpr` or a `Pattern` is either a registered
   binder position or an entry in ``NON_BINDER_FIELDS`` with the reason it
   binds nothing.  A node class added later fails here rather than being
   quietly unvisited.
2. **Agreement with the guard table.**  Every site a position names is a key
   ``GUARD_SITES`` answers, or is listed as a position whose guard answer is a
   property of something other than the position.
3. **The derived rosters are the rosters.**  The three sets the verifier and
   code generation read are computed from ``GUARD_SITES``, and this file pins
   what they compute to what was measured before they were derived — the
   verdict-signature half of moving where a decision lives.
"""
from __future__ import annotations

import dataclasses
import inspect

import pytest

from vera import ast, binders, narrowing
from vera.parser import parse_to_ast


# =====================================================================
# 1. Completeness against the AST
# =====================================================================

def _declared_type_carrying_fields() -> list[tuple[type, str]]:
    """Every (node class, field) in `vera.ast` carrying a TypeExpr/Pattern.

    Reflected rather than listed: a list would be the same thing the registry
    is replacing, one level up.  Only fields DECLARED on the class count —
    an inherited one belongs to the base that declares it — so a subclass
    does not have to re-answer its parent's question.
    """
    found: list[tuple[type, str]] = []
    for _, obj in sorted(vars(ast).items()):
        if not (inspect.isclass(obj) and dataclasses.is_dataclass(obj)
                and obj.__module__ == ast.__name__):
            continue
        own = set(obj.__dict__.get("__annotations__", {}))
        for fld in dataclasses.fields(obj):
            if fld.name not in own:
                continue
            annotation = str(fld.type)
            if "TypeExpr" in annotation or "Pattern" in annotation:
                found.append((obj, fld.name))
    return found


#: Reflected once: the parametrisation and the totals both read it, so they
#: cannot disagree about what the AST holds.
TYPE_CARRYING_FIELDS = _declared_type_carrying_fields()


def test_the_ast_still_has_fields_to_classify() -> None:
    """The premise: reflection found something.

    A rename in `vera.ast` that made the annotation test match nothing would
    otherwise turn every cell below into a vacuous pass — the shape TESTING.md
    § Class Instruments calls worse than an absent one.
    """
    assert len(TYPE_CARRYING_FIELDS) >= 25, TYPE_CARRYING_FIELDS


@pytest.mark.parametrize(
    "node_class,field_name",
    TYPE_CARRYING_FIELDS,
    ids=[f"{c.__name__}.{f}" for c, f in TYPE_CARRYING_FIELDS],
)
def test_every_type_carrying_field_is_classified(
    node_class: type, field_name: str,
) -> None:
    """Registered as a binder position, or exempted with a reason.

    Not "registered OR ignored": an unclassified field is exactly the state
    #1426, #1439, #1445, #1448 and #1455 were all found in, so the only way
    past this cell is to decide.
    """
    registered = {
        b.field for b in binders.BINDER_FIELDS.get(node_class, ())
    }
    exempted = binders.NON_BINDER_FIELDS.get(node_class, {})
    is_binder = field_name in registered
    is_exempt = field_name in exempted
    assert is_binder != is_exempt, (
        f"{node_class.__name__}.{field_name} is "
        f"{'in both tables' if is_binder else 'in neither table'}: a field "
        f"carrying a TypeExpr or a Pattern either declares a slot binding "
        f"(add it to BINDER_FIELDS with its site) or does not (add it to "
        f"NON_BINDER_FIELDS with the reason)"
    )
    if is_exempt:
        assert exempted[field_name].strip(), (
            f"{node_class.__name__}.{field_name} is exempted with an empty "
            f"reason"
        )


def test_no_table_entry_names_a_field_the_ast_does_not_have() -> None:
    """The other direction: a field renamed out from under the registry.

    Completeness alone is satisfied by a registry full of dead entries, and a
    dead entry reads as coverage of a position that no longer exists.
    """
    known = {(c, f) for c, f in TYPE_CARRYING_FIELDS}
    stale: list[str] = []
    for node_class, entries in binders.BINDER_FIELDS.items():
        for binder in entries:
            if (node_class, binder.field) not in known:
                stale.append(f"BINDER_FIELDS[{node_class.__name__}]"
                             f".{binder.field}")
    for node_class, reasons in binders.NON_BINDER_FIELDS.items():
        for field_name in reasons:
            if (node_class, field_name) not in known:
                stale.append(f"NON_BINDER_FIELDS[{node_class.__name__}]"
                             f".{field_name}")
    assert not stale, stale


def test_every_registered_position_has_a_note() -> None:
    """A position with no note is a position nobody has to justify."""
    missing = [
        f"{c.__name__}.{b.field}"
        for c, entries in binders.BINDER_FIELDS.items()
        for b in entries
        if not b.note.strip()
    ]
    assert not missing, missing


# =====================================================================
# 2. Agreement with the guard table
# =====================================================================

#: Positions whose guard answer is NOT a property of the position, so they
#: have no `GUARD_SITES` entry to read.  Listed here rather than left to fall
#: out of a membership test, so adding a position without a guard answer is a
#: decision with a reason attached.
SITES_ANSWERED_ELSEWHERE = {
    "effect-operation argument":
        "guarded for a BUILT-IN effect's operation and not for a "
        "user-declared one, so the verifier computes it from the operation's "
        "parent effect (#754, #1268)",
    "State-op resume":
        "codegen wraps a `get` clause's net value; the answer belongs to the "
        "clause's dispatch path rather than to the position (#1203)",
}


def test_every_site_is_answered_somewhere() -> None:
    named = {
        b.key() for entries in binders.BINDER_FIELDS.values()
        for b in entries if b.key() is not None
    }
    unanswered = sorted(
        site for site in named
        if site not in binders.GUARD_SITES
        and site not in SITES_ANSWERED_ELSEWHERE
    )
    assert not unanswered, (
        f"{unanswered} name no guard answer: either give the site a "
        f"GUARD_SITES entry, or record in SITES_ANSWERED_ELSEWHERE why the "
        f"answer is not a property of the position"
    )


def test_every_guard_site_entry_carries_its_evidence() -> None:
    """A guard answer with no note is a claim about codegen nobody measured."""
    missing = [k for k, g in binders.GUARD_SITES.items() if not g.note.strip()]
    assert not missing, missing


def test_the_construction_sites_are_guard_sites() -> None:
    """A construction position stores into a slot the container declares, so
    its site must be one the guard table answers — that is the coupling that
    keeps a store from being emitted where the stream counts nothing."""
    for node_class, sites in binders.CONSTRUCTION_SITES.items():
        for site in sites:
            assert site in binders.GUARD_SITES, (
                f"CONSTRUCTION_SITES[{node_class.__name__}] names {site!r}, "
                f"which GUARD_SITES does not answer"
            )


# =====================================================================
# 3. The derived rosters are the rosters
# =====================================================================

#: What the three rosters held as literals before they were derived, measured
#: at `origin/release/v0.2.0` 8eca11c0 plus the `handler clause binder` this
#: release adds.  Pinning them is the verdict-signature half of moving where
#: a decision lives: the derivation may not quietly change a membership.
_REFINED_BIND_GUARDED_SITES_AS_MEASURED = frozenset({
    "return type",
    "call argument",
    "closure argument",
    "closure return",
    "let binding",
    "match binding",
    "tuple destructure",
    "ADT sub-pattern bind",
    "constructor field",
    "tuple component",
    "array element",
    "map value",
    "State write boundary",
    "handler clause binder",
})

_NAT_CONSTRUCTION_GUARDED_SITES_AS_MEASURED = frozenset({
    "constructor field",
    "tuple component",
    "array element",
    "map value",
})

_INT_WIDENING_CONSTRUCTION_GUARDED_SITES_AS_MEASURED = frozenset({
    "array element",
    "tuple component",
})


def test_the_refinement_roster_is_what_it_was() -> None:
    assert (narrowing.REFINED_BIND_GUARDED_SITES
            == _REFINED_BIND_GUARDED_SITES_AS_MEASURED)


def test_the_nat_construction_roster_is_what_it_was() -> None:
    from vera import verifier

    assert (verifier._NAT_CONSTRUCTION_GUARDED_SITES
            == _NAT_CONSTRUCTION_GUARDED_SITES_AS_MEASURED)


def test_the_widening_construction_roster_is_what_it_was() -> None:
    from vera import verifier

    assert (verifier._INT_WIDENING_CONSTRUCTION_GUARDED_SITES
            == _INT_WIDENING_CONSTRUCTION_GUARDED_SITES_AS_MEASURED)


def test_the_rosters_come_from_the_table_rather_than_a_literal() -> None:
    """Dropping a table entry moves the roster that reads it.

    Without this the three assertions above are satisfied by three literals
    that happen to agree with the table, which is the arrangement #1412
    replaced.
    """
    from vera import verifier

    assert (narrowing.REFINED_BIND_GUARDED_SITES
            == binders.guarded_sites("refinement_predicate"))
    assert (verifier._NAT_CONSTRUCTION_GUARDED_SITES
            == binders.guarded_sites("nat_sign_at_construction"))
    assert (verifier._INT_WIDENING_CONSTRUCTION_GUARDED_SITES
            == binders.guarded_sites("int_widen_at_construction"))


# =====================================================================
# The enumerator finds what the program declares
# =====================================================================

_EVERY_POSITION = """type Pos = { @Int | @Int.0 > 0 };

private data Box {
  Boxed(Pos)
}

effect Log {
  op emit(Int -> Unit);
}

private fn consume(@Pos -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Pos.0
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Pos = consume(@Int.0);
  let Tuple<@Int, @Nat> = Tuple(1, 2);
  match Boxed(@Pos.0) {
    Boxed(@Nat) -> nat_to_int(@Nat.0),
    _ -> 0
  }
}
where {
  fn helper(@Nat -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    handle[State<Int>] (@Int = 0) {
      put(@Pos) -> { @Pos.0 } with @Int = 1
    } in {
      nat_to_int(@Nat.0)
    }
  }
}
"""


def test_the_enumerator_reaches_every_kind_the_program_writes() -> None:
    """One program, every position kind it spells, found by the walk.

    The kinds are compared as a SET against what the source writes, so a walk
    that stopped descending at a `where` block (the shape #1455 was), or at a
    handler clause (#1445), loses a kind rather than a count.
    """
    program = parse_to_ast(_EVERY_POSITION)
    kinds = {p.binder.kind for p in binders.binder_positions(program)}
    assert kinds == {
        "function parameter",
        "function return",
        "let",
        "destructure",
        "match arm",
        "ADT sub-pattern",
        "pattern binder",
        "handler clause",
        "handler state override",
        "handler state init",
        "constructor field",
        "effect-operation formal",
        "effect-operation result",
    }, sorted(kinds)


def test_a_where_helpers_parameter_is_a_position_of_its_own() -> None:
    """#1455 in the enumerator's terms: a helper's parameter is a position,
    at the same site as a top-level one, so nothing downstream can treat it
    as a special case."""
    program = parse_to_ast(_EVERY_POSITION)
    params = [
        p for p in binders.binder_positions(program)
        if p.binder.kind == "function parameter"
    ]
    owners = [p.owner.name for p in params]  # type: ignore[attr-defined]
    assert "helper" in owners, owners
    assert {p.site for p in params} == {"call argument"}


def test_a_pattern_binder_inherits_the_position_that_declares_it() -> None:
    """The same `@Nat` is a `match binding` under an arm and an
    `ADT sub-pattern bind` under a constructor pattern, and the guards differ
    per position — so the site is inherited rather than restated."""
    program = parse_to_ast(_EVERY_POSITION)
    sites = {
        p.site for p in binders.binder_positions(program)
        if p.binder.kind == "pattern binder"
    }
    assert sites == {"ADT sub-pattern bind"}, sites


def test_the_state_writes_share_one_guard_key_under_three_names() -> None:
    """#1439's rule, now a property of the registry rather than of three
    call sites remembering to pass the same string."""
    program = parse_to_ast(_EVERY_POSITION)
    writes = [
        p for p in binders.binder_positions(program)
        if p.binder.kind in ("handler state init", "handler state override")
    ]
    assert {p.site for p in writes} == {
        "handler state init", "handler state update",
    }
    assert {p.key() for p in writes} == {"State write boundary"}


_QUANTIFIER_IN_A_REFINEMENT = """type Small = { @Int | forall(@Int, [1], fn(@Int -> @Bool) effects(pure) { @Int.0 > 0 }) };

public fn f(@Small -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Small.0
}
"""


def test_a_contract_only_binder_never_inherits_a_guarded_site() -> None:
    """The site travels through a PATTERN and nothing else.

    A pattern is the one place a position is declared by one node and spelled
    by another, which is why the site is inherited at all: the same
    `BindingPattern` is a `match binding` under an arm and an
    `ADT sub-pattern bind` under a constructor pattern.  Carried further, a
    quantifier written inside a parameter's refinement predicate took the
    enclosing position's site and `key()` answered `call argument` — a guard
    key, for a binder that is translated to a Z3 bound variable and never
    reaches a run (CodeRabbit on PR #1465).

    No production consumer reads `key()` for a quantifier today, which is
    exactly why the registry has to be right about it: the wrong answer would
    be waiting for the first one.
    """
    program = parse_to_ast(_QUANTIFIER_IN_A_REFINEMENT)
    quantifiers = [
        p for p in binders.binder_positions(program)
        if p.binder.kind == "quantifier binder"
    ]
    assert quantifiers, "the walk did not reach the quantifier at all"
    assert {p.site for p in quantifiers} == {None}, (
        f"a contract-only binder inherited a position: "
        f"{[p.site for p in quantifiers]}"
    )
    assert {p.key() for p in quantifiers} == {None}
