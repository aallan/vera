"""A component type reaches a NESTED container literal (R-1412 F3, PR #1606).

The verifier's construction descent (`_descend_construction_container`)
threads a component type down through three container positions — a `Tuple`
argument, an array-literal element and a `map_insert` value (and its chained
receiver) — walking the `if` / `match` / block wrappers between them, and
obligates the scalar it finally reaches.  Only the OUTERMOST container of a
chain has a target recorded by the checker; every literal nested inside it
knows its type only from the position it stands in.

So code generation has to hand the same component type down the same
positions, or the store it guards is the outermost one alone.  A recorded
`tier3` with no guard behind it is a false claim: the value goes in
unexamined while the report counts it as runtime-checked.  Before this was
fixed the hand-down reached one level (a Tuple directly inside a Tuple) and
nothing else — a `Tuple` three deep, a `Tuple` inside an array literal, an
array literal inside a `Tuple` and a `Tuple` stored as a map value were all
recorded `tier3` and stored a forbidden value silently.

Every cell here is a DIFFERENTIAL between the two components, over a matrix
GENERATED from the positions the descent walks rather than listed by hand:

* the record and the artifact agree — every obligation of the leaf's kind
  recorded `tier3` has its guard in the function's WAT, every guard is on
  the record, and every leaf the program stores is;
* the artifact does what the record says — a forbidden input traps with the
  guard's own message wherever a store is recorded `tier3`, and an allowed
  control runs to its value, so a guard cannot pass by over-firing.

Three leaf kinds, one per obligation the store carries: a `@Nat` narrowing
(`nat_bind`), a refinement predicate (`refine_bind`) and a `@Nat` -> `@Int`
widening (`nat_to_int_coerce`).  The narrowing and refinement leaves are
`float_to_int(@Float64.0)`, opaque to the solver, so the input decides the
value; the widening leaf is the `@Nat` parameter, and a value above
`i64.MAX` is the forbidden one.  The container is built and never read
back, so only a guard AT THE STORE can trap — a read-side pattern guard
cannot stand in for a missing store guard.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from dataclasses import dataclass

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.verifier import verify

from tests.codegen_helpers import wat_fn_body


def _trap_kind(kind: int) -> re.Pattern[str]:
    """A `$vera.trap` call of one `vera.trap_registry.TRAP_KINDS` code."""
    return re.compile(
        rf"i32\.const {kind}\s+i32\.const -?\d+\s+i32\.const -?\d+\s+"
        rf"call \$vera\.trap")


@dataclass(frozen=True)
class _Leaf:
    """One kind of store obligation, and how its guard shows."""

    slot: str             #: the component type the leaf is stored at
    value: str            #: the stored expression
    obligation: str       #: the obligation kind the store records
    guard: re.Pattern[str]  #: that guard, in the WAT
    bad_args: tuple[object, ...]  #: an input the slot forbids
    trap: str             #: what the guard says when it fires


#: `g`'s arguments that every slot allows.
_GOOD_ARGS = (5.0, 5)

_LEAVES = {
    # `nat_guard` is trap kind 2.
    "nat": _Leaf("Nat", "float_to_int(@Float64.0)", "nat_bind",
                 _trap_kind(2), (-5.0, 5),
                 "Negative value bound into a @Nat slot"),
    # A §2.6.5 predicate fails through `$vera.contract_fail`.
    "refined": _Leaf("PosInt", "float_to_int(@Float64.0)", "refine_bind",
                     re.compile(r"call \$vera\.contract_fail"), (-5.0, 5),
                     "Refinement violation"),
    # `nat_widen` is trap kind 3; 2^64 - 1 is a `@Nat` above i64.MAX.
    "widen": _Leaf("Int", "@Nat.0", "nat_to_int_coerce", _trap_kind(3),
                   (5.0, 2**64 - 1), "widened into an @Int slot"),
}

_PRELUDE = "type PosInt = { @Int | @Int.0 > 0 };\n\n"
_HDR = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _wrap(wrapper: str, expr: str) -> str:
    """The wrappers the descent walks between two container levels."""
    if wrapper == "direct":
        return expr
    if wrapper == "if":
        return f"if @Float64.0 > 0.0 then {{ {expr} }} else {{ {expr} }}"
    if wrapper == "match":
        return f"match @Float64.0 > 0.0 {{ true -> {expr}, false -> {expr} }}"
    if wrapper == "block":
        # The statement builds a `Tuple` of its OWN type before the tail: a
        # component type that leaked past the tail it was handed to would
        # guard `0 - 3` as the leaf's slot and trap the allowed control.
        return (f"{{ let @Tuple<Int, Int> = Tuple(0 - 3, 1); "
                f"let @Int = 9; {expr} }}")
    raise ValueError(wrapper)


def _chain(kinds: list[str], leaf: _Leaf, leaf_level: int, nest_index: int,
           wrapper: str) -> tuple[str, str]:
    """(type, expression) of a container chain, ``kinds[0]`` outermost.

    A `Tuple` level holds the next level beside one scalar component (the
    nested one first or second, by *nest_index*); that component is the
    leaf at *leaf_level* and an `@Int` literal elsewhere.  An `Array`, `Map`
    or `Chain` level holds the next level as its element / value, and at the
    innermost level holds the leaf itself.  `Chain` is a `map_insert` whose
    RECEIVER is another `map_insert`, with the next level in both values —
    the chained-receiver position the descent obligates.
    """
    ty: str | None = None
    ex: str | None = None
    depth = len(kinds)
    for level in range(depth, 0, -1):
        kind = kinds[level - 1]
        if kind in ("Array", "Map", "Chain"):
            inner_ty = leaf.slot if ty is None else ty
            inner = leaf.value if ex is None else _wrap(wrapper, ex)
            if kind == "Array":
                ty, ex = f"Array<{inner_ty}>", f"[{inner}]"
            elif kind == "Map":
                ty = f"Map<String, {inner_ty}>"
                ex = f'map_insert(map_new(), "k", {inner})'
            else:
                ty = f"Map<String, {inner_ty}>"
                ex = (f'map_insert(map_insert(map_new(), "j", {inner}), '
                      f'"k", {inner})')
            continue
        scalar = ((leaf.slot, leaf.value) if level == leaf_level
                  else ("Int", str(level + 10)))
        if ty is None:
            comps = [scalar, ("Int", "2")]
        else:
            nested = (ty, _wrap(wrapper, ex))
            comps = [nested, scalar] if nest_index == 0 else [scalar, nested]
        ty = f"Tuple<{comps[0][0]}, {comps[1][0]}>"
        ex = f"Tuple({comps[0][1]}, {comps[1][1]})"
    assert ty is not None and ex is not None
    return ty, ex


def _program(context: str, ty: str, ex: str) -> str:
    """Place the chain at a position with a RECORDED target."""
    pre = _PRELUDE
    if context == "let":
        body = f"let @{ty} = {ex};\n  7"
    elif context == "call arg":
        pre += f"private fn h(@{ty} -> @Int)\n{_HDR}{{\n  7\n}}\n\n"
        body = f"h({ex})"
    elif context == "Some field":
        body = f"let @Option<{ty}> = Some({ex});\n  7"
    elif context == "user ctor field":
        pre += f"private data W {{\n  MkW({ty})\n}}\n\n"
        body = f"let @W = MkW({ex});\n  7"
    else:
        raise ValueError(context)
    return (f"{pre}public fn g(@Float64, @Nat -> @Int)\n{_HDR}{{\n"
            f"  {body}\n}}\n")


#: The chains, by level kind, outermost first.  Alternation puts each
#: container kind both inside and outside each other one.
_SHAPES = {
    "tuple": lambda d: ["Tuple"] * d,
    "tuple/array": lambda d: ["Tuple", "Array"] * d,
    "array/tuple": lambda d: ["Array", "Tuple"] * d,
    "tuple/map": lambda d: ["Tuple", "Map"] * d,
    "map/tuple": lambda d: ["Map", "Tuple"] * d,
    "tuple/chain": lambda d: ["Tuple", "Chain"] * d,
    "chain/tuple": lambda d: ["Chain", "Tuple"] * d,
}
_CONTEXTS = ("let", "call arg", "Some field", "user ctor field")
_MAX_DEPTH = 5


def _cells() -> Iterator[tuple[str, str, str]]:
    for leaf_name, leaf in _LEAVES.items():
        for context in _CONTEXTS:
            for shape, make in _SHAPES.items():
                for depth in range(1, _MAX_DEPTH + 1):
                    kinds = make(depth)[:depth]
                    levels = sorted({1, (depth + 1) // 2, depth})
                    for leaf_level in levels:
                        # A scalar sibling needs a Tuple level; an Array or
                        # Map level holds the leaf only as the innermost.
                        if (kinds[leaf_level - 1] != "Tuple"
                                and leaf_level != depth):
                            continue
                        for nest_index in ((0, 1) if depth > 1 else (0,)):
                            wrappers = (("direct", "if", "match", "block")
                                        if 1 < depth <= 3 else ("direct",))
                            for wrapper in wrappers:
                                ty, ex = _chain(kinds, leaf, leaf_level,
                                                nest_index, wrapper)
                                label = (f"{context}|{shape}|d{depth}|"
                                         f"{leaf_name}@{leaf_level}|"
                                         f"n{nest_index}|{wrapper}")
                                yield label, leaf_name, _program(
                                    context, ty, ex)


_ALL_CELLS = list(_cells())


def _record_gap(label: str) -> bool:
    """A chain whose OUTERMOST container is a `map_insert` standing where no
    `let` or return names its type (#1608).

    The verifier enters its construction descent for a `map_insert` only
    from a `let`'s or a return's declared type, while codegen guards the
    value from the call's own recorded target wherever it stands — so these
    cells are guarded with nothing on the record.  The safe direction (the
    store is checked; the account omits it), pinned in that state below
    until #1608 gives the walk its `map_insert` entry.
    """
    context, shape = label.split("|")[:2]
    return shape.startswith(("map/", "chain/")) and context != "let"


_CELLS = [c for c in _ALL_CELLS if not _record_gap(c[0])]
_GAP_CELLS = [c for c in _ALL_CELLS if _record_gap(c[0])]


def _measure(
    source: str, leaf: _Leaf,
) -> tuple[list[str], int, str, str]:
    """(statuses of the leaf's obligation kind in `g`, that kind's guards in
    `g`'s WAT, the forbidden run, the allowed run)."""
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    errors = [d.description[:90] for d in diags if d.severity == "error"]
    assert not errors, errors
    result = verify(program, source,
                    expr_types=arts.expr_semantic_types,
                    expr_target_types=arts.expr_target_types)
    statuses = sorted(o.status for o in result.obligations
                      if o.kind == leaf.obligation and o.fn_name == "g")
    compiled = codegen_compile(
        program, source=source, file="p.vera",
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    errors = [d.description[:90] for d in compiled.diagnostics
              if d.severity == "error"]
    assert not errors, errors
    guards = len(leaf.guard.findall(wat_fn_body(compiled.wat, "g")))

    def run(args: tuple[object, ...]) -> str:
        try:
            value = execute(compiled, fn_name="g", args=list(args)).value
            return f"ran:{value}"
        except Exception as exc:  # noqa: BLE001 — the trap IS the observation
            return str(exc)

    return statuses, guards, run(leaf.bad_args), run(_GOOD_ARGS)


def test_the_matrix_covers_every_position_and_depth() -> None:
    """The generator reaches what it claims to, so a green run means it."""
    labels = [label for label, _, _ in _ALL_CELLS]
    assert len(labels) == len(set(labels))
    for leaf_name in _LEAVES:
        for context in _CONTEXTS:
            for shape in _SHAPES:
                for depth in range(1, _MAX_DEPTH + 1):
                    assert any(
                        label.startswith(f"{context}|{shape}|d{depth}|"
                                         f"{leaf_name}@")
                        for label in labels), (leaf_name, context, shape,
                                               depth)
    for wrapper in ("if", "match", "block"):
        assert any(label.endswith(f"|{wrapper}") for label in labels)
    # The chained receiver holds a nested container in a differential cell,
    # not only in the record-gap ones.
    assert any("|tuple/chain|d3|" in label for label, _, _ in _CELLS)
    assert any(label.startswith("let|chain/tuple|d2|")
               for label, _, _ in _CELLS)


@pytest.mark.parametrize("label,leaf_name,source", _ALL_CELLS,
                         ids=[c[0] for c in _ALL_CELLS])
def test_every_recorded_guard_is_emitted_and_every_emitted_guard_recorded(
    label: str, leaf_name: str, source: str,
) -> None:
    leaf = _LEAVES[leaf_name]
    statuses, guards, forbidden, allowed = _measure(source, leaf)
    leaves = source.count(leaf.value)
    tier3 = statuses.count("tier3")
    verified = statuses.count("verified")
    unguarded = statuses.count("tier3_unguarded")
    # No false Tier 3: every `tier3` record has its guard in the module.
    assert tier3 <= guards, (
        f"{label}: {tier3} {leaf.obligation} recorded tier3, but only "
        f"{guards} guard(s) in the WAT — a runtime check claimed and absent"
    )
    # And the artifact does what the record says.
    if tier3:
        assert leaf.trap in forbidden, (
            f"{label}: {tier3} tier3 record(s), but the forbidden input ran: "
            f"{forbidden!r}")
    assert allowed == "ran:7", f"{label}: allowed run gave {allowed!r}"
    if _record_gap(label):
        return
    # Outside #1608's positions, the converse: every guard is on the record
    # (a guard the solver also PROVED is over-checking, never unsound), and
    # every stored leaf is.  `tier3_unguarded` is an honest disclosure — a
    # position whose guard the backend does not emit, such as a widening
    # into a `Map` value (E531) — so it counts as recorded.
    assert guards <= tier3 + verified, (
        f"{label}: {guards} guard(s) in the WAT against {tier3} tier3 + "
        f"{verified} verified {leaf.obligation} record(s)")
    assert tier3 + verified + unguarded >= leaves, (label, statuses, leaves)


@pytest.mark.parametrize(
    "label,source",
    [(c[0], c[2]) for c in _GAP_CELLS if c[1] == "nat"],
    ids=[c[0] for c in _GAP_CELLS if c[1] == "nat"])
def test_a_map_value_outside_a_let_is_guarded_but_not_yet_recorded(
    label: str, source: str,
) -> None:
    """#1608's shape, pinned: every `@Nat` leaf GUARDED, none recorded.

    When #1608 lands the record half, this cell goes red and the converse
    assertions above stop exempting the label.
    """
    leaf = _LEAVES["nat"]
    statuses, guards, forbidden, allowed = _measure(source, leaf)
    assert statuses == [], (label, statuses)
    assert guards == source.count(leaf.value), (label, guards)
    assert leaf.trap in forbidden, f"{label}: forbidden run gave {forbidden!r}"
    assert allowed == "ran:7", f"{label}: allowed run gave {allowed!r}"
