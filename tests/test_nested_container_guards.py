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
recorded `tier3` and stored a negative `@Nat` silently.

Every cell here is a DIFFERENTIAL between the two components, over a matrix
GENERATED from the positions the descent walks rather than listed by hand:

* the record and the artifact agree — the number of `nat_bind` obligations
  recorded `tier3` equals the number of `@Nat` sign guards in the function's
  WAT, and every leaf the program stores is on the record;
* the artifact does what the record says — a negative input traps with the
  `@Nat` guard's own message, and a non-negative control runs to its value,
  so a guard cannot pass by over-firing.

Each `@Nat` leaf is `float_to_int(@Float64.0)`: opaque to the solver, so its
narrowing is `tier3` whatever the shape, and the input decides its sign.
The container is built and never read back, so only a guard AT THE STORE can
trap — a read-side pattern guard cannot stand in for a missing store guard.
"""

from __future__ import annotations

import re
from collections.abc import Iterator

import pytest

from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import execute
from vera.parser import parse_to_ast
from vera.verifier import verify

from tests.codegen_helpers import wat_fn_body


#: The `@Nat` sign guard: `nat_guard` is trap kind 2 in
#: `vera.trap_registry.TRAP_KINDS`, reported through `$vera.trap`.
_NAT_GUARD = re.compile(
    r"i32\.const 2\s+i32\.const -?\d+\s+i32\.const -?\d+\s+call \$vera\.trap")
_NAT_TRAP = "Negative value bound into a @Nat slot"

#: An opaque `@Nat` narrowing source (Tier 3 in every shape).
_LEAF = "float_to_int(@Float64.0)"

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
        # guard `0 - 3` as a `@Nat` and trap the non-negative control.
        return (f"{{ let @Tuple<Int, Int> = Tuple(0 - 3, 1); "
                f"let @Int = 9; {expr} }}")
    raise ValueError(wrapper)


def _chain(kinds: list[str], nat_level: int, nest_index: int,
           wrapper: str) -> tuple[str, str]:
    """(type, expression) of a container chain, ``kinds[0]`` outermost.

    A `Tuple` level holds the next level beside one scalar leaf (the nested
    component first or second, by *nest_index*); that leaf is the `@Nat` at
    *nat_level* and an `@Int` literal elsewhere.  An `Array` or `Map` level
    holds the next level as its one element / value, and at the innermost
    level holds the `@Nat` leaf itself.
    """
    ty: str | None = None
    ex: str | None = None
    depth = len(kinds)
    for level in range(depth, 0, -1):
        kind = kinds[level - 1]
        if kind == "Array":
            if ty is None:
                ty, ex = "Array<Nat>", f"[{_LEAF}]"
            else:
                ty, ex = f"Array<{ty}>", f"[{_wrap(wrapper, ex)}]"
            continue
        if kind == "Map":
            if ty is None:
                ty, ex = "Map<String, Nat>", f'map_insert(map_new(), "k", {_LEAF})'
            else:
                ty = f"Map<String, {ty}>"
                ex = f'map_insert(map_new(), "k", {_wrap(wrapper, ex)})'
            continue
        leaf = (("Nat", _LEAF) if level == nat_level
                else ("Int", str(level + 10)))
        if ty is None:
            comps = [leaf, ("Int", "2")]
        else:
            inner = (ty, _wrap(wrapper, ex))
            comps = [inner, leaf] if nest_index == 0 else [leaf, inner]
        ty = f"Tuple<{comps[0][0]}, {comps[1][0]}>"
        ex = f"Tuple({comps[0][1]}, {comps[1][1]})"
    assert ty is not None and ex is not None
    return ty, ex


def _program(context: str, ty: str, ex: str) -> str:
    """Place the chain at a position with a RECORDED target."""
    pre = ""
    if context == "let":
        body = f"let @{ty} = {ex};\n  7"
    elif context == "call arg":
        pre = f"private fn h(@{ty} -> @Int)\n{_HDR}{{\n  7\n}}\n\n"
        body = f"h({ex})"
    elif context == "Some field":
        body = f"let @Option<{ty}> = Some({ex});\n  7"
    elif context == "user ctor field":
        pre = f"private data W {{\n  MkW({ty})\n}}\n\n"
        body = f"let @W = MkW({ex});\n  7"
    else:
        raise ValueError(context)
    return f"{pre}public fn g(@Float64 -> @Int)\n{_HDR}{{\n  {body}\n}}\n"


#: The chains, by level kind, outermost first.  Alternation puts each
#: container kind both inside and outside each other one.
_SHAPES = {
    "tuple": lambda d: ["Tuple"] * d,
    "tuple/array": lambda d: ["Tuple", "Array"] * d,
    "array/tuple": lambda d: ["Array", "Tuple"] * d,
    "tuple/map": lambda d: ["Tuple", "Map"] * d,
    "map/tuple": lambda d: ["Map", "Tuple"] * d,
}
_CONTEXTS = ("let", "call arg", "Some field", "user ctor field")
_MAX_DEPTH = 5


def _cells() -> Iterator[tuple[str, str]]:
    for context in _CONTEXTS:
        for shape, make in _SHAPES.items():
            for depth in range(1, _MAX_DEPTH + 1):
                kinds = make(depth)[:depth]
                levels = sorted({1, (depth + 1) // 2, depth})
                for nat_level in levels:
                    # A `@Nat` sibling needs a Tuple level; an Array or Map
                    # level holds one only as the innermost leaf.
                    if kinds[nat_level - 1] != "Tuple" and nat_level != depth:
                        continue
                    for nest_index in ((0, 1) if depth > 1 else (0,)):
                        wrappers = (("direct", "if", "match", "block")
                                    if 1 < depth <= 3 else ("direct",))
                        for wrapper in wrappers:
                            ty, ex = _chain(kinds, nat_level, nest_index,
                                            wrapper)
                            label = (f"{context}|{shape}|d{depth}|"
                                     f"nat@{nat_level}|n{nest_index}|{wrapper}")
                            yield label, _program(context, ty, ex)


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
    return shape.startswith("map/") and context != "let"


_CELLS = [c for c in _ALL_CELLS if not _record_gap(c[0])]
_GAP_CELLS = [c for c in _ALL_CELLS if _record_gap(c[0])]


def _measure(source: str) -> tuple[list[str], int, str, str]:
    """(nat_bind statuses in `g`, nat guards in `g`'s WAT, run(-5), run(5))."""
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    errors = [d.description[:90] for d in diags if d.severity == "error"]
    assert not errors, errors
    result = verify(program, source,
                    expr_types=arts.expr_semantic_types,
                    expr_target_types=arts.expr_target_types)
    statuses = sorted(o.status for o in result.obligations
                      if o.kind == "nat_bind" and o.fn_name == "g")
    compiled = codegen_compile(
        program, source=source, file="p.vera",
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    errors = [d.description[:90] for d in compiled.diagnostics
              if d.severity == "error"]
    assert not errors, errors
    guards = len(_NAT_GUARD.findall(wat_fn_body(compiled.wat, "g")))

    def run(arg: float) -> str:
        try:
            return f"ran:{execute(compiled, fn_name='g', args=[arg]).value}"
        except Exception as exc:  # noqa: BLE001 — the trap IS the observation
            return str(exc)

    return statuses, guards, run(-5.0), run(5.0)


def test_the_matrix_covers_every_position_and_depth() -> None:
    """The generator reaches what it claims to, so a green run means it."""
    labels = [label for label, _ in _ALL_CELLS]
    assert len(labels) == len(set(labels))
    for context in _CONTEXTS:
        for shape in _SHAPES:
            for depth in range(1, _MAX_DEPTH + 1):
                assert any(label.startswith(f"{context}|{shape}|d{depth}|")
                           for label in labels), (context, shape, depth)
    for wrapper in ("if", "match", "block"):
        assert any(label.endswith(f"|{wrapper}") for label in labels)


@pytest.mark.parametrize("label,source", _CELLS, ids=[c[0] for c in _CELLS])
def test_every_recorded_guard_is_emitted_and_every_emitted_guard_recorded(
    label: str, source: str,
) -> None:
    statuses, guards, negative, positive = _measure(source)
    leaves = source.count(_LEAF)
    # Every leaf the program stores is on the record, at Tier 3 — the leaf
    # is opaque, so nothing else is a correct status for it.
    assert statuses == ["tier3"] * leaves, (label, statuses, leaves)
    # Both directions: a `tier3` with no guard is a false claim, and a guard
    # with no record is a check the report does not count.
    assert guards == statuses.count("tier3"), (
        f"{label}: {statuses.count('tier3')} nat_bind recorded tier3, but "
        f"{guards} @Nat guard(s) in the WAT"
    )
    assert _NAT_TRAP in negative, f"{label}: run(-5.0) gave {negative!r}"
    assert positive == "ran:7", f"{label}: run(5.0) gave {positive!r}"


@pytest.mark.parametrize("label,source", _GAP_CELLS,
                         ids=[c[0] for c in _GAP_CELLS])
def test_a_map_value_outside_a_let_is_guarded_but_not_yet_recorded(
    label: str, source: str,
) -> None:
    """#1608's shape, pinned: every leaf GUARDED, none on the record.

    When #1608 lands the record half, this cell goes red and the label
    moves into the full differential above.
    """
    statuses, guards, negative, positive = _measure(source)
    assert statuses == [], (label, statuses)
    assert guards == source.count(_LEAF), (label, guards)
    assert _NAT_TRAP in negative, f"{label}: run(-5.0) gave {negative!r}"
    assert positive == "ran:7", f"{label}: run(5.0) gave {positive!r}"
