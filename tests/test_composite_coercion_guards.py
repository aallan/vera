"""A composite value's `Int` component coerced to a `Nat` component traps.

The checker admits a value whose type has an `Int` component at a position
whose type has a `Nat` there (`Option<Int>` at an `Option<Nat>` formal, an
array literal of `Wrap<Int>` under an `Array<Wrap<Nat>>` binding, a pattern
binder declared `Tuple<Int, Nat>` over a `Tuple<Int, Int>` field, ...), and
records the target type on the coerced node alone.  Nothing obligates the
component, so code generation is the one thing between a negative `Int` and
a `@Nat` slot: #1542's shape, #1695's line.  One rule decides every such
site off the typed program (`vera/narrowing.py`'s differing tree, applied by
`vera/wasm/coercion.py`):

* a construction hands each child its component of the target, and a scalar
  child the checker did not type at `Nat` itself is guarded where it is
  stored, with the guard a scalar narrowing has;
* an opaque value (a slot, a call's result, an index, a `match` or `if`
  result) is walked at run time along every path where the target holds a
  `Nat` its type does not: `Some`, the differing side of a `Result`, a
  tuple's or a record's component, every constructor's field on the path,
  every element of an `Array`, every key, value and element of a `Map` or
  `Set`, a `Future`'s payload;
* a pattern binder declared narrower than the field it binds walks the
  bound value at the binder.

The matrix is GENERATED from the positions the checker records a target at
(the site axis), the shapes a component can sit in (the shape axis), how the
coerced value is built (in place, or opaque behind a slot) and three inputs.
The leaf is `float_to_int(@Float64.0)`, opaque to the solver, and every read
back binds the component at `@Int`, a widening no guard reads, so only a
check at the coercion can stop the negative:

* -5 traps with the narrowing guard's own message;
* 5 runs to 5, so a guard cannot pass by over-firing;
* 0 builds the shape's empty value (`None`, `Err`, `[]`, an empty map or
  set) where it has one, which holds no component and runs to 7.

The record agrees with the artifact: `vera verify` reports each new guard as
one W004 naming `component_coercion` (the verifier records nothing at these
sites until #1695's obligation table does), and the compiled module holds
one such check per site.  A leaf the checker types at `Nat` itself keeps
the guard it has and gains none (the negative space).
"""

from __future__ import annotations

import functools
from collections.abc import Iterator
from dataclasses import dataclass, fields

import pytest

from tests import pipeline
from vera import ast
from vera.types import pretty_type

# A generated class instrument (tests/matrix_sample.py): a pull request runs a
# sample of its parametrised cells, and all of them when it changes this file
# or a module that decides its class, here code generation's guard of a
# composite coercion and the differing tree it is decided by.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/narrowing.py",
        "vera/wasm/coercion.py",
        "vera/wasm/data.py",
        "vera/wasm/calls_containers.py",
        "vera/wasm/calls_handlers.py",
        "vera/wasm/calls.py",
        "vera/wasm/closures.py",
        "vera/codegen/contracts.py",
    ],
)

_NAT_TRAP = "Negative value bound into a @Nat slot"
_BOUNDARY_TRAP = "Refinement violation"
_EMITTER_FILE = "wasm/coercion.py:"


# =====================================================================
# The generator
# =====================================================================


@dataclass(frozen=True)
class Shape:
    """A composite type with one component, and how a cell uses it."""

    name: str
    ty: str             #: over ``{C}``, the component type
    build: str          #: over ``{x}``, a construction holding the component
    empty: str | None   #: a value holding no component, or ``None``
    read: str           #: over ``{v}``, the component read back at `@Int`
    zero: str           #: a value of the coerced type with no bad component
    effect: str = "pure"  #: the effect row every function of the cell has


SHAPES: dict[str, Shape] = {s.name: s for s in (
    Shape("Option", "Option<{C}>", "Some({x})", "None",
          "option_unwrap_or({v}, 7)", "None"),
    Shape("Result.Ok", "Result<{C}, String>", "Ok({x})", 'Err("e")',
          "result_unwrap_or({v}, 7)", 'Err("e")'),
    Shape("Result.Err", "Result<String, {C}>", "Err({x})", 'Ok("o")',
          "match {v} {{ Ok(@String) -> 7, Err(@Int) -> @Int.0 }}",
          'Ok("o")'),
    Shape("Tuple", "Tuple<Int, {C}>", "Tuple(1, {x})", None,
          "match {v} {{ Tuple(@Int, @Int) -> @Int.0 }}", "Tuple(1, 7)"),
    Shape("Box", "Box<{C}>", "MkBox(1, {x})", None,
          "match {v} {{ MkBox(@Int, @Int) -> @Int.0 }}", "MkBox(1, 7)"),
    Shape("Duo", "Duo<{C}>", "Second(1, {x})", "Neither",
          "match {v} {{ First(@Int) -> @Int.0, Second(@Int, @Int) -> "
          "@Int.0, Neither -> 7 }}", "Neither"),
    Shape("P", "P<{C}, Bool>", "MkP(true, {x})", None,
          "match {v} {{ MkP(@Bool, @Int) -> @Int.0 }}", "MkP(true, 7)"),
    Shape("Array", "Array<{C}>", "[{x}]", "[]",
          "if array_length({v}) > 0 then {{ {v}[0] }} else {{ 7 }}", "[]"),
    Shape("Array<Option>", "Array<Option<{C}>>", "[Some({x})]", "[None]",
          "if array_length({v}) > 0 then {{ option_unwrap_or({v}[0], 7) }} "
          "else {{ 7 }}", "[None]"),
    Shape("Option<Array>", "Option<Array<{C}>>", "Some([{x}])", "None",
          "match {v} {{ Some(@Array<Int>) -> if array_length("
          "@Array<Int>.0) > 0 then {{ @Array<Int>.0[0] }} else {{ 7 }}, "
          "None -> 7 }}", "None"),
    Shape("Map.value", "Map<String, {C}>", 'map_insert(map_new(), "k", {x})',
          "map_new()",
          'match map_get({v}, "k") {{ Some(@Int) -> @Int.0, None -> 7 }}',
          "map_new()"),
    Shape("Map.key", "Map<{C}, Int>", "map_insert(map_new(), {x}, 1)",
          "map_new()",
          "if map_size({v}) > 0 then {{ map_keys({v})[0] }} else {{ 7 }}",
          "map_new()"),
    Shape("Set", "Set<{C}>", "set_add(set_new(), {x})", "set_new()",
          "if set_size({v}) > 0 then {{ set_to_array({v})[0] }} else {{ 7 }}",
          "set_new()"),
    # A `Future` is its payload at run time (`async` evaluates eagerly), so
    # its walk is the payload's.
    Shape("Future", "Future<{C}>", "async({x})", None, "await({v})",
          "async(7)", effect="<Async>"),
)}

_DECLS = (
    "private data Wrap<A> {\n  W(A)\n}\n\n"
    "private data Box<T> {\n  MkBox(Int, T)\n}\n\n"
    "private data Duo<A> {\n  First(A),\n  Second(Int, A),\n  Neither\n}\n\n"
    "private data P<A, B> {\n  MkP(B, A)\n}\n\n"
)
_LEAF = "float_to_int(@Float64.0)"


def _hdr(effect: str) -> str:
    return f"  requires(true)\n  ensures(true)\n  effects({effect})\n"


def _choose(shape: Shape) -> str:
    """The shape's value from the parameter: the empty one at 0.0, if any."""
    built = shape.build.format(x=_LEAF)
    if shape.empty is None:
        return built
    return (f"if @Float64.0 == 0.0 then {{ {shape.empty} }} "
            f"else {{ {built} }}")


def program(site: str, shape: Shape, form: str) -> str:
    """The program of one cell: `f(@Float64 -> @Int)` coerces the shape's
    `Int`-component value into its `Nat`-component type at *site* and
    returns the component read back at `@Int`."""
    nat = shape.ty.format(C="Nat")
    wide = shape.ty.format(C="Int")
    eff = shape.effect
    hdr = _hdr(eff)
    pre = _DECLS
    if form == "opaque":
        lets = f"let @{wide} = {_choose(shape)};\n  "
        v = f"@{wide}.0"
    else:
        lets = ""
        v = _choose(shape)
    read = shape.read.format(v=f"@{nat}.0")
    helpers = ""
    if site == "let":
        body = f"{lets}let @{nat} = {v};\n  {read}"
    elif site == "return":
        helpers = f"private fn g(@Float64 -> @{nat})\n{hdr}{{\n  {lets}{v}\n}}\n\n"
        body = f"let @{nat} = g(@Float64.0);\n  {read}"
    elif site == "closure return":
        pre = f"type Mk = fn(Float64 -> {nat}) effects({eff});\n\n" + pre
        body = (f"let @Mk = fn(@Float64 -> @{nat}) effects({eff}) {{ {lets}{v} }};\n"
                f"  let @{nat} = apply_fn(@Mk.0, @Float64.0);\n  {read}")
    elif site == "call argument":
        helpers = f"private fn g(@{nat} -> @Int)\n{hdr}{{\n  {read}\n}}\n\n"
        body = f"{lets}g({v})"
    elif site == "generic call argument":
        helpers = f"private forall<T> fn keep(@T -> @T)\n{hdr}{{\n  @T.0\n}}\n\n"
        body = f"{lets}let @{nat} = keep({v});\n  {read}"
    elif site == "apply_fn argument":
        pre = f"type Rd = fn({nat} -> Int) effects({eff});\n\n" + pre
        body = (f"{lets}let @Rd = fn(@{nat} -> @Int) effects({eff}) {{ "
                f"{read} }};\n  apply_fn(@Rd.0, {v})")
    elif site == "put argument":
        body = (f"{lets}handle[State<{nat}>](@{nat} = {shape.zero}) {{\n"
                f"    get(@Unit) -> {{ resume(@{nat}.0) }},\n"
                f"    put(@{nat}) -> {{ resume(()) }}\n"
                f"  }} in {{\n    put({v});\n"
                f"    let @{nat} = get(());\n    {read}\n  }}")
    elif site == "throw argument":
        body = (f"{lets}handle[Exn<{nat}>] {{\n"
                f"    throw(@{nat}) -> {read}\n"
                f"  }} in {{\n    throw({v})\n  }}")
    elif site == "declared field":
        pre = pre + f"private data Holder {{\n  MkH({nat})\n}}\n\n"
        body = (f"{lets}match MkH({v}) {{\n"
                f"    MkH(@{nat}) -> {read}\n  }}")
    elif site == "generic field":
        body = (f"{lets}let @Option<{nat}> = Some({v});\n"
                f"  match @Option<{nat}>.0 {{\n"
                f"    Some(@{nat}) -> {read},\n    None -> 7\n  }}")
    elif site == "array element":
        body = (f"{lets}let @Array<{nat}> = [{v}];\n"
                f"  let @{nat} = @Array<{nat}>.0[0];\n  {read}")
    elif site == "tuple component":
        body = (f"{lets}let @Tuple<{nat}, Int> = Tuple({v}, 1);\n"
                f"  match @Tuple<{nat}, Int>.0 {{\n"
                f"    Tuple(@{nat}, @Int) -> {read}\n  }}")
    elif site == "state init":
        body = (f"{lets}handle[State<{nat}>](@{nat} = {v}) {{\n"
                f"    get(@Unit) -> {{ resume(@{nat}.0) }},\n"
                f"    put(@{nat}) -> {{ resume(()) }}\n"
                f"  }} in {{\n    let @{nat} = get(());\n    {read}\n  }}")
    elif site == "binder, depth 1":
        body = f"{lets}match W({v}) {{\n    W(@{nat}) -> {read}\n  }}"
    elif site == "binder, depth 2":
        body = f"{lets}match W(W({v})) {{\n    W(W(@{nat})) -> {read}\n  }}"
    elif site == "binder, opaque scrutinee":
        body = (f"{lets}let @Wrap<{wide}> = W({v});\n"
                f"  match @Wrap<{wide}>.0 {{\n    W(@{nat}) -> {read}\n  }}")
    elif site == "binder, top level":
        body = f"{lets}match {v} {{\n    @{nat} -> {read}\n  }}"
    elif site == "destructure binder":
        body = f"{lets}let Wrap<@{nat}> = W({v});\n  {read}"
    elif site == "clause binder":
        body = (f"{lets}handle[Exn<{wide}>] {{\n"
                f"    throw(@{nat}) -> {read}\n"
                f"  }} in {{\n    throw({v})\n  }}")
    else:  # pragma: no cover — a site with no template
        raise ValueError(site)
    return f"{pre}{helpers}public fn f(@Float64 -> @Int)\n{hdr}{{\n  {body}\n}}\n"


#: Every position the checker records a target type at, by the node it is
#: recorded on: a declared binding's initialiser, a function's and a
#: closure's result, a formal (a call's, a generic call's, an `apply_fn`
#: closure's, an effect operation's), a constructor's field (a declared and
#: a type-parameter one), a component of a literal (an array element, a
#: tuple component), a handler's state, and the pattern binders: inside a
#: constructor pattern at depth one and two, over a slot scrutinee, at the
#: top level, in a destructuring `let`, and at a handler clause.
SITES = (
    "let", "return", "closure return", "call argument",
    "generic call argument", "apply_fn argument", "put argument",
    "throw argument", "declared field", "generic field", "array element",
    "tuple component", "state init", "binder, depth 1", "binder, depth 2",
    "binder, opaque scrutinee", "binder, top level", "destructure binder",
    "clause binder",
)
FORMS = ("opaque", "built")
ARGS = (-5.0, 5.0, 0.0)

#: Programs the checker refuses, which are no cells: a `State` over an
#: `Array` (E340).
_NOT_CELLS: dict[tuple[str, str], str] = {
    (site, shape): "E340"
    for site in ("put argument", "state init")
    for shape in ("Array", "Array<Option>")
}

#: The one exclusion by site kind and shape (ruling 2): a handler clause
#: binder over a payload whose head is a container already has a record,
#: `refine_bind` disclosed `tier3_unguarded` (E506), and gains no guard
#: beside it; #1695's obligation table gives the position its row.
_EXCLUDED = frozenset(
    ("clause binder", shape)
    for shape in ("Array", "Array<Option>", "Map.value", "Map.key", "Set")
)
_EXCLUDED_REASON = (
    "W67 (#1695): a handler clause binder over an Array, Map or Set payload "
    "is recorded refine_bind tier3_unguarded (E506) and is not guarded")


def _programs() -> Iterator[tuple[str, str, str]]:
    for site in SITES:
        for shape in SHAPES:
            if (site, shape) in _NOT_CELLS:
                continue
            for form in FORMS:
                yield site, shape, form


#: The positions a function boundary already guards (#746): a formal or a
#: declared result whose type is a tuple with a `Nat` component, which the
#: callee's entry or epilogue checks for every caller.  An opaque value
#: coerced there defers to that guard rather than doubling it, so it traps
#: with the boundary's message and gains no check and no W004 (the negative
#: space of the deference).
_BOUNDARY = frozenset(
    (site, "Tuple")
    for site in ("call argument", "apply_fn argument", "return",
                 "closure return")
)

_PROGRAMS = list(_programs())
_PROGRAM_IDS = [f"{s} / {sh} / {f}" for s, sh, f in _PROGRAMS]
_RECORDED = [p for p in _PROGRAMS if (p[0], p[1]) not in _EXCLUDED
             and not ((p[0], p[1]) in _BOUNDARY and p[2] == "opaque")]
_RECORDED_IDS = [f"{s} / {sh} / {f}" for s, sh, f in _RECORDED]


def _run_cells() -> Iterator[object]:
    for site, shape, form in _PROGRAMS:
        for arg in ARGS:
            cell_id = f"{site} / {shape} / {form} / {arg}"
            if (site, shape) in _EXCLUDED and arg == -5.0:
                yield pytest.param(site, shape, form, arg, id=cell_id,
                                   marks=pytest.mark.xfail(
                                       strict=True, reason=_EXCLUDED_REASON))
            else:
                yield pytest.param(site, shape, form, arg, id=cell_id)


# =====================================================================
# Observation
# =====================================================================


@functools.lru_cache(maxsize=None)
def _compiled(src: str) -> pipeline.Compiled:
    compiled = pipeline.compile(src, file="cell.vera")
    errors = [d for d in compiled.result.diagnostics if d.severity == "error"]
    assert not errors, [(d.error_code, d.description[:120]) for d in errors]
    return compiled


@functools.lru_cache(maxsize=None)
def _verified(src: str) -> pipeline.Verified:
    return pipeline.verify(src, file="cell.vera", reconcile=True)


def _nodes(node: object) -> Iterator[ast.Node]:
    stack = [node]
    while stack:
        item = stack.pop()
        if isinstance(item, ast.Node):
            yield item
            for f in fields(item):
                if f.name == "span" or f.metadata.get("identity"):
                    continue
                stack.append(getattr(item, f.name))
        elif isinstance(item, tuple):
            stack.extend(item)


def _leaf_in_place(src: str) -> bool:
    """Whether the checker typed the program's leaf at `Nat` itself, as an
    in-place construction (`Some(x)` at an `Option<Nat>` target) has it:
    then the leaf keeps its own guard and the rule adds none."""
    checked = pipeline.check(src, file="cell.vera")
    typed = checked.typed
    targets = [
        typed.target_type(node)
        for tld in typed.linked.program.declarations
        for node in _nodes(tld.decl)
        if isinstance(node, ast.FnCall) and node.name == "float_to_int"
    ]
    assert targets, "the cell holds no leaf"
    in_place = {t is not None and pretty_type(t) == "Nat" for t in targets}
    assert len(in_place) == 1, f"leaves typed both ways: {targets}"
    return in_place.pop()


def _coercion_w004(verified: pipeline.Verified) -> list[str]:
    return [w.description for w in verified.warnings
            if w.error_code == "W004"
            and "'component_coercion'" in w.description]


def _coercion_checks(compiled: pipeline.Compiled) -> list[object]:
    return [c for c in compiled.result.emitted_checks
            if c.emitter.startswith(_EMITTER_FILE)]


def _ran(src: str, fn: str, arg: float | int) -> pipeline.Ran:
    return pipeline.run(_compiled(src).result, fn, [arg],
                        capture_stderr=False)


def _assert_traps(ran: pipeline.Ran, message: str = _NAT_TRAP) -> None:
    assert ran.trap is not None, (
        f"the negative component flowed into a `@Nat` slot: "
        f"returned {ran.execution.value}")
    assert message in str(ran.trap), str(ran.trap)[:300]


def _assert_returns(ran: pipeline.Ran, value: int) -> None:
    assert ran.trap is None, f"trapped on an allowed value: {str(ran.trap)[:300]}"
    assert ran.execution.value == value


# =====================================================================
# The matrix
# =====================================================================


def test_the_matrix_spans_every_site_and_shape() -> None:
    """The axes are the ones the class spans, and every refused program is
    refused for the reason `_NOT_CELLS` names, so no cell hides there."""
    assert len(SITES) == 19 and len(SHAPES) == 14
    assert len(_PROGRAMS) == len(SITES) * len(SHAPES) * 2 - 2 * len(_NOT_CELLS)
    for (site, shape), code in _NOT_CELLS.items():
        for form in FORMS:
            checked = pipeline.check(
                program(site, SHAPES[shape], form), file="cell.vera")
            assert code in {d.error_code for d in checked.errors}, (
                site, shape, form)


class TestTheRun:
    """What the compiled program does with each input."""

    @pytest.mark.parametrize(("site", "shape", "form", "arg"), _run_cells())
    def test_the_value(self, site: str, shape: str, form: str,
                       arg: float) -> None:
        src = program(site, SHAPES[shape], form)
        ran = _ran(src, "f", arg)
        if arg < 0:
            _assert_traps(ran, _BOUNDARY_TRAP
                          if (site, shape) in _BOUNDARY and form == "opaque"
                          else _NAT_TRAP)
        elif arg > 0:
            _assert_returns(ran, 5)
        else:
            _assert_returns(ran, 7 if SHAPES[shape].empty is not None else 0)


class TestTheRecord:
    """`vera verify` and the compiled module agree on every new guard."""

    @pytest.mark.parametrize(("site", "shape", "form"), _RECORDED,
                             ids=_RECORDED_IDS)
    def test_one_guard_per_coercion(self, site: str, shape: str,
                                    form: str) -> None:
        """Each cell coerces once, so its module holds exactly one narrowing
        guard: never none (a lost guard), never two (a double one).  An
        opaque value's is the coercion's walk; a construction's is the
        store guard code generation already placed, where it placed one.
        `vera verify` passes with no warning but W004, one W004 naming
        `component_coercion` per such check."""
        src = program(site, SHAPES[shape], form)
        verified = _verified(src)
        assert verified.ok, [(d.error_code, d.description[:120])
                             for d in verified.errors]
        codes = {w.error_code for w in verified.warnings}
        assert codes <= {"W004"}, sorted(codes)
        compiled = _compiled(src)
        guards = pipeline.checks(compiled.result, kind="nat_guard")
        assert len(guards) == 1, guards
        coercion = _coercion_checks(compiled)
        if form == "opaque":
            assert len(coercion) == 1, guards
        assert len(_coercion_w004(verified)) == len(coercion)

    @pytest.mark.parametrize(("site", "shape", "form"), _RECORDED,
                             ids=_RECORDED_IDS)
    def test_an_in_place_leaf_keeps_its_own_guard(
        self, site: str, shape: str, form: str,
    ) -> None:
        """The negative space: where the checker typed the leaf at `Nat`, the
        module holds the one narrowing guard it held before and no
        coercion check, and `vera verify` reports no new W004."""
        src = program(site, SHAPES[shape], form)
        if not _leaf_in_place(src):
            return
        compiled = _compiled(src)
        nat_guards = pipeline.checks(compiled.result, kind="nat_guard")
        assert len(nat_guards) == 1, nat_guards
        assert _coercion_checks(compiled) == []
        assert _coercion_w004(_verified(src)) == []

    @pytest.mark.parametrize("site", sorted(s for s, _sh in _BOUNDARY))
    def test_a_boundary_guard_is_deferred_to(self, site: str) -> None:
        """An opaque `Tuple<Int, Int>` at a `Tuple<Int, Nat>` formal or
        result keeps the one guard it had at base, the callee's (#746): one
        refinement check, its one W004, and no coercion check beside it."""
        src = program(site, SHAPES["Tuple"], "opaque")
        verified = _verified(src)
        assert verified.ok
        compiled = _compiled(src)
        assert _coercion_checks(compiled) == []
        assert pipeline.checks(compiled.result, kind="nat_guard") == ()
        boundary = pipeline.checks(
            compiled.result,
            emitter="codegen/contracts.py:_emit_refinement_check")
        assert len(boundary) == 1, boundary
        w004 = [w.description for w in verified.warnings]
        assert len(w004) == 1 and "'refine_bind'" in w004[0], w004
        assert {w.error_code for w in verified.warnings} == {"W004"}

    @pytest.mark.parametrize(("site", "shape", "form"), sorted(
        (s, sh, f) for s, sh, f in _PROGRAMS if (s, sh) in _EXCLUDED))
    def test_the_excluded_position_is_disclosed(
        self, site: str, shape: str, form: str,
    ) -> None:
        """A clause binder over a container payload keeps its disclosure,
        E506, and no guard stands beside it."""
        src = program(site, SHAPES[shape], form)
        verified = _verified(src)
        assert verified.ok
        assert "E506" in {w.error_code for w in verified.warnings}
        assert _coercion_w004(verified) == []
        assert _coercion_checks(_compiled(src)) == []


# =====================================================================
# The function types (ruling 1): admitted, and no walk can check them
# =====================================================================

_FN_RETURN = """\
type IntToNat = fn(Int -> Nat) effects(pure);
type IntToInt = fn(Int -> Int) effects(pure);

private fn apply_nat(@IntToNat, @Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@IntToNat.0, @Int.0)
}

public fn f(@Int -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 };
  apply_nat(@IntToInt.0, @Int.0)
}
"""

_FN_PARAM = """\
type NatToInt = fn(Nat -> Int) effects(pure);
type IntToInt = fn(Int -> Int) effects(pure);

private fn apply_int(@IntToInt, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@IntToInt.0, @Int.0)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @NatToInt = fn(@Nat -> @Int) effects(pure) { nat_to_int(@Nat.0) };
  apply_int(@NatToInt.0, @Int.0)
}
"""

_FN_REASON = (
    "W67 (#1695): a function type gaining a Nat component is admitted "
    "(is_subtype rule 9 with 3b) and no runtime walk can check it where the "
    "function is passed; #1695's row or a checker refusal closes it")


@pytest.mark.xfail(strict=True, reason=_FN_REASON)
def test_repro_a_closure_returning_int_at_a_nat_result_is_refused() -> None:
    _assert_traps(_ran(_FN_RETURN, "f", -5))


@pytest.mark.xfail(strict=True, reason=_FN_REASON)
def test_repro_a_closure_taking_nat_at_an_int_formal_is_refused() -> None:
    _assert_traps(_ran(_FN_PARAM, "f", -5))


# =====================================================================
# The reported instances (#1542's seven positions), verbatim
# =====================================================================

_WRAP = "private data Wrap<A> {\n  W(A)\n}\n\n"
_F = "public fn f(@Int -> @Nat)\n  requires(true)\n  ensures(true)\n  effects(pure)\n"

_P1 = _WRAP + _F + """\
{
  let @Array<Wrap<Nat>> = [W(@Int.0)];
  match @Array<Wrap<Nat>>.0[0] {
    W(@Nat) -> @Nat.0
  }
}
"""

_P2 = _WRAP + _F + """\
{
  let @Array<Wrap<Nat>> = [W(@Int.0)];
  let @Wrap<Nat> = @Array<Wrap<Nat>>.0[0];
  match @Wrap<Nat>.0 {
    W(@Nat) -> @Nat.0
  }
}
"""

_P3 = _WRAP + """\
private fn first(@Array<Wrap<Nat>> -> @Wrap<Nat>)
  requires(array_length(@Array<Wrap<Nat>>.0) > 0)
  ensures(true)
  effects(pure)
{
  @Array<Wrap<Nat>>.0[0]
}

""" + _F + """\
{
  let @Array<Wrap<Nat>> = [W(@Int.0)];
  match first(@Array<Wrap<Nat>>.0) {
    W(@Nat) -> @Nat.0
  }
}
"""

_P4 = _WRAP + _F + """\
{
  let @Tuple<Int, Int> = Tuple(1, @Int.0);
  match W(@Tuple<Int, Int>.0) {
    W(@Tuple<Int, Nat>) -> match @Tuple<Int, Nat>.0 {
      Tuple(@Int, @Nat) -> @Nat.0
    }
  }
}
"""

_P5 = _F + """\
{
  let @Array<Option<Nat>> = [Some(@Int.0)];
  option_unwrap_or(@Array<Option<Nat>>.0[0], 7)
}
"""

_P6 = _F + """\
{
  let @Option<Int> = Some(@Int.0);
  let @Option<Nat> = @Option<Int>.0;
  match @Option<Nat>.0 {
    Some(@Nat) -> @Nat.0,
    None -> 0
  }
}
"""

_P7 = """\
private fn peekn(@Option<Nat> -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(@Option<Nat>.0, 0)
}

""" + _F + """\
{
  let @Option<Int> = Some(@Int.0);
  peekn(@Option<Int>.0)
}
"""


def _assert_one_guard(src: str) -> None:
    """`vera verify` passes with one W004 naming the coercion and no other
    warning; -5 traps as a narrowing does; 5 runs to 5."""
    verified = _verified(src)
    assert verified.ok, [(d.error_code, d.description[:120])
                         for d in verified.errors]
    assert {w.error_code for w in verified.warnings} <= {"W004"}
    assert len(_coercion_w004(verified)) == 1, verified.warnings
    _assert_traps(_ran(src, "f", -5))
    _assert_returns(_ran(src, "f", 5), 5)


def test_repro_p1_index_scrutinee() -> None:
    """A constructor nested in an array literal under an `Array<Wrap<Nat>>`
    binding: the descent reaches the field two levels down (kills the
    descent cut to one level)."""
    _assert_one_guard(_P1)


def test_repro_p2_slot_scrutinee() -> None:
    _assert_one_guard(_P2)


def test_repro_p3_call_scrutinee() -> None:
    _assert_one_guard(_P3)


def test_repro_p4_rebound_composite_pattern() -> None:
    """A binder declared `Tuple<Int, Nat>` over a `Tuple<Int, Int>` field
    walks the bound value (kills the binder rule reverted)."""
    _assert_one_guard(_P4)


def test_repro_p5_option_unwrap_or() -> None:
    _assert_one_guard(_P5)


def test_repro_p6_let_option_coercion() -> None:
    """A slot reference under a composite target: the opaque walk (kills
    the rule applied to constructions alone)."""
    _assert_one_guard(_P6)


def test_repro_p7_call_argument_option() -> None:
    """An `Option<Int>` argument at an `Option<Nat>` formal: the opaque walk
    at the argument (kills the rule applied to constructions alone)."""
    _assert_one_guard(_P7)


# =====================================================================
# The walk's own boundaries: each a mutant's killer
# =====================================================================

_ARRAY_LATE = _F + """\
{
  let @Array<Int> = [1, 2, @Int.0];
  let @Array<Nat> = @Array<Int>.0;
  @Array<Nat>.0[0]
}
"""

_EMPTY_SIDES = """\
private fn pick(@Int -> @Result<Int, String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { Err("e") } else { Ok(@Int.0) }
}

private fn none_or(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  if @Int.0 > 0 then { None } else { Some(@Int.0) }
}

""" + _F + """\
{
  let @Result<Nat, String> = pick(@Int.0);
  let @Option<Nat> = none_or(@Int.0);
  result_unwrap_or(@Result<Nat, String>.0, 3) + option_unwrap_or(@Option<Nat>.0, 4)
}
"""


_MIXED_BOUNDARY = """\
private fn g(@Tuple<Nat, Option<Nat>> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Tuple<Nat, Option<Nat>>.0 {
    Tuple(@Nat, @Option<Nat>) -> nat_to_int(@Nat.0) + nat_to_int(option_unwrap_or(@Option<Nat>.0, 0))
  }
}

public fn f(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Tuple<Int, Option<Int>> = Tuple(@Int.1, Some(@Int.0));
  g(@Tuple<Int, Option<Int>>.0)
}
"""


def test_repro_a_boundary_defers_only_its_own_positions() -> None:
    """`g`'s entry checks the tuple's `Nat` component (#746) and nothing
    inside the `Option`: the call site walks the `Option` alone, so a
    negative first component traps at the boundary, a negative payload at
    the walk, and one W004 names the coercion."""
    _assert_one_guard_count(_MIXED_BOUNDARY, 1)
    compiled = _compiled(_MIXED_BOUNDARY)
    _assert_traps(pipeline.run(compiled.result, "f", [-5, 1],
                               capture_stderr=False), _BOUNDARY_TRAP)
    _assert_traps(pipeline.run(compiled.result, "f", [1, -5],
                               capture_stderr=False))
    _assert_returns(pipeline.run(compiled.result, "f", [2, 3],
                                 capture_stderr=False), 5)


def test_repro_the_walk_reads_every_array_element() -> None:
    """The negative is the third element of an opaque `Array<Int>` coerced
    to `Array<Nat>`: a walk that skips the elements, or reads one, lets it
    through (kills the walk skipping Array elements)."""
    _assert_one_guard_count(_ARRAY_LATE, 1)
    _assert_traps(_ran(_ARRAY_LATE, "f", -5))
    _assert_returns(_ran(_ARRAY_LATE, "f", 5), 1)


def test_repro_the_walk_passes_none_and_err() -> None:
    """`None` and an `Err` hold no `Nat` component: at 5 both coercions see
    their empty side and the run returns 3 + 4 (kills the walk trapping on
    `None` or `Err`); at -5 the `Ok` side traps."""
    _assert_one_guard_count(_EMPTY_SIDES, 2)
    _assert_returns(_ran(_EMPTY_SIDES, "f", 5), 7)
    _assert_traps(_ran(_EMPTY_SIDES, "f", -5))


def _assert_one_guard_count(src: str, count: int) -> None:
    verified = _verified(src)
    assert verified.ok, [(d.error_code, d.description[:120])
                         for d in verified.errors]
    assert {w.error_code for w in verified.warnings} <= {"W004"}
    assert len(_coercion_w004(verified)) == count, verified.warnings


# =====================================================================
# The differing tree (vera/narrowing.py), the rule's pure half
# =====================================================================

_TREE_DECLS = """\
private data List<A> {
  Nil,
  Cons(A, List<A>)
}

private data Spin<A> {
  Stop,
  Go(Spin<A>)
}

public fn f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0
}
"""


def _tree(source: object, target: object) -> object:
    from vera import narrowing

    typed = pipeline.check(_TREE_DECLS, file="tree.vera").typed
    return narrowing.differing_tree(
        source, target, typed.field_types_at, typed.constructors_of)


def _positions(tree: object, path: tuple[object, ...] = ()) -> set[tuple[object, ...]]:
    """Every `Nat` position of *tree* by its path, an `again` by its own."""
    if tree is None:
        return set()
    if tree.kind in ("nat", "again"):
        return {path + (tree.kind,)}
    out: set[tuple[object, ...]] = set()
    for ctor, index, child in tree.parts:
        out |= _positions(child, path + ((ctor.split("$")[-1], index),))
    return out


def test_the_tree_reaches_every_nested_position() -> None:
    """A tuple's components, a nested tuple's, an `Option`'s `Some`, a
    `Map`'s keys and values: each `Int` under a `Nat` is a position, and
    nothing else is."""
    from vera.types import INT, NAT, AdtType

    def tup(*args: object) -> AdtType:
        return AdtType("Tuple", tuple(args))

    source = tup(INT, tup(INT, INT), AdtType("Option", (INT,)),
                 AdtType("Map", (INT, INT)))
    target = tup(NAT, tup(INT, NAT), AdtType("Option", (NAT,)),
                 AdtType("Map", (NAT, INT)))
    assert _positions(_tree(source, target)) == {
        (("Tuple", 0), "nat"),
        (("Tuple", 1), ("Tuple", 1), "nat"),
        (("Tuple", 2), ("Some", 0), "nat"),
        (("Tuple", 3), ("key", 0), "nat"),
    }


def test_a_recursive_type_is_walked_to_its_fixpoint() -> None:
    """`List<Int>` at `List<Nat>`: the head is a position and the tail is
    the same walk again; `Spin<A>` holds its parameter nowhere, so its
    recursion alone is no position and there is no tree."""
    from vera.types import INT, NAT, AdtType

    assert _positions(_tree(AdtType("List", (INT,)),
                            AdtType("List", (NAT,)))) == {
        (("Cons", 0), "nat"), (("Cons", 1), "again")}
    assert _tree(AdtType("Spin", (INT,)), AdtType("Spin", (NAT,))) is None


def test_a_refinement_or_a_function_target_holds_no_position() -> None:
    """A refinement component is the refinement walk's record (#1410), and
    a function's result or parameter is produced by a later call: neither
    is a `Nat` position (rulings 1 and 2)."""
    from vera import ast as vast
    from vera.types import INT, NAT, AdtType, FunctionType, PureEffectRow, RefinedType

    pos = RefinedType(INT, vast.BoolLit(value=True))
    assert _tree(AdtType("Option", (INT,)), AdtType("Option", (pos,))) is None
    fn_int = FunctionType((INT,), INT, PureEffectRow())
    fn_nat = FunctionType((INT,), NAT, PureEffectRow())
    assert _tree(AdtType("Option", (fn_int,)),
                 AdtType("Option", (fn_nat,))) is None


def test_a_boundary_guard_s_positions_leave_the_tree() -> None:
    """`without_paths` drops the tuple positions a function boundary's
    component guard checks (#746) and keeps every other: the `Some` under
    the third component is no tuple path, so it stays."""
    from vera import narrowing
    from vera.types import INT, NAT, AdtType

    def tup(*args: object) -> AdtType:
        return AdtType("Tuple", tuple(args))

    tree = _tree(tup(INT, tup(INT, INT), AdtType("Option", (INT,))),
                 tup(NAT, tup(INT, NAT), AdtType("Option", (NAT,))))
    pruned = narrowing.without_paths(tree, frozenset({(0,), (1, 1)}))
    assert _positions(pruned) == {(("Tuple", 2), ("Some", 0), "nat")}
    assert narrowing.without_paths(
        _tree(tup(INT, INT), tup(INT, NAT)), frozenset({(1,)})) is None
