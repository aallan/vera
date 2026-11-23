"""An operand with no WebAssembly value, at every lowering (#1870).

`Unit` is zero-size: a value of it, of a `Future` of it or of a refinement of
it compiles to no WebAssembly value (spec §2.2.2).  The class is every
lowering that takes such an operand: each either has a rule for it or the
checker refuses the program by the rule that refuses its neighbour.  Before
#1870, `() == ()` lowered to an `i64.eq` over an empty stack (a module that
does not load, behind a green check and verify), `show` and `hash` of one
never evaluated it (`show(IO.print("a"))` printed no "a"), a `match` on one
dropped its function, a prelude generic read at `Unit` (`option_unwrap_or`)
and a read of `@Unit.result` ended in an internal error (E699).

The matrix is the class's whole space, by the registry:

- every built-in with a type variable or an `Eq`, `Ord` or `Hash` bound
  (`vera.builtins.BUILTINS`), each variable instantiated at each zero-size
  type with the others at `Int`;
- the four abilities' operations and the six comparison operators;
- `match` over such a scrutinee and a reference to such a result;
- each by position: a body, a `requires`, an `ensures`, an `assert`, an
  argument (a position whose expression cannot be written purely, a
  `Future<Unit>` in a contract, has no cell);
- each at `Unit`, `Future<Unit>` and `U`, a refinement of `Unit`.

Each cell's expectation is the table's (:func:`expected_registry_cell`,
:data:`OPERATORS`, :data:`ABILITIES`): refused at check with the code the
neighbour's rule gives (E135 for a zero-size element of an `Array`, `Map` or
`Set`, E206 for a generic whose body reads the variable, E143 and E242 for an
ordering, E182 for a read), or it checks, verifies with no error, compiles
with no function dropped, and prints what the table says.  A run cell holds
the same output at each of the three types: the value is the type's one
value, whichever spelling it has.
"""
from __future__ import annotations

from dataclasses import dataclass

import pytest

from tests import pipeline
from vera.builtins import BUILTINS, Prelude
from vera.prelude import prelude_forall_vars_read
from vera.types import AdtType, FunctionType, PrimitiveType, Type, TypeVar

pytestmark = pytest.mark.matrix(decides=[
    "vera/wasm/operators.py",
    "vera/wasm/calls_handlers.py",
    "vera/wasm/data.py",
    "vera/wasm/inference.py",
    "vera/environment.py",
    "vera/builtins.py",
    "vera/prelude.py",
    "vera/checker/expressions.py",
    "vera/smt.py",
])

# --- The three zero-size types ---------------------------------------------

#: Each zero-size type, by the name a cell spells it with, and an
#: expression of it.  A `Future<Unit>` is built by `async`, an effect, so it
#: is written only where `Async` is in the row.
ZERO_SIZE: dict[str, str] = {
    "Unit": "()",
    "Future<Unit>": "async(())",
    "U": "mk_u(1)",
}

PROLOGUE = """\
type U = { @Unit | true };

private fn mk_u(@Int -> @U)
  requires(true)
  ensures(true)
  effects(pure)
{
  ()
}

private fn idb(@Bool -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Bool.0
}

"""

MAIN_HEAD = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO, Async>)
{
"""


def program(statements: str, before: str = "") -> str:
    return PROLOGUE + before + MAIN_HEAD + statements + "\n}\n"


@dataclass(frozen=True)
class Expect:
    """A cell's expectation: refused at check with *code*, or runs and
    prints *stdout*."""

    code: str | None = None
    stdout: str | None = None


def assert_cell(source: str, expect: Expect) -> None:
    checked = pipeline.check(source)
    codes = sorted({d.error_code for d in checked.errors})
    if expect.code is not None:
        assert expect.code in codes, (codes, source)
        return
    assert checked.ok, (codes, source)
    verified = pipeline.verify(source, reconcile=True)
    assert not verified.errors, (
        [(d.error_code, d.description) for d in verified.errors], source)
    compiled = pipeline.compile(source)
    dropped = [d for d in compiled.diagnostics if d.error_code == "E602"]
    assert not dropped, ([d.description for d in dropped], source)
    ran = pipeline.run(compiled)
    assert ran.ok, (ran.trap, source)
    assert ran.stdout == expect.stdout, (ran.stdout, source)


# --- The registry ------------------------------------------------------------

_INT = PrimitiveType("Int")


def _sub(t: Type, mapping: dict[str, str]) -> str:
    """*t* spelled with each type variable replaced by *mapping*'s type."""
    if isinstance(t, TypeVar):
        return mapping[t.name]
    if isinstance(t, PrimitiveType):
        return t.name
    if isinstance(t, AdtType):
        if not t.type_args:
            return t.name
        return f"{t.name}<{', '.join(_sub(a, mapping) for a in t.type_args)}>"
    if isinstance(t, FunctionType):
        params = ", ".join(_sub(p, mapping) for p in t.params)
        return f"fn({params} -> {_sub(t.return_type, mapping)}) effects(pure)"
    raise AssertionError(t)  # pragma: no cover


def _value(t: Type, mapping: dict[str, str]) -> str:
    """An expression of *t* under *mapping* that reads no slot."""
    if isinstance(t, TypeVar):
        name = mapping[t.name]
        return ZERO_SIZE.get(name, "1")
    if isinstance(t, PrimitiveType):
        return {"Int": "1", "Nat": "1", "Bool": "true"}[t.name]
    if isinstance(t, FunctionType):
        params = ", ".join(f"@{_sub(p, mapping)}" for p in t.params)
        ret = _sub(t.return_type, mapping)
        return (f"fn({params} -> @{ret}) effects(pure) "
                f"{{ {_value(t.return_type, mapping)} }}")
    assert isinstance(t, AdtType), t
    args = t.type_args
    if t.name == "Array":
        return f"[{_value(args[0], mapping)}]"
    if t.name == "Option":
        return f"Some({_value(args[0], mapping)})"
    if t.name == "Result":
        return f"Ok({_value(args[0], mapping)})"
    if t.name == "Future":
        return f"async({_value(args[0], mapping)})"
    if t.name == "Map":
        return (f"map_insert(map_new(), {_value(args[0], mapping)}, "
                f"{_value(args[1], mapping)})")
    if t.name == "Set":
        return f"set_add(set_new(), {_value(args[0], mapping)})"
    if t.name == "Ordering":
        return "Less"
    raise AssertionError(t)  # pragma: no cover


def _holds_element(t: Type, var: str) -> bool:
    """Whether *var* stands inside an `Array`, `Map` or `Set` in *t*."""
    if isinstance(t, AdtType):
        if t.name in ("Array", "Map", "Set") and any(
                _mentions(a, var) for a in t.type_args):
            return True
        return any(_holds_element(a, var) for a in t.type_args)
    if isinstance(t, FunctionType):
        return any(_holds_element(p, var) for p in (*t.params, t.return_type))
    return False


def _mentions(t: Type, var: str) -> bool:
    if isinstance(t, TypeVar):
        return t.name == var
    if isinstance(t, AdtType):
        return any(_mentions(a, var) for a in t.type_args)
    if isinstance(t, FunctionType):
        return any(_mentions(p, var) for p in (*t.params, t.return_type))
    return False


#: What a call prints, `show` of its result, at a cell that runs: the same
#: at each zero-size type, which has one value.  Keyed by built-in and the
#: variable instantiated at the zero-size type.
RUNS: dict[tuple[str, str], str] = {
    ("option_map", "B"): "Some(unit)",
    ("option_and_then", "B"): "Some(unit)",
    ("result_unwrap_or", "E"): "1",
    ("result_map", "B"): "Ok(unit)",
    ("async", "T"): "unit",
    ("await", "T"): "unit",
}


def expected_registry_cell(name: str, var: str) -> Expect:
    """The table's verdict for built-in *name* with *var* at a zero-size
    type: E135 when the variable is an element of a container the type
    cannot be stored in (§2.2.2), E206 when the built-in's lowering reads a
    value of it, as a generic's body reads `@T.n` (§2.2.2, §2.7: the
    prelude body that lowers it, or the emitter's record), else the call
    runs."""
    spec = BUILTINS[name]
    sig = spec.signature
    if any(_holds_element(t, var) for t in (*sig.params, sig.ret)):
        return Expect(code="E135")
    if isinstance(spec.lowering, Prelude):
        reads = prelude_forall_vars_read().get(name, frozenset())
    else:
        reads = frozenset(getattr(spec.lowering, "reads", ()))
    if var in reads:
        return Expect(code="E206")
    return Expect(stdout=RUNS[(name, var)])


def _in_a_function_result(t: Type, var: str) -> bool:
    """Whether *var* stands in the result of a function type in *t*: a
    `Future<Unit>` there would be built inside a pure closure, where
    `async` cannot be called, so that cell has no program."""
    if isinstance(t, FunctionType):
        return _mentions(t.return_type, var)
    if isinstance(t, AdtType):
        return any(_in_a_function_result(a, var) for a in t.type_args)
    return False


def _registry_writable(name: str, var: str, zero: str) -> bool:
    sig = BUILTINS[name].signature
    return not (zero == "Future<Unit>" and any(
        _in_a_function_result(p, var) for p in sig.params))


REGISTRY_CELLS = [
    (name, var, zero)
    for name, spec in BUILTINS.items()
    if spec.signature.forall or spec.signature.constraints
    for var in (spec.signature.forall or ())
    for zero in ZERO_SIZE
    if _registry_writable(name, var, zero)
]


def registry_program(name: str, var: str, zero: str) -> str:
    sig = BUILTINS[name].signature
    mapping = {v: (zero if v == var else "Int") for v in sig.forall or ()}
    ret = _sub(sig.ret, mapping)
    if sig.params:
        call = f"{name}({', '.join(_value(p, mapping) for p in sig.params)})"
    else:
        # A call with no arguments takes its instance from the binding.
        call = f"{name}()"
    if _holds_element(sig.ret, var) or not sig.params:
        # The result is a container of the zero-size type, or the call
        # takes its instance from the binding: the binding states it.
        return program(f"  let @{ret} = {call};\n  IO.print(\"x\")")
    if ret in ZERO_SIZE or ret.startswith("Future<"):
        return program(f"  IO.print(show({call}))")
    return program(f"  let @{ret} = {call};\n  IO.print(show(@{ret}.0))")


@pytest.mark.parametrize(
    "cell", REGISTRY_CELLS, ids=lambda c: f"{c[0]}-{c[1]}-{c[2]}")
def test_every_generic_builtin_at_a_zero_size_type(
    cell: tuple[str, str, str],
) -> None:
    name, var, zero = cell
    assert_cell(registry_program(name, var, zero),
                expected_registry_cell(name, var))


def test_the_registry_cells_cover_every_generic_builtin() -> None:
    """The space: every built-in with a type variable is a cell, and every
    cell the table says runs has its output."""
    generic = {n for n, s in BUILTINS.items() if s.signature.forall}
    assert {c[0] for c in REGISTRY_CELLS} == generic
    runs = {(n, v) for n, v, _ in REGISTRY_CELLS
            if expected_registry_cell(n, v).code is None}
    assert runs == set(RUNS)


# --- Operators and abilities, by position ------------------------------------

#: Each comparison and ability operation over two (or one) operands, the
#: table's verdict, and a spelling that holds for a contract position.
#: `T`/`F` is what a body or an argument prints for its value.
OPERATORS: dict[str, tuple[str, Expect]] = {
    "==": ("{a} == {b}", Expect(stdout="T")),
    "!=": ("{a} != {b}", Expect(stdout="F")),
    "<": ("{a} < {b}", Expect(code="E143")),
    "<=": ("{a} <= {b}", Expect(code="E143")),
    ">": ("{a} > {b}", Expect(code="E143")),
    ">=": ("{a} >= {b}", Expect(code="E143")),
    "eq": ("eq({a}, {b})", Expect(stdout="T")),
}

ABILITIES: dict[str, tuple[str, str, Expect]] = {
    # operation, its type, a contract that holds, verdict
    "show": ("show({a})", "String", Expect(stdout="unit")),
    "hash": ("hash({a})", "Int", Expect(stdout="0")),
    "compare": ("compare({a}, {b})", "Ordering", Expect(code="E242")),
}

POSITIONS = ("body", "requires", "ensures", "assert", "argument")

#: The positions whose expression must be pure (a contract, an `assert`'s
#: predicate, E187): a `Future<Unit>` is built only by `async`, an effect,
#: so it has no expression there, and no cell.
PURE_POSITIONS = ("requires", "ensures", "assert")


def _writable(zero: str, position: str) -> bool:
    return not (zero == "Future<Unit>" and position in PURE_POSITIONS)

#: A position whose cell meets another mechanism: `eq` inside an `assert` is
#: never rewritten to `==` (#1525's walk over a fixed list of expression
#: kinds), so its function is dropped whatever its operands are.
WALK_1525 = {("eq", "assert")}


def _operator_program(op: str, zero: str, position: str) -> str | None:
    template = OPERATORS[op][0]
    a = b = ZERO_SIZE[zero]
    expr = template.format(a=a, b=b)
    holds = f"!({expr})" if op == "!=" else expr
    if not _writable(zero, position):
        return None
    if position in ("requires", "ensures"):
        clause = (f"requires({holds})\n  ensures(true)"
                  if position == "requires"
                  else f"requires(true)\n  ensures({holds})")
        callee = (f"private fn c(@Int -> @Int)\n  {clause}\n  effects(pure)\n"
                  "{\n  @Int.0\n}\n\n")
        return program("  IO.print(int_to_string(c(1)))", before=callee)
    if position == "assert":
        return program(f"  assert({holds});\n  IO.print(\"T\")")
    value = expr if position == "body" else f"idb({expr})"
    return program(f"  let @Bool = {value};\n"
                   "  IO.print(if @Bool.0 then { \"T\" } else { \"F\" })")


def _operator_expect(op: str, position: str) -> Expect:
    expect = OPERATORS[op][1]
    if expect.code is not None:
        return expect
    if position in ("requires", "ensures"):
        return Expect(stdout="1")
    if position == "assert":
        return Expect(stdout="T")
    return expect


OPERATOR_CELLS = [
    pytest.param(
        op, zero, pos,
        marks=[pytest.mark.xfail(
            strict=True, reason="#1525: eq is not rewritten inside assert")]
        if (op, pos) in WALK_1525 and OPERATORS[op][1].code is None else [],
        id=f"{op}-{zero}-{pos}")
    for op in OPERATORS for zero in ZERO_SIZE for pos in POSITIONS
    if _operator_program(op, zero, pos) is not None
]


@pytest.mark.parametrize(("op", "zero", "position"), OPERATOR_CELLS)
def test_every_comparison_of_zero_size_values(
    op: str, zero: str, position: str,
) -> None:
    source = _operator_program(op, zero, position)
    assert source is not None
    assert_cell(source, _operator_expect(op, position))


def _ability_program(name: str, zero: str, position: str) -> str | None:
    template, ty, _ = ABILITIES[name]
    a = ZERO_SIZE[zero]
    expr = template.format(a=a, b=a)
    shown = {"String": "@String.0", "Int": "int_to_string(@Int.0)",
             "Ordering": "show(@Ordering.0)"}[ty]
    if not _writable(zero, position):
        return None
    if position in ("requires", "ensures"):
        holds = {"show": f'{expr} == "unit"', "hash": f"{expr} == 0",
                 "compare": f"{expr} == Equal"}[name]
        clause = (f"requires({holds})\n  ensures(true)"
                  if position == "requires"
                  else f"requires(true)\n  ensures({holds})")
        callee = (f"private fn c(@Int -> @Int)\n  {clause}\n  effects(pure)\n"
                  "{\n  @Int.0\n}\n\n")
        return program("  IO.print(int_to_string(c(1)))", before=callee)
    if position == "assert":
        holds = {"show": f'{expr} == "unit"', "hash": f"{expr} == 0",
                 "compare": f"{expr} == Equal"}[name]
        return program(f"  assert({holds});\n  IO.print(\"T\")")
    if position == "body":
        return program(f"  let @{ty} = {expr};\n  IO.print({shown})")
    # argument: the operation's value handed to a function of its type
    ident = (f"private fn ident(@{ty} -> @{ty})\n  requires(true)\n"
             f"  ensures(true)\n  effects(pure)\n{{\n  @{ty}.0\n}}\n\n")
    return program(f"  let @{ty} = ident({expr});\n  IO.print({shown})",
                   before=ident)


def _ability_expect(name: str, position: str) -> Expect:
    expect = ABILITIES[name][2]
    if expect.code is not None:
        return expect
    if position in ("requires", "ensures"):
        return Expect(stdout="1")
    if position == "assert":
        return Expect(stdout="T")
    return expect


ABILITY_CELLS = [
    pytest.param(name, zero, pos, id=f"{name}-{zero}-{pos}")
    for name in ABILITIES for zero in ZERO_SIZE for pos in POSITIONS
    if _ability_program(name, zero, pos) is not None
]


@pytest.mark.parametrize(("name", "zero", "position"), ABILITY_CELLS)
def test_every_ability_operation_on_a_zero_size_value(
    name: str, zero: str, position: str,
) -> None:
    source = _ability_program(name, zero, position)
    assert source is not None
    assert_cell(source, _ability_expect(name, position))


# --- Operands evaluated for their effects, in order --------------------------

#: An operand with an effect, at each lowering that takes one: the effect
#: happens, in order, and then the result the table gives.
EFFECT_CELLS: dict[str, tuple[str, str]] = {
    "eq_operator": (
        '  let @Bool = IO.print("a") == IO.print("b");\n'
        '  IO.print(if @Bool.0 then { "T" } else { "F" })', "abT"),
    "neq_operator": (
        '  let @Bool = IO.print("a") != IO.print("b");\n'
        '  IO.print(if @Bool.0 then { "T" } else { "F" })', "abF"),
    "eq_ability": (
        '  let @Bool = eq(IO.print("a"), IO.print("b"));\n'
        '  IO.print(if @Bool.0 then { "T" } else { "F" })', "abT"),
    "show": ('  IO.print(show(IO.print("a")))', "aunit"),
    "hash": ('  IO.print(int_to_string(hash(IO.print("a"))))', "a0"),
    "match": ('  IO.print(match IO.print("a") { _ -> "T" })', "aT"),
    "match_binder": ('  IO.print(match IO.print("a") { @Unit -> "T" })', "aT"),
    "match_future": ('  IO.print(match async(IO.print("a")) { _ -> "T" })',
                     "aT"),
    "match_refined": ('  IO.print(match mk_u(1) { _ -> "T" })', "T"),
    # The built-in `Future`'s constructor over an irrefutable pattern
    # matches the one value too, and binds no local.
    "match_future_pattern": (
        '  IO.print(match async(IO.print("a")) { Future(_) -> "T" })', "aT"),
    "match_future_binder": (
        '  IO.print(match async(()) { Future(@Unit) -> "T" })', "T"),
}


@pytest.mark.parametrize("cell", sorted(EFFECT_CELLS))
def test_an_operand_with_an_effect_is_evaluated_in_order(cell: str) -> None:
    statements, stdout = EFFECT_CELLS[cell]
    assert_cell(program(statements), Expect(stdout=stdout))


# --- A reference to a zero-size result ---------------------------------------

@pytest.mark.parametrize("zero", list(ZERO_SIZE))
@pytest.mark.parametrize("use", [
    "@{z}.result == @{z}.result", 'show(@{z}.result) == "unit"'])
def test_a_reference_to_a_zero_size_result_is_refused(zero: str, use: str) -> None:
    """E182, the rule that refuses `@Unit.0` (§2.2.2): the result has no
    value to read.  It ended in E699 when compared.  A `Future<Unit>` is
    built by `async`, so its function declares `Async`; the postcondition
    calls nothing."""
    value = ZERO_SIZE[zero]
    effects = "<Async>" if zero == "Future<Unit>" else "pure"
    callee = (f"private fn g(@Int -> @{zero})\n  requires(true)\n"
              f"  ensures({use.format(z=zero)})\n  effects({effects})\n"
              "{\n  " + value + "\n}\n\n")
    assert_cell(program("  IO.print(\"x\")", before=callee), Expect(code="E182"))


# --- A generic that reads its type parameter only through its result -------

#: The generic's body reads no `@T` slot; its postcondition reads
#: `@T.result`.  At a zero-size type the result has no local, so the read
#: is a read of `T` and the instance is refused (E206); at `Int` it runs.
RESULT_ONLY_GENERIC = """\
type Gen<A> = fn(Unit -> A) effects({eff});

private forall<T> fn run(@Gen<T> -> @T)
  requires(true)
  ensures(@T.result == @T.result)
  effects({eff})
{{
  apply_fn(@Gen<T>.0, ())
}}

"""


@pytest.mark.parametrize("zero", [*ZERO_SIZE, "Int"])
def test_a_generic_read_only_through_its_result(zero: str) -> None:
    value = {**ZERO_SIZE, "Int": "1"}[zero]
    eff = "<Async>" if zero == "Future<Unit>" else "pure"
    before = RESULT_ONLY_GENERIC.format(eff=eff)
    call = f"  run(fn(@Unit -> @{zero}) effects({eff}) {{ {value} }});\n"
    expect = Expect(stdout="x") if zero == "Int" else Expect(code="E206")
    assert_cell(program(call + '  IO.print("x")', before=before), expect)


# --- An operand that does not complete ---------------------------------------

NEVER_CELLS = {
    "int_eq_throw": 'if 1 == throw("x") then { "T" } else { "F" }',
    "unit_eq_throw": 'if () == throw("x") then { "T" } else { "F" }',
    "show_throw": 'show(throw("x"))',
    "hash_throw": 'int_to_string(hash(throw("x")))',
    "match_throw": 'match throw("x") { _ -> "T" }',
}


@pytest.mark.parametrize("cell", sorted(NEVER_CELLS))
def test_an_operand_that_does_not_complete(cell: str) -> None:
    """A `Never` has no value either: the lowering after it is never
    reached, and the handler's value is printed."""
    statements = (
        "  IO.print(handle[Exn<String>] {\n"
        '    throw(@String) -> "caught"\n'
        "  } in {\n"
        f"    {NEVER_CELLS[cell]}\n"
        "  })")
    assert_cell(program(statements), Expect(stdout="caught"))


# --- The reported instances, red first ---------------------------------------

def test_repro_1870_unit_equality_loads_and_is_true() -> None:
    source = (
        "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
        "  effects(<IO>)\n{\n"
        '  IO.print(if () == () then { "same\\n" } else { "diff\\n" })\n}\n')
    assert pipeline.run(source).stdout == "same\n"


def test_repro_1870_show_of_an_effect_evaluates_it() -> None:
    source = program('  IO.print(show(IO.print("a")))')
    assert pipeline.run(source).stdout == "aunit"


def test_repro_1870_prelude_generic_at_unit_is_refused() -> None:
    source = program("  option_unwrap_or(Some(()), ());\n  IO.print(\"x\")")
    assert "E206" in {d.error_code for d in pipeline.check(source).errors}


def test_the_comparison_dispatch_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A pair of widths the comparison dispatch has no rule for is an
    internal error (E699), never the i64 default: with the zero-size rule
    blinded, `() == ()` reaches the default's guard, which refuses it where
    the default wrote the module that did not load."""
    from vera.wasm.inference import InferenceMixin

    monkeypatch.setattr(InferenceMixin, "_holds_nothing",
                        lambda self, expr: None)
    compiled = pipeline.compile(program(
        '  let @Bool = () == ();\n  IO.print(if @Bool.0 then { "T" } else { "F" })'))
    codes = {d.error_code for d in compiled.diagnostics}
    assert "E699" in codes, codes


def test_repro_1870_verifier_proves_unit_equality() -> None:
    """Two `Unit` values are equal at Tier 1, and a claim that they differ
    is refuted, not left to run time."""
    holds = ("public fn f(@Unit -> @Bool)\n  requires(true)\n"
             "  ensures(@Bool.result == true)\n  effects(pure)\n{\n  () == ()\n}\n")
    refuted = holds.replace("== true", "== false")
    verified = pipeline.verify(holds)
    assert verified.ok and verified.result.summary.tier3_runtime == 0
    assert "E500" in {d.error_code for d in pipeline.verify(refuted).errors}


# --- Unparametrised: one cell per rule, for the sampled gate ----------------
#
# The gate on a pull request samples the matrix above, so each rule this
# change adds has a cell here that runs on every pull request.

def _runs(statements: str, stdout: str, before: str = "") -> None:
    assert_cell(program(statements, before=before), Expect(stdout=stdout))


def test_repro_unit_inequality_is_false() -> None:
    _runs('  let @Bool = () != ();\n'
          '  IO.print(if @Bool.0 then { "T" } else { "F" })', "F")


def test_repro_both_operands_are_evaluated_in_order() -> None:
    _runs('  let @Bool = IO.print("a") == IO.print("b");\n'
          '  IO.print(if @Bool.0 then { "T" } else { "F" })', "abT")


def test_repro_hash_of_an_effect_evaluates_it() -> None:
    _runs('  IO.print(int_to_string(hash(IO.print("a"))))', "a0")


def test_repro_a_match_on_an_effect_evaluates_it() -> None:
    _runs('  IO.print(match IO.print("a") { _ -> "T" })', "aT")


def test_repro_a_future_pattern_over_a_zero_size_scrutinee() -> None:
    _runs('  IO.print(match async(IO.print("a")) { Future(@Unit) -> "T" })',
          "aT")


def test_repro_an_operand_that_does_not_complete() -> None:
    for expr in ('if 1 == throw("x") then { "T" } else { "F" }',
                 'match throw("x") { _ -> "T" }'):
        _runs("  IO.print(handle[Exn<String>] {\n"
              '    throw(@String) -> "caught"\n'
              f"  }} in {{\n    {expr}\n  }})", "caught")


def test_repro_show_and_hash_read_their_argument_s_slots() -> None:
    """The argument is translated in the function's own environment: a
    `Unit` call reading a parameter, and a `String` read from a slot."""
    source = (PROLOGUE
              + "private fn u(@Int -> @Unit)\n  requires(true)\n"
              "  ensures(true)\n  effects(pure)\n{\n  ()\n}\n\n"
              "public fn s(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
              "  effects(pure)\n{\n"
              "  string_length(show(u(@Int.0))) + hash(u(@Int.0))\n}\n")
    assert pipeline.run(source, fn="s", args=[1]).execution.value == 4
    _runs('  let @String = "ab";\n  IO.print(show(@String.0))', "ab")


def test_repro_hash_of_a_float_and_a_string() -> None:
    """`Float64` hashes to its bit pattern, a `String` to FNV-1a over its
    bytes (spec §9.8.1)."""
    _runs("  IO.print(int_to_string(hash(1.5)))", "4609434218613702656")
    _runs('  IO.print(int_to_string(hash("ab")))', "620445648566982762")


def test_repro_array_fold_at_a_unit_accumulator_is_refused() -> None:
    source = program(
        "  array_fold([1], (), fn(@Unit, @Int -> @Unit) effects(pure) "
        "{ () });\n  IO.print(\"x\")")
    assert "E206" in {d.error_code for d in pipeline.check(source).errors}


def test_repro_a_zero_size_result_reference_is_refused() -> None:
    callee = ("private fn g(@Int -> @Unit)\n  requires(true)\n"
              "  ensures(@Unit.result == ())\n  effects(pure)\n{\n  ()\n}\n\n")
    source = program('  IO.print("x")', before=callee)
    assert "E182" in {d.error_code for d in pipeline.check(source).errors}


def test_repro_a_contract_over_two_calls_returning_a_refined_unit() -> None:
    """Two stand-in terms of a call's result were chosen unequal (E501)."""
    callee = ("private fn c(@Int -> @Int)\n  requires(mk_u(1) == mk_u(2))\n"
              "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n\n")
    _runs("  IO.print(int_to_string(c(1)))", "1", before=callee)


def test_repro_an_ordering_of_zero_size_values_is_an_internal_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The checker refuses `<` over `Unit` (E143); with every integer
    literal made to read as zero-size, `1 < 2` reaches the guard behind
    it, which names the comparison."""
    from vera import ast
    from vera.wasm.inference import InferenceMixin

    monkeypatch.setattr(
        InferenceMixin, "_holds_nothing",
        lambda self, expr: "unit" if isinstance(expr, ast.IntLit) else None)
    source = program("  let @Bool = 1 < 2;\n"
                     '  IO.print(if @Bool.0 then { "T" } else { "F" })')
    compiled = pipeline.compile(source)
    internal = [d for d in compiled.diagnostics if d.error_code == "E699"]
    assert internal, [d.error_code for d in compiled.diagnostics]
    assert ("an operator other than == and != over two values of a type "
            "with no WebAssembly value" in internal[0].description), (
        internal[0].description)
    line = source.splitlines().index("  let @Bool = 1 < 2;") + 1
    assert internal[0].location.line == line, internal[0].location


def test_repro_the_verifier_reads_both_operands_types() -> None:
    """Two values are equal by their type only when both operands' checked
    types erase: with no types recorded, or one side a value, the rule
    gives no verdict."""
    from vera import ast
    from vera.smt import SmtContext
    from vera.types import INT, UNIT

    left, right = ast.UnitLit(), ast.IntLit(value=1)
    expr = ast.BinaryExpr(left=left, op=ast.BinOp.EQ, right=right)
    ctx = SmtContext()
    assert not ctx._compares_two_zero_size_values(expr)
    types = {id(left): UNIT, id(right): INT}
    ctx._recorded_type_hook = lambda node: types.get(id(node))
    assert not ctx._compares_two_zero_size_values(expr)
    types[id(right)] = UNIT
    assert ctx._compares_two_zero_size_values(expr)


# --- Every binary dispatch, by operand type, by which side holds nothing ----
#
# Each dispatch of a binary operator by its operands' type (`Int`, `Nat`,
# `Byte`, `Float64`, `Bool`, `String`, a data type, an array) is crossed
# with a `Never` operand (a call of a function that does not return, and a
# `throw`) or a `Unit` one, on either side, under each operator class.  A
# cell the checker accepts is validated by wasmtime and run; a dispatch
# that returned before the zero-size rule (the `Byte` one, #1905's second
# review) wrote a module that did not load.

BINARY_PROLOGUE = """\
private fn stop(@Unit -> @Never)
  requires(true)
  ensures(true)
  effects(<Exn<String>>)
{
  throw("x")
}

private fn nat1(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

private fn byte1(@Unit -> @Byte)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

"""

OPERAND_VALUES: dict[str, str] = {
    "Int": "1",
    "Nat": "nat1(())",
    "Byte": "byte1(())",
    "Float64": "1.5",
    "Bool": "true",
    "String": '"s"',
    "data": "Some(1)",
    "array": "[1]",
}

#: The operand with no value.  A call of a function declared to return
#: `Never` is not here: code generation drops such a function (`E601`),
#: another mechanism, pinned by a strict xfail below.
NOTHING_VALUES: dict[str, str] = {
    "never": 'throw("x")',
    "unit": "()",
}

OPERATOR_CLASSES: dict[str, str] = {
    "equality": "==",
    "ordering": "<",
    "arithmetic": "+",
    "boolean": "&&",
}


def _binary_program(ty: str, nothing: str, side: str, cls: str) -> str:
    a, b = OPERAND_VALUES[ty], NOTHING_VALUES[nothing]
    left, right = (b, a) if side == "left" else (a, b)
    expr = f"{left} {OPERATOR_CLASSES[cls]} {right}"
    shown = f"show({expr})" if cls == "arithmetic" else (
        f'if {expr} then {{ "T" }} else {{ "F" }}')
    return (BINARY_PROLOGUE
            + "public fn main(@Unit -> @Unit)\n  requires(true)\n"
            "  ensures(true)\n  effects(<IO>)\n{\n"
            "  IO.print(handle[Exn<String>] {\n"
            '    throw(@String) -> "caught"\n'
            f"  }} in {{\n    {shown}\n  }})\n}}\n")


BINARY_CELLS = [
    pytest.param(ty, nothing, side, cls, id=f"{ty}-{nothing}-{side}-{cls}")
    for ty in OPERAND_VALUES for nothing in NOTHING_VALUES
    for side in ("left", "right") for cls in OPERATOR_CLASSES
]


def expected_binary(ty: str, nothing: str, side: str, cls: str) -> set[str]:
    """The table's codes for a cell, or none for one that runs.

    Equality takes `Unit` beside another type as incompatible (E142), and
    judges `Eq` by its left operand, so a `Never` there, or an `Array`, is
    no `Eq` type (E243).  Ordering takes neither as orderable (E143), nor
    arithmetic as numeric (E140).  `&&` takes `Never` as a `Bool` and
    `Unit` as none: a left operand that is not one is E144, a right one
    E145."""
    other = "left" if side == "right" else "right"
    sides = {side: nothing, other: ty}
    if cls == "equality":
        if nothing == "unit":
            return {"E142"}
        return {"E243"} if sides["left"] in ("never", "array") else set()
    if cls == "ordering":
        return {"E143"}
    if cls == "arithmetic":
        return {"E140"}
    codes = set()
    if sides["left"] not in ("Bool", "never"):
        codes.add("E144")
    if sides["right"] not in ("Bool", "never"):
        codes.add("E145")
    return codes


@pytest.mark.parametrize(("ty", "nothing", "side", "cls"), BINARY_CELLS)
def test_every_binary_dispatch_beside_an_operand_with_no_value(
    ty: str, nothing: str, side: str, cls: str,
) -> None:
    import wasmtime

    source = _binary_program(ty, nothing, side, cls)
    checked = pipeline.check(source)
    codes = {d.error_code for d in checked.errors}
    assert codes == expected_binary(ty, nothing, side, cls), (codes, source)
    if codes:
        return
    compiled = pipeline.compile(source)
    assert compiled.ok, ([d.error_code for d in compiled.diagnostics], source)
    config = wasmtime.Config()
    config.wasm_exceptions = True
    wasmtime.Module.validate(wasmtime.Engine(config),
                             compiled.result.wasm_bytes)
    ran = pipeline.run(compiled)
    assert ran.ok, (ran.trap, source)
    assert ran.stdout == "caught", (ran.stdout, source)


@pytest.mark.xfail(strict=True, reason=(
    "a function declared to return Never is dropped by code generation "
    "(E601), another mechanism"))
def test_a_call_of_a_function_that_returns_never() -> None:
    source = (BINARY_PROLOGUE
              + "public fn main(@Unit -> @Unit)\n  requires(true)\n"
              "  ensures(true)\n  effects(<IO>)\n{\n"
              "  IO.print(handle[Exn<String>] {\n"
              '    throw(@String) -> "caught"\n'
              "  } in {\n"
              '    if byte1(()) == stop(()) then { "T" } else { "F" }\n'
              "  })\n}\n")
    assert pipeline.run(source).stdout == "caught"


def test_repro_a_generic_read_only_through_its_result_at_unit() -> None:
    """`@T.result` is a read of `T`: at `Unit` the instance has no result
    local, and the call was an internal error (E699) behind a green check."""
    before = RESULT_ONLY_GENERIC.format(eff="pure")
    call = "  run(fn(@Unit -> @Unit) effects(pure) { () });\n"
    source = program(call + '  IO.print("x")', before=before)
    assert "E206" in {d.error_code for d in pipeline.check(source).errors}


@pytest.mark.parametrize("zero", list(ZERO_SIZE))
def test_e163_at_a_zero_size_result_offers_no_reference(zero: str) -> None:
    """A result reference of another type on a function whose result is
    zero-size: E163 says the result has no value to read and names no
    reference (the one it named, `@Unit.result`, is E182).  Its fix applied
    as written checks clean."""
    value = ZERO_SIZE[zero]
    effects = "<Async>" if zero == "Future<Unit>" else "pure"
    callee = ("private fn g(@Int -> @{z})\n  requires(true)\n"
              "  ensures({e})\n  effects({f})\n{{\n  {v}\n}}\n\n")
    source = program('  IO.print("x")', before=callee.format(
        z=zero, e="@Int.result == 1", f=effects, v=value))
    checked = pipeline.check(source)
    (diag,) = [d for d in checked.errors if d.error_code == "E163"]
    assert "a zero-size result has no value to read" in diag.description
    assert ".result" not in diag.fix, diag.fix
    assert diag.fix == ("Remove the result reference; with nothing else to "
                        "state, write `ensures(true)`.")
    fixed = program('  IO.print("x")', before=callee.format(
        z=zero, e="true", f=effects, v=value))
    assert pipeline.check(fixed).ok


def test_repro_e163_at_a_unit_result() -> None:
    callee = ("private fn g(@Int -> @Unit)\n  requires(true)\n"
              "  ensures(@Int.result == 1)\n  effects(pure)\n{\n  ()\n}\n\n")
    checked = pipeline.check(program('  IO.print("x")', before=callee))
    (diag,) = [d for d in checked.errors if d.error_code == "E163"]
    assert ".result" not in diag.fix, diag.fix


def test_repro_a_short_circuit_never_reaches_a_right_operand_it_skips() -> None:
    """The right operand of `&&`, `||` and `==>` runs only where the left
    does not decide: a `throw` there is not reached when the left does."""
    for expr, out in (('false && throw("x")', "F"),
                      ('true || throw("x")', "T"),
                      ('false ==> throw("x")', "T"),
                      ('true && throw("x")', "caught")):
        _runs("  IO.print(handle[Exn<String>] {\n"
              '    throw(@String) -> "caught"\n'
              f"  }} in {{\n    if {expr} then {{ \"T\" }} else {{ \"F\" }}\n"
              "  })", out)
