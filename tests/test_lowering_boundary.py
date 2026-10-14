"""What code generation can lower is decided once, and the checker refuses the rest.

The class (#1597, #1512, #1506, #1499, #1522): a construct `vera check`
accepts, and code generation then refuses (E602, E607, E612, E613, E699) or
compiles to a module that does not load, because the backend has no lowering
for it.  `vera/lowering.py` holds each rule once; the checker refuses the
construct where it is written, and code generation asks the same function at
its own refusal site, where a refusal is an internal error naming the rule
the checker should have applied.

The reported programs are the unparametrised ``test_repro_*`` tests below:
each was accepted by `vera check` and refused by code generation, and each is
now refused at check, at the construct, with its code.
"""

from __future__ import annotations

from dataclasses import dataclass

import pytest
import wasmtime

from tests import pipeline as vera_pipeline
from vera.checker.registration import builtin_effect_names
from vera.environment import TypeEnv
from vera.errors import Diagnostic

# A class instrument (tests/matrix_sample.py): a pull request runs a sample of
# its parametrised cells, and all of them when it changes this file or a
# module that decides its class, here what code generation lowers and where
# the checker refuses the rest.
pytestmark = pytest.mark.matrix(
    decides=[
        "vera/lowering.py",
        "vera/checker/control.py",
        "vera/checker/calls.py",
        "vera/checker/core.py",
        "vera/checker/expressions.py",
        "vera/codegen/compilability.py",
        "vera/codegen/monomorphize.py",
        "vera/wasm/calls_handlers.py",
        "vera/wasm/operators.py",
    ],
)


def _locate(source: str, marker: str, occurrence: int = 0) -> tuple[int, int]:
    """1-based (line, column) of *marker*'s *occurrence*-th match."""
    idx = -1
    for _ in range(occurrence + 1):
        idx = source.index(marker, idx + 1)
    line = source.count("\n", 0, idx) + 1
    column = idx - (source.rfind("\n", 0, idx) + 1) + 1
    return line, column


def _placed(errors: tuple[Diagnostic, ...]) -> list[tuple[str, int, int]]:
    return [(d.error_code, d.location.line, d.location.column) for d in errors]


def _codegen_refuses(source: str) -> bool:
    """The premise of every repro: past the check, code generation refuses
    the program — a diagnostic of its own (an E6xx, or an error it emits
    without a code) or a module that does not load."""
    compiled = vera_pipeline.compile(source, past_check=True)
    result = compiled.result
    if any((d.error_code or "").startswith("E6") or d.severity == "error"
           for d in result.diagnostics):
        return True
    try:
        ran = vera_pipeline.run(result, fn="main")
    except wasmtime.WasmtimeError:
        return True  # the module does not load
    return not ran.ok


# =====================================================================
# The reported programs
# =====================================================================

_REPRO_1597 = """\
public fn fetch(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(<Http>)
{
  Http.get(@String.0)
}

public fn test_fetch(@String -> @Result<String, String>)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Http] {
    get(@String) -> { resume(Ok("mock")) },
    post(@String, @String) -> { resume(Ok("mock")) }
  } in {
    fetch(@String.0)
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match test_fetch("u") {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""

_REPRO_1512 = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<String>](@String = "") {
    get(@Unit) -> { resume(@String.0) },
    put(@String) -> { resume(()) }
  } in {
    put("abcde");
    string_length(get(()))
  }
}
"""

_REPRO_1499_BARE = """\
ability Sz<T> {
  op size(T -> Int);
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  size(1)
}
"""

_REPRO_1499_CONSTRAINED = """\
ability Sz<T> {
  op size(T -> Int);
}

public forall<T where Sz<T>> fn measure(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  size(@T.0)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  measure(1)
}
"""

#: The constraint alone, with no operation called: code generation refuses
#: any instantiation of a generic a user ability constrains (E613).
_REPRO_1499_CONSTRAINT_ONLY = _REPRO_1499_CONSTRAINED.replace(
    "  size(@T.0)\n", "  0\n")

_REPRO_1499_QUALIFIED = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if Eq.eq(1, 1) then {
    1
  } else {
    0
  }
}
"""

_REPRO_1522 = """\
private forall<T> fn g(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 0) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    handle[State<T>](@T = @T.0) {
      get(@Unit) -> { resume(@T.0) },
      put(@T) -> { put(1);
        resume(()) }
    } in {
      put(@T.0);
      1
    }
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  g(5)
}
"""

#: #1506's remaining shapes: a quantifier position written as a type
#: parameter, instantiated where code generation's i64 counter or i32 result
#: cannot stand for it.  Each was accepted, and compiled to a module that
#: fails to load.
_KEEP = """\
private forall<T> fn keep(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

"""
_QUANT_GENERIC = _KEEP + """\
private forall<T> fn q(@T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  QUANT
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  if q(ARG) then {
    1
  } else {
    0
  }
}
"""

_REPRO_1506_PARAMETER = _QUANT_GENERIC.replace(
    "QUANT", "forall(@Nat, 3, fn(@T -> @Bool) effects(pure) "
             "{ let @T = keep(@T.0);\n    true })").replace("ARG", "true")
_REPRO_1506_RESULT = _QUANT_GENERIC.replace(
    "QUANT", "forall(@Nat, 3, fn(@Nat -> @T) effects(pure) { @T.0 })"
).replace("ARG", "5")
_REPRO_1506_BOUND = _QUANT_GENERIC.replace(
    "QUANT", "forall(@Nat, @T.0, fn(@Nat -> @Bool) effects(pure) { true })"
).replace("ARG", "true")


def test_repro_1597_handler_for_http() -> None:
    """A `handle[Http]` mock: check accepted it and code generation dropped
    `test_fetch` (E602).  Refused at the handler."""
    assert _codegen_refuses(_REPRO_1597)
    checked = vera_pipeline.check(_REPRO_1597)
    assert _placed(checked.errors) == [
        ("E340", *_locate(_REPRO_1597, "handle[Http]"))]


def test_repro_1512_state_string_cell() -> None:
    """A `State<String>` cell: code generation refused it (E607).  Refused
    at the cell type."""
    assert _codegen_refuses(_REPRO_1512)
    checked = vera_pipeline.check(_REPRO_1512)
    assert _placed(checked.errors) == [
        ("E340", *_locate(_REPRO_1512, "String>"))]


def test_repro_1499_bare_user_ability_operation() -> None:
    """`size(1)` for a user ability's operation: code generation found no
    function to call.  Refused at the call."""
    assert _codegen_refuses(_REPRO_1499_BARE)
    checked = vera_pipeline.check(_REPRO_1499_BARE)
    assert _placed(checked.errors) == [
        ("E340", *_locate(_REPRO_1499_BARE, "size(1)"))]


def test_repro_1499_operation_through_a_user_ability_constraint() -> None:
    """`size(@T.0)` under `where Sz<T>`: E613 at line 0.  Refused at the
    constraint and at the call."""
    assert _codegen_refuses(_REPRO_1499_CONSTRAINED)
    checked = vera_pipeline.check(_REPRO_1499_CONSTRAINED)
    assert _placed(checked.errors) == [
        ("E340", *_locate(_REPRO_1499_CONSTRAINED, "Sz<T>>")),
        ("E340", *_locate(_REPRO_1499_CONSTRAINED, "size(@T.0)")),
    ]


def test_repro_1499_user_ability_constraint_alone() -> None:
    """The constraint with no operation called: still E613 at compile, so
    the constraint itself is the construct refused."""
    assert _codegen_refuses(_REPRO_1499_CONSTRAINT_ONLY)
    checked = vera_pipeline.check(_REPRO_1499_CONSTRAINT_ONLY)
    assert _placed(checked.errors) == [
        ("E340", *_locate(_REPRO_1499_CONSTRAINT_ONLY, "Sz<T>>"))]


def test_repro_1499_qualified_ability_call() -> None:
    """`Eq.eq(1, 1)` was E220, whose fix told the reader to declare an
    effect named `Eq`.  A qualified call to an ability operation is E340
    now, with the bare call as the fix."""
    checked = vera_pipeline.check(_REPRO_1499_QUALIFIED)
    assert _placed(checked.errors) == [
        ("E340", *_locate(_REPRO_1499_QUALIFIED, "Eq.eq"))]
    assert "eq(1, 1)" in checked.errors[0].fix


def test_repro_1522_generic_cell_nested_in_same_family() -> None:
    """`State<T>` nested in `State<Int>` with a clause-body `put`: at
    `T = Int` code generation dropped `g$Int` (E602, E620).  E339 at the
    operation, naming the instantiation."""
    assert _codegen_refuses(_REPRO_1522)
    checked = vera_pipeline.check(_REPRO_1522)
    assert _placed(checked.errors) == [
        ("E339", *_locate(_REPRO_1522, "put(1)"))]
    assert "State<T>" in checked.errors[0].description


def test_repro_1506_predicate_parameter_type_parameter() -> None:
    """`fn(@T -> @Bool)` read at `T = Bool`: the module failed to load."""
    assert _codegen_refuses(_REPRO_1506_PARAMETER)
    checked = vera_pipeline.check(_REPRO_1506_PARAMETER)
    assert _placed(checked.errors) == [
        ("E179", *_locate(_REPRO_1506_PARAMETER, "T -> @Bool) effects"))]


def test_repro_1506_predicate_result_type_parameter() -> None:
    """`fn(@Nat -> @T)` at `T = Int`: the module failed to load."""
    assert _codegen_refuses(_REPRO_1506_RESULT)
    checked = vera_pipeline.check(_REPRO_1506_RESULT)
    assert _placed(checked.errors) == [
        ("E179", *_locate(_REPRO_1506_RESULT, "T) effects"))]


def test_repro_1506_bound_type_parameter() -> None:
    """A bound typed by a type parameter at `T = Bool`: the module failed
    to load."""
    assert _codegen_refuses(_REPRO_1506_BOUND)
    checked = vera_pipeline.check(_REPRO_1506_BOUND)
    assert _placed(checked.errors) == [
        ("E128", *_locate(_REPRO_1506_BOUND, "@T.0, fn"))]


# =====================================================================
# The class instrument: every rule over every shape of its construct
# =====================================================================
#
# Each cell is a program and the verdict a stated rule gives it, written in
# the cell (never computed by `vera/lowering.py`, which is what is under
# test).  Every cell asserts THE invariant: refused at check with the rule's
# code, XOR checked clean, compiled, loaded and run to its value.  A refused
# cell also asserts the refusal is the backend's: past the check, code
# generation refuses the program too, so a rule cannot refuse what lowers.
# Every refusal has its nearest accepted neighbour as a cell beside it.


@dataclass(frozen=True)
class Verdict:
    """What the toolchain did with one program."""

    #: The check's error codes, in source order.
    check_codes: tuple[str, ...]
    #: Code generation's refusals: an E6xx at any severity, or an error.
    drops: tuple[str, ...]
    #: Whether the compiled module loaded.
    loads: bool
    #: ``main``'s value, when it ran.
    value: object

    def describe(self) -> str:
        return (f"check={self.check_codes} drops={self.drops} "
                f"loads={self.loads} value={self.value!r}")


def _verdict(source: str) -> Verdict:
    checked = vera_pipeline.check(source)
    codes = tuple(d.error_code for d in checked.errors)
    if codes:
        return Verdict(codes, (), False, None)
    result = vera_pipeline.compile(source).result
    drops = tuple(sorted(
        d.error_code or "uncoded" for d in result.diagnostics
        if (d.error_code or "").startswith("E6") or d.severity == "error"))
    if drops or "main" not in result.exports:
        return Verdict((), drops, False, None)
    try:
        ran = vera_pipeline.run(result, fn="main")
    except wasmtime.WasmtimeError as exc:
        return Verdict((), (), False, f"load: {exc}"[:120])
    return Verdict((), (), True, ran.value if ran.ok else "trap")


def _holds(source: str, refused: tuple[str, ...] | None,
           value: object, *, backend: bool = True) -> None:
    """THE invariant, for a cell whose rule gives *refused* (its codes) or
    *value*.  With *backend*, a refused cell is also refused by code
    generation past the check: the rule refuses only what does not lower."""
    verdict = _verdict(source)
    if refused is not None:
        assert verdict.check_codes == refused, (
            f"{verdict.describe()}\n{source}")
        if backend:
            assert _codegen_refuses(source), (
                f"refused at check, and code generation lowers it:\n"
                f"{source}")
        return
    assert verdict.loads and verdict.value == value, (
        f"{verdict.describe()}\n{source}")


def _main(body: str, *, eff: str = "pure") -> str:
    return (
        "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        f"  effects({eff})\n{{\n  {body}\n}}\n"
    )


# ---------------------------------------------------------------------
# Rule 1: the effect a handler handles (#1597)
# ---------------------------------------------------------------------

#: One clause per effect the registry lists with an operation, and a
#: user-declared effect: the operation, its clause, and the declaration the
#: program needs.  The registry is the enumeration
#: (`test_every_registry_effect_has_a_handler_row`), so an effect it gains
#: is a missing row here.
_HANDLED: dict[str, tuple[str, str, str]] = {
    # effect: (handler effect, clause, declarations)
    "State": ("State<Int>", "get(@Unit) -> { resume(@Int.0) },\n"
              "    put(@Int) -> { resume(()) }", ""),
    "Exn": ("Exn<Int>", "throw(@Int) -> { @Int.0 }", ""),
    "IO": ("IO", "print(@String) -> { resume(()) }", ""),
    "Http": ("Http", 'get(@String) -> { resume(Ok("m")) }', ""),
    "Inference": ("Inference", 'complete(@String) -> { resume(Ok("m")) }',
                  ""),
    "DB": ("DB", "execute(@String, @Array<Option<String>>) -> "
           "{ resume(Ok(0)) }", ""),
    "Random": ("Random", "random_int(@Int, @Int) -> { resume(4) }", ""),
    "Counter": ("Counter", "tick(@Unit) -> { resume(1) }",
                "effect Counter {\n  op tick(Unit -> Int);\n}\n\n"),
}

#: The registry's effects with no operation: a handler needs a clause (the
#: grammar's `handler_clause+`), so none can be written.  Not cells.
_NO_HANDLER_WRITABLE = frozenset({"Async", "Diverge", "HttpServer"})

#: Where the handler is written: a function body, a closure body (lifted
#: and compiled apart), and a `where` helper.
_HANDLER_PLACES = ("function", "closure", "where helper")


def _handler_source(effect: str, place: str) -> str:
    handled, clause, decls = _HANDLED[effect]
    body = ("put(5);\n    get(())" if effect == "State"
            else "if true then { throw(7) } else { 1 }" if effect == "Exn"
            else "7")
    handle = (f"handle[{handled}]" + ("(@Int = 0)" if effect == "State"
                                      else "")
              + f" {{\n    {clause}\n  }} in {{\n    {body}\n  }}")
    if place == "function":
        return decls + _main(handle)
    if place == "closure":
        return decls + (
            "type Thunk = fn(Unit -> Int) effects(pure);\n\n"
            + _main(f"let @Thunk = fn(@Unit -> @Int) effects(pure) "
                    f"{{ {handle} }};\n  apply_fn(@Thunk.0, ())"))
    return decls + (
        "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  run(())\n}\nwhere {\n"
        "  fn run(@Unit -> @Int)\n    requires(true)\n    ensures(true)\n"
        f"    effects(pure)\n  {{\n    {handle}\n  }}\n}}\n")


_HANDLER_CELLS = [
    pytest.param(effect, place, id=f"{effect}|{place}")
    for effect in _HANDLED for place in _HANDLER_PLACES
]


class TestHandlerEffect:
    """Rule 1: a handler lowers for `State` and `Exn` and no other effect."""

    def test_every_registry_effect_has_a_handler_row(self) -> None:
        registry = builtin_effect_names()
        assert registry - _NO_HANDLER_WRITABLE <= set(_HANDLED), sorted(
            registry - _NO_HANDLER_WRITABLE - set(_HANDLED))
        assert not _NO_HANDLER_WRITABLE - registry
        env = TypeEnv()
        for effect in _NO_HANDLER_WRITABLE:
            assert not env.effects[effect].operations, effect

    def test_an_effect_with_no_operation_has_no_handler_to_write(
        self,
    ) -> None:
        for effect in sorted(_NO_HANDLER_WRITABLE):
            parsed = vera_pipeline.parse(_main(
                f"handle[{effect}] {{\n  }} in {{\n    1\n  }}"))
            assert not parsed.ok, effect

    @pytest.mark.parametrize(("effect", "place"), _HANDLER_CELLS)
    def test_handler(self, effect: str, place: str) -> None:
        # The rule: State and Exn lower, every other effect is refused.
        lowers = effect in ("State", "Exn")
        _holds(_handler_source(effect, place),
               None if lowers else ("E340",),
               {"State": 5, "Exn": 7}.get(effect))


# ---------------------------------------------------------------------
# Rule 2: the State cell (#1512), in a handler and in a declared row
# ---------------------------------------------------------------------

#: Cell types across the representation classes: one word (a scalar, or a
#: pointer to the heap), a `(ptr, len)` pair, nothing at all.  Each is the
#: type, its declarations, an initial value, the value written, an
#: expression reading the cell back as an Int, and the rule's verdict: a
#: cell lowers when its value is one word.
_CELLS: dict[str, tuple[str, str, str, str, str, bool]] = {
    "Int": ("Int", "", "0", "5", "{v}", True),
    "Nat": ("Nat", "", "0", "5", "nat_to_int({v})", True),
    "Bool": ("Bool", "", "false", "true", "if {v} then { 5 } else { 0 }",
             True),
    "Float64": ("Float64", "", "0.0", "5.0", "float_to_int({v})", True),
    "Byte": ("Byte", "", "0", "5", "byte_to_int({v})", True),
    "Option<Int>": ("Option<Int>", "", "None", "Some(5)",
                    "match {v} { Some(@Int) -> @Int.0, None -> 0 }", True),
    "Tuple<Int, Int>": ("Tuple<Int, Int>", "", "Tuple(0, 0)",
                        "Tuple(2, 3)",
                        "match {v} { Tuple(@Int, @Int) -> @Int.0 + @Int.1 }",
                        True),
    "data": ("Colour", "private data Colour {\n  Red,\n  Green(Int)\n}\n\n",
             "Red", "Green(5)",
             "match {v} { Green(@Int) -> @Int.0, Red -> 0 }", True),
    # Read by its size: `map_get` straight on a `get(())` dispatches on an
    # inferred value type and finds nothing (#1686, another mechanism).
    "Map<String, Int>": (
        "Map<String, Int>", "", "map_new()",
        'map_insert(map_insert(map_insert(map_insert(map_insert(map_new(), '
        '"a", 1), "b", 2), "c", 3), "d", 4), "e", 5)',
        "map_size({v})", True),
    "data wrapper of String": (
        "Text", "private data Text {\n  T(String)\n}\n\n", 'T("")',
        'T("abcde")', "match {v} { T(@String) -> string_length(@String.0) }",
        True),
    "Future<Int>": ("Future<Int>", "", "async(0)", "async(5)",
                    "await({v})", True),
    "String": ("String", "", '""', '"abcde"', "string_length({v})", False),
    "Array<Int>": ("Array<Int>", "", "[0]", "[1, 2, 3, 4, 5]",
                   "array_length({v})", False),
    "Array<String>": ("Array<String>", "", '[""]', '["a", "b", "c", "d", "e"]',
                      "array_length({v})", False),
    "refinement of String": (
        "Short", "type Short = { @String | string_length(@String.0) < 9 };\n\n",
        '""', '"abcde"', "string_length({v})", False),
    "alias of String": ("Name", "type Name = String;\n\n", '""', '"abcde"',
                        "string_length({v})", False),
    "Unit": ("Unit", "", "()", "()", "5", False),
}

#: A cell whose program violates the invariant through another mechanism:
#: pinned, and flipped when that issue closes.  The row cell reads the
#: `Future` with no clause inlined, and runs.
_CELL_KNOWN = {
    ("Future<Int>", "handler"): "#1685: the clause inlining reads a Future "
                                "cell as a heap pointer, and the module does "
                                "not load",
}

#: Where the cell is written: a handler, and a declared row read under one.
_CELL_PLACES = ("handler", "row")


def _cell_source(name: str, place: str) -> str:
    ty, decls, init, written, read, _ = _CELLS[name]
    eff = "<Async>" if name == "Future<Int>" else "pure"
    # A zero-size state has no slot to read (E182), so a Unit get clause
    # resumes the one Unit value.
    state = "()" if ty == "Unit" else f"@{ty}.0"
    handler = (
        f"handle[State<{ty}>](@{ty} = {init}) {{\n"
        f"    get(@Unit) -> {{ resume({state}) }},\n"
        f"    put(@{ty}) -> {{ resume(()) }}\n"
        "  } in {\n    BODY\n  }")
    if place == "handler":
        return decls + _main(handler.replace(
            "BODY", f"put({written});\n    " + read.replace("{v}", "get(())")),
            eff=eff)
    row_eff = f"<State<{ty}>, Async>" if eff != "pure" else f"<State<{ty}>>"
    return decls + (
        "private fn cellf(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        f"  effects({row_eff})\n{{\n  put({written});\n  "
        + read.replace("{v}", "get(())") + "\n}\n\n"
        + _main(handler.replace("BODY", "cellf(())"), eff=eff))


def _cell_params() -> list[object]:
    params = []
    for name in _CELLS:
        for place in _CELL_PLACES:
            known = _CELL_KNOWN.get((name, place))
            marks = ([pytest.mark.xfail(strict=True, reason=known)]
                     if known else [])
            params.append(pytest.param(name, place, id=f"{name}|{place}",
                                       marks=marks))
    return params


class TestStateCell:
    """Rule 2: a `State` cell lowers when its value is one word."""

    @pytest.mark.parametrize(("name", "place"), _cell_params())
    def test_cell(self, name: str, place: str) -> None:
        lowers = _CELLS[name][5]
        # A row cell is read under a handler of the same cell, so a refused
        # type is refused at both.
        refused = None if lowers else (
            ("E340",) if place == "handler" else ("E340", "E340"))
        _holds(_cell_source(name, place), refused, 5)

    def test_the_cell_rule_spans_every_class(self) -> None:
        """Not vacuous: both verdicts occur, and each refused class (a pair,
        nothing) and each accepted class (scalar, pointer) has a row."""
        verdicts = {name: row[5] for name, row in _CELLS.items()}
        assert {"String", "Array<Int>", "Unit"} <= {
            n for n, ok in verdicts.items() if not ok}
        assert {"Int", "Option<Int>", "data wrapper of String"} <= {
            n for n, ok in verdicts.items() if ok}


# ---------------------------------------------------------------------
# Rule 2: the Exn payload, and the handler's spelling of either
# ---------------------------------------------------------------------

#: Payload types: a value with a representation is thrown, a pair included
#: (the tag takes two words); one with none is refused.
_PAYLOADS: dict[str, tuple[str, str, str, str, bool]] = {
    # name: (type, declarations, thrown, clause result over @T.0, lowers)
    "Int": ("Int", "", "7", "@Int.0", True),
    "Bool": ("Bool", "", "true", "if @Bool.0 then { 7 } else { 0 }", True),
    "String": ("String", "", '"abcdefg"', "string_length(@String.0)", True),
    "nullary data": ("Failure", "private data Failure {\n  Failed\n}\n\n",
                     "Failed", "7", True),
    "Option<Int>": ("Option<Int>", "", "Some(7)",
                    "match @Option<Int>.0 { Some(@Int) -> @Int.0, None -> 0 }",
                    True),
    "Unit": ("Unit", "", "()", "7", False),
}


def _payload_source(name: str, place: str) -> str:
    ty, decls, thrown, result, _ = _PAYLOADS[name]
    handler = (f"handle[Exn<{ty}>] {{\n    throw(@{ty}) -> {{ {result} }}\n"
               "  } in {\n    BODY\n  }")
    if place == "handler":
        return decls + _main(handler.replace(
            "BODY", f"if true then {{ throw({thrown}) }} else {{ 1 }}"))
    return decls + (
        "private fn boom(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        f"  effects(<Exn<{ty}>>)\n{{\n  throw({thrown})\n}}\n\n"
        + _main(handler.replace("BODY", "boom(())")))


class TestExnPayload:
    """Rule 2's twin: an `Exn` payload lowers when it has a value."""

    @pytest.mark.parametrize("place", _CELL_PLACES)
    @pytest.mark.parametrize("name", sorted(_PAYLOADS))
    def test_payload(self, name: str, place: str) -> None:
        lowers = _PAYLOADS[name][4]
        refused = None if lowers else (
            ("E340",) if place == "handler" else ("E340", "E340"))
        _holds(_payload_source(name, place), refused, 7)


_SMALL = "type Small = { @Nat | @Nat.0 < 10 };\n\n"
_SPELLINGS: dict[str, tuple[str, tuple[str, ...] | None]] = {
    # A handler keys its cell by a type name: an inline refinement has none.
    "State inline refinement": (_main(
        "handle[State<{ @Nat | @Nat.0 < 10 }>](@{ @Nat | @Nat.0 < 10 } = 5) "
        "{\n    put(@Nat) -> { resume(()) }\n  } in {\n    put(1);\n"
        "    nat_to_int(get(()))\n  }"), ("E340",)),
    "State alias of a refinement": (_SMALL + _main(
        "handle[State<Small>](@Small = 5) {\n    put(@Small) -> "
        "{ resume(()) }\n  } in {\n    put(1);\n    nat_to_int(get(()))\n  }"),
        None),
    "Exn inline refinement": (_main(
        "handle[Exn<{ @Nat | @Nat.0 < 10 }>] {\n    throw(@Nat) -> "
        "{ nat_to_int(@Nat.0) }\n  } in {\n    if true then { throw(1) } "
        "else { 0 }\n  }"), ("E340",)),
    "Exn alias of a refinement": (_SMALL + _main(
        "handle[Exn<Small>] {\n    throw(@Small) -> { nat_to_int(@Small.0) "
        "}\n  } in {\n    if true then { throw(1) } else { 0 }\n  }"), None),
    # A declared row's cell is registered from the row, which needs no name.
    "row inline refinement": (
        "private fn cellf(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
        "  effects(<State<{ @Int | @Int.0 >= 0 }>>)\n{\n  put(1);\n"
        "  get(())\n}\n\n" + _main("1"), None),
}


@pytest.mark.parametrize("name", sorted(_SPELLINGS))
def test_handler_cell_spelling(name: str) -> None:
    source, refused = _SPELLINGS[name]
    _holds(source, refused, 1)


# ---------------------------------------------------------------------
# Rule 2b: a State clause resumes once, as its last step
# ---------------------------------------------------------------------

#: Clause bodies over a `State<Int>` handler whose body performs both
#: operations, so each clause is reached, with the rule's verdict.
_CLAUSES: dict[str, tuple[str, str, bool]] = {
    # name: (get clause, put clause, lowers)
    "tail resume": ("resume(@Int.0)", "resume(())", True),
    "branch inside the argument": (
        "resume(if @Int.0 > 3 then { @Int.0 } else { 0 })", "resume(())",
        True),
    "single-arm match tail": ("match @Int.0 { _ -> resume(@Int.0) }",
                              "resume(())", True),
    "no resume": ("resume(@Int.0)", "()", False),
    "two resumes": ("resume(@Int.0)", "resume(());\n      resume(())", False),
    "a resume in each if arm": (
        "if @Int.0 > 3 then { resume(@Int.0) } else { resume(0) }",
        "resume(())", False),
    "a resume in each match arm": (
        "match @Int.0 { 0 -> resume(0), _ -> resume(@Int.0) }", "resume(())",
        False),
}


def _clause_source(get_clause: str, put_clause: str, *,
                   with_update: str = "", body: str = "") -> str:
    return _main(
        "handle[State<Int>](@Int = 0) {\n"
        f"    get(@Unit) -> {{ {get_clause} }},\n"
        f"    put(@Int) -> {{ {put_clause} }}{with_update}\n"
        "  } in {\n    " + (body or "put(5);\n    get(())") + "\n  }")


class TestStateClause:
    """Rule 2b, over the clause shapes and the `with` update."""

    @pytest.mark.parametrize("name", sorted(_CLAUSES))
    def test_clause(self, name: str) -> None:
        get_clause, put_clause, lowers = _CLAUSES[name]
        _holds(_clause_source(get_clause, put_clause),
               None if lowers else ("E340",), 5)

    def test_a_resume_in_the_with_update_is_refused(self) -> None:
        _holds(_clause_source("resume(@Int.0)", "resume(())",
                              with_update=" with @Int = { resume(());\n"
                                          "      @Int.0 }"),
               ("E340",), None)

    def test_a_with_update_without_resume_lowers(self) -> None:
        # The neighbour: the update replaces the store.
        _holds(_clause_source("resume(@Int.0)", "resume(())",
                              with_update=" with @Int = @Int.1 + 1"),
               None, 6)

    def test_an_unreached_clause_is_refused_too(self) -> None:
        """Conservative: the rule is the clause's, so a clause no operation
        reaches is refused like one that is reached, where code generation,
        which inlines a clause only where an operation reaches it, would
        have built the program."""
        source = _clause_source("resume(@Int.0)", "()", body="7")
        assert _verdict(source).check_codes == ("E340",)
        compiled = vera_pipeline.compile(source, past_check=True)
        assert vera_pipeline.run(compiled.result, fn="main").value == 7


# ---------------------------------------------------------------------
# Rule 3: a quantifier's predicate and bound (#1506) — E179, E128
# ---------------------------------------------------------------------

_QUANT_DECLS = (
    "private data Colour {\n  Red,\n  Green\n}\n\n"
    "type Idx = Nat;\n\n"
    "type Small = { @Nat | @Nat.0 < 2 };\n\n"
    "type Smaller = { @Small | @Small.0 < 1 };\n\n"
    "type Verdict = Bool;\n\n"
)

#: The predicate's parameter: the rule admits Int, Nat and an alias of
#: either; a refinement (inline, aliased, chained), another type, and a type
#: parameter are refused.
_PREDICATE_PARAMS: dict[str, bool] = {
    "Nat": True, "Int": True, "Idx": True,
    "{ @Nat | @Nat.0 < 100 }": False, "Small": False, "Smaller": False,
    "Bool": False, "String": False, "Colour": False, "T": False,
}
#: The predicate's result: Bool, a refinement of Bool or an alias of it.
_PREDICATE_RESULTS: dict[str, bool] = {
    "Bool": True, "{ @Bool | true }": True, "Verdict": True,
    "Int": False, "Nat": False, "T": False,
}
#: The bound: an Int or Nat count, a refinement of one; the parameter of
#: `q` it is read from, and the argument `main` passes.
_BOUNDS: dict[str, tuple[str, str, bool]] = {
    # name: (parameter type, argument, lowers)
    "Int": ("Int", "3", True),
    "Nat": ("Nat", "3", True),
    "refined Nat": ("Small", "1", True),
    "T": ("T", "true", False),
    "Bool": ("Bool", "true", False),
    "Float64": ("Float64", "3.0", False),
}


def _quant_source(param: str, result: str, *, bound: str = "3",
                  arity: int = 1) -> str:
    body = "true" if result in ("Bool", "{ @Bool | true }", "Verdict") else (
        "@T.0" if result == "T" else "5")
    params = ", ".join(f"@{param}" for _ in range(arity)) or ""
    pred = f"fn({params} -> @{result}) effects(pure) {{ {body} }}"
    quant = f"forall(@Nat, {bound}, {pred})"
    generic = "T" in (param, result) or bound == "@T.0"
    if generic:
        return _QUANT_DECLS + (
            "private forall<T> fn q(@T -> @Bool)\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{\n  {quant}\n}}\n\n"
            + _main("if q(true) then { 1 } else { 0 }"))
    return _QUANT_DECLS + _main(f"if {quant} then {{ 1 }} else {{ 0 }}")


class TestQuantifierSignature:
    """Rule 3: one Int or Nat parameter written as a type name, a Bool
    result, an integer bound — and a type parameter at none of them.

    E179 and E128 are the spec's signature rules (§6.3.3), wider than what
    the loop cannot build: a refinement parameter is bound and refused
    because the counter takes values it excludes, and a parameter the body
    never reads leaves nothing to fail.  So these cells assert the rule, and
    the backend half is the #1506 repros above, each a module that failed to
    load."""

    @pytest.mark.parametrize("param", sorted(_PREDICATE_PARAMS))
    def test_predicate_parameter(self, param: str) -> None:
        lowers = _PREDICATE_PARAMS[param]
        _holds(_quant_source(param, "Bool"),
               None if lowers else ("E179",), 1, backend=False)

    @pytest.mark.parametrize("result", sorted(_PREDICATE_RESULTS))
    def test_predicate_result(self, result: str) -> None:
        lowers = _PREDICATE_RESULTS[result]
        _holds(_quant_source("Nat", result), None if lowers else ("E179",),
               1, backend=False)

    @pytest.mark.parametrize("arity", (0, 2))
    def test_predicate_arity(self, arity: int) -> None:
        _holds(_quant_source("Nat", "Bool", arity=arity), ("E179",), None)

    @pytest.mark.parametrize("bound", sorted(_BOUNDS))
    def test_bound(self, bound: str) -> None:
        """A bound of each type, read from `q`'s parameter: the counter
        loop compares the bound as an i64, so every refused row is a module
        that does not load past the check."""
        param, arg, lowers = _BOUNDS[bound]
        forall = "forall<T> " if param == "T" else ""
        source = _QUANT_DECLS + (
            f"private {forall}fn q(@{param} -> @Bool)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n"
            f"  forall(@Nat, @{param}.0, fn(@Nat -> @Bool) effects(pure) "
            "{ true })\n}\n\n"
            + _main(f"if q({arg}) then {{ 1 }} else {{ 0 }}"))
        _holds(source, None if lowers else ("E128",), 1)

    def test_a_type_parameter_index_defers(self) -> None:
        """The neighbour of the refused type-parameter positions: the index
        lowers at every instantiation, so it is accepted and runs."""
        source = _QUANT_DECLS + (
            "private forall<T> fn q(@T -> @Bool)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n"
            "  forall(@T, 3, fn(@Nat -> @Bool) effects(pure) { true })\n}\n\n"
            + _main("if q(true) then { 1 } else { 0 }"))
        _holds(source, None, 1)


# ---------------------------------------------------------------------
# Rule 4: abilities (#1499)
# ---------------------------------------------------------------------

#: An ability, its declaration, and its operation applied to an Int value
#: `{x}`, as an Int.  The built-in four are the abilities the language
#: implements; `Sz` is user-declared, and nothing implements it.
_ABILITIES: dict[str, tuple[str, str]] = {
    "Sz": ("ability Sz<T> {\n  op size(T -> Int);\n}\n\n", "size({x})"),
    "Eq": ("", "if eq({x}, {x}) then { 1 } else { 0 }"),
    "Ord": ("", "match compare({x}, {x}) { Equal -> 1, _ -> 0 }"),
    "Hash": ("", "if hash({x}) == hash({x}) then { 1 } else { 0 }"),
    "Show": ("", "string_length(show({x}))"),
}
_ABILITY_OPS = {"Sz": "size", "Eq": "eq", "Ord": "compare", "Hash": "hash",
                "Show": "show"}

#: How the ability is used: its operation called bare at a concrete type,
#: qualified, through a `where` constraint in a generic body, and the
#: constraint alone.
_ABILITY_FORMS = ("bare", "qualified", "through a constraint",
                  "constraint alone")


def _ability_source(ability: str, form: str) -> str:
    decls, call = _ABILITIES[ability]
    if form == "bare":
        return decls + _main(call.replace("{x}", "1"))
    if form == "qualified":
        op = _ABILITY_OPS[ability]
        return decls + _main(call.replace("{x}", "1").replace(
            f"{op}(", f"{ability}.{op}(", 1))
    body = call.replace("{x}", "@T.0") if form == "through a constraint" \
        else "1"
    return decls + (
        f"private forall<T where {ability}<T>> fn f(@T -> @Int)\n"
        f"  requires(true)\n  ensures(true)\n  effects(pure)\n{{\n"
        f"  {body}\n}}\n\n" + _main("f(1)"))


def _ability_refusal(ability: str, form: str) -> tuple[str, ...] | None:
    """The rule: a user ability is refused in every form (at the constraint
    and the call, both, where both are written); a built-in one only when
    qualified, since an ability's operation is called bare."""
    if ability == "Sz":
        return ("E340", "E340") if form == "through a constraint" else (
            "E340",)
    return ("E340",) if form == "qualified" else None


class TestAbility:
    """Rule 4, over every form of use, for a user ability and the four
    built-in ones."""

    @pytest.mark.parametrize("form", _ABILITY_FORMS)
    @pytest.mark.parametrize("ability", sorted(_ABILITIES))
    def test_ability(self, ability: str, form: str) -> None:
        refused = _ability_refusal(ability, form)
        # A qualified call was E220 before, and never reached code
        # generation, so its refusal is the check's alone.
        _holds(_ability_source(ability, form), refused, 1,
               backend=form != "qualified")


# ---------------------------------------------------------------------
# Rule 5: a clause-body operation under a type-parameter cell (#1522)
# ---------------------------------------------------------------------

#: Outer and inner cell types, in a generic over T (and U), with an initial
#: value and a value written for each.  The rule: the operation is refused
#: where the two cells are, or at some instantiation become, one family.
_NEST_TYPES: dict[str, tuple[str, str]] = {
    "Int": ("0", "1"), "Nat": ("0", "1"), "T": ("@T.0", "@T.0"),
    "U": ("@U.0", "@U.0"), "Option<T>": ("None", "Some(@T.0)"),
    "Option<Int>": ("None", "Some(1)"),
}
_NESTINGS: dict[tuple[str, str], bool] = {
    # (outer, inner): may the two be one family?
    ("Int", "T"): True, ("T", "Int"): True, ("T", "T"): True,
    ("T", "U"): True, ("Option<T>", "Option<Int>"): True,
    ("Int", "Nat"): False, ("Option<T>", "Int"): False,
}
#: Where the operation is: in the inner clause's body (it means the OUTER
#: cell, through the inner one), nowhere, or in the inner handled body
#: (where it means the inner cell).
_OP_PLACES = ("clause body", "no operation", "handled body")


def _nest_source(outer: str, inner: str, op_place: str, at: str) -> str:
    o_init, o_value = _NEST_TYPES[outer]
    i_init, i_value = _NEST_TYPES[inner]
    two = "U" in (outer, inner)
    clause = (f"put({o_value});\n        resume(())"
              if op_place == "clause body" else "resume(())")
    body = (f"put({i_value});\n      1" if op_place != "no operation"
            else "1")
    forall = "forall<T, U>" if two else "forall<T>"
    params = "@T, @U -> @Int" if two else "@T -> @Int"
    call = f"g({at}, {at})" if two else f"g({at})"
    return (
        f"private {forall} fn g({params})\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n"
        f"  handle[State<{outer}>](@{outer} = {o_init}) {{\n"
        f"    get(@Unit) -> {{ resume(@{outer}.0) }},\n"
        f"    put(@{outer}) -> {{ resume(()) }}\n"
        "  } in {\n"
        f"    handle[State<{inner}>](@{inner} = {i_init}) {{\n"
        f"      get(@Unit) -> {{ resume(@{inner}.0) }},\n"
        f"      put(@{inner}) -> {{ {clause} }}\n"
        "    } in {\n"
        f"      {body}\n"
        "    }\n  }\n}\n\n" + _main(call))


_NEST_CELLS = [
    pytest.param(outer, inner, op_place, at,
                 id=f"{outer}/{inner}|{op_place}|T={at}")
    for (outer, inner) in _NESTINGS for op_place in _OP_PLACES
    for at in ("5", "true")
]


def _one_family_at(outer: str, inner: str, at: str) -> bool:
    """Whether the instantiation `main` makes, `g(at)` (or `g(at, at)`),
    turns the two cells into one family: at `T = Int` every pair that may
    coincide does, and at `T = Bool` the two whose cells are both named by
    type parameters (`T`/`T`, and `T`/`U` with both bound to `Bool`)."""
    if at == "5":
        return _NESTINGS[(outer, inner)]
    return (outer, inner) in (("T", "T"), ("T", "U"))


class TestGenericCellNesting:
    """Rule 5: E339 treats a cell named by a type parameter as able to be
    any family it unifies with.  Conservative: past the check, code
    generation refuses the refused cells whose instantiation makes the two
    cells one family, and builds and runs the others (`g(true)` over
    `Int`/`T`, which ran at the base), and both kinds occur."""

    @pytest.mark.parametrize(("outer", "inner", "op_place", "at"),
                             _NEST_CELLS)
    def test_nesting(self, outer: str, inner: str, op_place: str,
                     at: str) -> None:
        refused = (_NESTINGS[(outer, inner)]
                   and op_place == "clause body")
        source = _nest_source(outer, inner, op_place, at)
        if not refused:
            _holds(source, None, 1)
            return
        verdict = _verdict(source)
        assert verdict.check_codes == ("E339",), verdict.describe()
        if _one_family_at(outer, inner, at):
            assert _codegen_refuses(source), source
        else:
            past = vera_pipeline.compile(source, past_check=True).result
            assert vera_pipeline.run(past, fn="main").value == 1, source

    def test_both_kinds_of_refusal_occur(self) -> None:
        """Not vacuous: among the refused cells, some instantiations make the
        cells one family and some do not."""
        refused = [(o, i, at) for (o, i, op, at) in (
            c.values for c in _NEST_CELLS)
            if _NESTINGS[(o, i)] and op == "clause body"]
        kinds = {_one_family_at(o, i, at) for o, i, at in refused}
        assert kinds == {True, False}, refused

    def test_the_issue_instance_is_refused_at_both_instantiations(
        self,
    ) -> None:
        """#1522's report: at T = Int code generation dropped the clone; at
        T = Bool the program ran.  Both are refused now, and past the check
        the Int clone is still the one code generation cannot build."""
        for at in ("5", "true"):
            source = _nest_source("Int", "T", "clause body", at)
            assert _verdict(source).check_codes == ("E339",), at
        assert _codegen_refuses(_nest_source("Int", "T", "clause body", "5"))


# =====================================================================
# Every refusal's fix compiles clean
# =====================================================================
#
# Each test reads the refusal's `fix` from the live diagnostic, applies the
# rewrite the fix names to the program it refused, and holds the result to
# the invariant's accepted half: it checks clean, compiles, loads and runs.
# Where the fix carries the code to write, the code is taken out of the fix
# text itself.


def _only_fix(source: str, code: str) -> str:
    """The fix of *source*'s one error, which carries *code*."""
    errors = vera_pipeline.check(source).errors
    assert [d.error_code for d in errors] == [code], [
        (d.error_code, d.description) for d in errors]
    return errors[0].fix


def _between(text: str, start: str, end: str) -> str:
    """The span of *text* from *start* up to (not including) *end*."""
    i = text.index(start)
    return text[i:text.index(end, i)]


class TestTheFixCompilesClean:
    """COMMON.md's rule for a new diagnostic, over every message E340 has,
    and the type-parameter messages this PR gives E339, E179 and E128."""

    def test_handler_for_a_host_effect(self) -> None:
        fix = _only_fix(_REPRO_1597, "E340")
        assert "a function that returns Ok(\"mock\")" in fix, fix
        fixed = _REPRO_1597.replace(
            """  handle[Http] {
    get(@String) -> { resume(Ok("mock")) },
    post(@String, @String) -> { resume(Ok("mock")) }
  } in {
    fetch(@String.0)
  }""", "  mock_get(@String.0)") + (
            "\nprivate fn mock_get(@String -> @Result<String, String>)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            '  Ok("mock")\n}\n')
        _holds(fixed, None, 4)

    def test_handler_for_a_user_effect(self) -> None:
        source = _handler_source("Counter", "function")
        fix = _only_fix(source, "E340")
        alias = _between(fix, "type Op", ";") + ";\n\n"
        assert "apply_fn(@Op.0, ())" in fix, fix
        fixed = alias + (
            "private fn run(@Op -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{\n  apply_fn(@Op.0, ())\n}\n\n"
            + _main("run(fn(@Unit -> @Int) effects(pure) { 7 })"))
        _holds(fixed, None, 7)

    @pytest.mark.parametrize("name", ("String", "Array<Int>"))
    def test_a_pair_cell(self, name: str) -> None:
        source = _cell_source(name, "handler")
        fix = _only_fix(source, "E340")
        decl = _between(fix, "private data", "}") + "}\n\n"
        box = decl.split()[2]
        ctor = decl.split("{")[1].split("(")[0].strip()
        assert f"State<{box}>" in fix and f"{ctor}(@{name})" in fix, fix
        ty, _decls, init, written, read, _ = _CELLS[name]
        fixed = decl + _main(
            f"handle[State<{box}>](@{box} = {ctor}({init})) {{\n"
            f"    get(@Unit) -> {{ resume(@{box}.0) }},\n"
            f"    put(@{box}) -> {{ resume(()) }}\n"
            f"  }} in {{\n    put({ctor}({written}));\n"
            f"    match get(()) {{\n      {ctor}(@{ty}) -> "
            + read.replace("{v}", f"@{ty}.0") + "\n    }\n  }")
        _holds(fixed, None, 5)

    def test_a_cell_with_no_representation(self) -> None:
        fix = _only_fix(_cell_source("Unit", "handler"), "E340")
        assert "State<Bool>" in fix, fix
        _holds(_cell_source("Bool", "handler"), None, 5)

    def test_an_inline_refinement_cell(self) -> None:
        source, _ = _SPELLINGS["State inline refinement"]
        fix = _only_fix(source, "E340")
        alias = _between(fix, "type Small", ";") + ";\n\n"
        assert "handle[State<Small>]" in fix, fix
        fixed = alias + source.replace(
            "{ @Nat | @Nat.0 < 10 }", "Small").replace(
            "put(@Nat)", "put(@Small)")
        _holds(fixed, None, 1)

    def test_an_exn_payload_with_no_representation(self) -> None:
        fix = _only_fix(_payload_source("Unit", "handler"), "E340")
        decl = _between(fix, "private data Failure", "}") + "}\n\n"
        assert "throw(Failed)" in fix, fix
        fixed = decl + _main(
            "handle[Exn<Failure>] {\n    throw(@Failure) -> { 7 }\n"
            "  } in {\n    if true then { throw(Failed) } else { 1 }\n  }")
        _holds(fixed, None, 7)

    def test_a_clause_without_a_single_tail_resume(self) -> None:
        get_clause, put_clause, _ = _CLAUSES["a resume in each if arm"]
        fix = _only_fix(_clause_source(get_clause, put_clause), "E340")
        assert "resume(if " in fix, fix
        _holds(_clause_source(
            "resume(if @Int.0 > 3 then { @Int.0 } else { 0 })", put_clause),
            None, 5)

    def test_a_resume_in_the_with_update(self) -> None:
        source = _clause_source(
            "resume(@Int.0)", "resume(())",
            with_update=" with @Int = { resume(());\n      @Int.0 }")
        fix = _only_fix(source, "E340")
        assert "free of resume" in fix, fix
        # In the update `@Int.1` is the value written, `@Int.0` the state
        # before it.
        _holds(_clause_source("resume(@Int.0)", "resume(())",
                              with_update=" with @Int = @Int.1"),
               None, 5)

    def test_a_qualified_ability_call(self) -> None:
        fix = _only_fix(_REPRO_1499_QUALIFIED, "E340")
        bare = fix.removeprefix("Call it bare: ").removesuffix(".")
        _holds(_REPRO_1499_QUALIFIED.replace("Eq.eq(1, 1)", bare), None, 1)

    def test_a_user_ability_operation_call(self) -> None:
        fix = _only_fix(_REPRO_1499_BARE, "E340")
        assert "private fn size_of(...)" in fix, fix
        fixed = _REPRO_1499_BARE.replace("size(1)", "size_of(1)") + (
            "\nprivate fn size_of(@Int -> @Int)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n  @Int.0\n}\n")
        _holds(fixed, None, 1)

    def test_a_user_ability_constraint(self) -> None:
        fix = _only_fix(_REPRO_1499_CONSTRAINT_ONLY, "E340")
        alias = _between(fix, "type SzOp<T>", ";") + ";\n\n"
        call = _between(fix, "apply_fn(", ")") + "@T.0)"
        fixed = alias + (
            "public forall<T> fn measure(@T, @SzOp<T> -> @Int)\n"
            "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
            f"  {call.replace('...', '')}\n}}\n\n"
            + _main("measure(1, fn(@Int -> @Int) effects(pure) { @Int.0 })"))
        _holds(fixed, None, 1)

    def test_a_generic_cell_nested_in_one_it_can_be(self) -> None:
        errors = vera_pipeline.check(_REPRO_1522).errors
        assert [d.error_code for d in errors] == ["E339"]
        assert "a concrete State type" in errors[0].fix, errors[0].fix
        _holds(_nest_source("Int", "Nat", "clause body", "5"), None, 1)

    def test_a_type_parameter_predicate_parameter(self) -> None:
        fix = _only_fix(_REPRO_1506_PARAMETER, "E179")
        assert "fn(@Nat -> @Bool)" in fix, fix
        fixed = _REPRO_1506_PARAMETER.replace(
            "fn(@T -> @Bool) effects(pure) { let @T = keep(@T.0);\n    true }",
            "fn(@Nat -> @Bool) effects(pure) { true }").replace(_KEEP, "")
        _holds(fixed, None, 1)

    def test_a_type_parameter_bound(self) -> None:
        fix = _only_fix(_REPRO_1506_BOUND, "E128")
        assert "@Int or @Nat in place of @T" in fix, fix
        fixed = _REPRO_1506_BOUND.replace(
            "private forall<T> fn q(@T -> @Bool)", "private fn q(@Nat -> @Bool)"
        ).replace("@T.0, fn", "@Nat.0, fn").replace("q(true)", "q(3)"
        ).replace(_KEEP, "")
        _holds(fixed, None, 1)
