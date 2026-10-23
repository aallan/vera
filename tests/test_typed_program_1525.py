"""One typed program: the type-level members of #1525 (ROADMAP Stage 26).

Code generation and the verifier each derived the types and instantiations
the checker already had, and the derivations disagreed: a function dropped
at compile, a module that does not validate, a clone verified that is never
emitted, a wrong value.  The typed program removes the second derivation:
monomorphisation runs once, before verify and compile, and every node of
every clone carries the type the checker gave it, so a later phase reads a
type and derives none.

The ``repro`` cells are the checklist lines of #1525, each the program its
issue or comment reports, asserting the outcome the typed program gives.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/typed.py",
    "vera/monomorphize.py",
    "vera/codegen/monomorphize.py",
    "vera/codegen/core.py",
    "vera/wasm/inference.py",
    "vera/wasm/calls.py",
    "vera/wasm/calls_arrays.py",
    "vera/wasm/calls_containers.py",
    "vera/wasm/calls_handlers.py",
    "vera/wasm/data.py",
    "vera/wasm/operators.py",
    "vera/verifier.py",
    "vera/smt.py",
    "vera/checker/core.py",
    "vera/checker/expressions.py",
    "vera/checker/calls.py",
])


_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


@dataclass(frozen=True)
class Repro:
    """One checklist line: its program and the outcome it must have."""

    files: dict[str, str]
    expect: Callable[[Path], None]


def _source(*parts: str) -> str:
    return "\n".join(part.strip("\n") + "\n" for part in parts)


_UNSET = object()


def _runs(fn: str, args: list[int] | None, value: object = _UNSET, *,
          stdout: str | None = None) -> Callable[[Path], None]:
    """The program checks, verifies, compiles, and *fn* returns *value* or
    prints *stdout*."""
    def expect(path: Path) -> None:
        verified = pipeline.verify(path)
        assert verified.ok, [d.format() for d in verified.diagnostics]
        ran = pipeline.run(path, fn, args or [])
        assert ran.ok, ran.stderr
        if stdout is not None:
            assert ran.stdout == stdout, ran.stdout
        if value is not _UNSET:
            assert ran.value == value, ran.value
    return expect


def _verifies(check: Callable[[pipeline.Verified], None] | None = None,
              ) -> Callable[[Path], None]:
    def expect(path: Path) -> None:
        verified = pipeline.verify(path)
        assert verified.ok, [d.format() for d in verified.diagnostics]
        if check is not None:
            check(verified)
    return expect


def _verify_refuses(code: str, text: str = "") -> Callable[[Path], None]:
    def expect(path: Path) -> None:
        verified = pipeline.verify(path)
        found = [d for d in verified.errors if d.error_code == code]
        assert found, [d.format() for d in verified.diagnostics]
        if text:
            assert any(text in d.description for d in found), [
                d.description for d in found]
    return expect


# ---------------------------------------------------------------------
# The numbered lines (each a closed issue's repro)
# ---------------------------------------------------------------------

_I1514_LET = _source(
    "type Id<T> = T;",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  let @Id<Nat> = 5;\n"
    "  nat_to_int(@Id<Nat>.0)\n}",
)
_I1514_SILENT = _source(
    "type Opt<A> = Option<A>;",
    "type Count = Nat;",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  let @Opt<Int> = Some(4);\n"
    "  option_unwrap_or(@Opt<Int>.0, 0)\n}",
)
_I1514_BINDER = _source(
    "type Id<T> = T;",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  match Some(5) {\n    Some(@Id<Nat>) -> nat_to_int(@Id<Nat>.0),\n"
    "    None -> 0\n  }\n}",
)
_IDG = "private forall<T> fn idg(@T -> @T)\n" + _C + "{\n  @T.0\n}"
_I1515 = _source(
    _IDG,
    "public fn main(@Unit -> @Int)\n" + _C
    + "{\n  idg(result_unwrap_or(Ok(3), 0))\n}",
)
_I1516 = _source(
    "private fn mk(@Int -> @fn(Int -> Int) effects(pure))\n" + _C
    + "{\n  fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }\n}",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  apply_fn(mk(0), 41)\n}",
)
_I1516_CELL = _source(
    "type F = fn(Int -> Int) effects(pure);",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  handle[State<F>](@F = fn(@Int -> @Int) effects(pure) { @Int.0 }) {\n"
    "    get(@Unit) -> { resume(@F.0) },\n"
    "    put(@F) -> { resume(()) }\n"
    "  } in {\n"
    "    put(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 });\n"
    "    apply_fn(get(()), 4)\n"
    "  }\n}",
)
_I1550_MB = _source(
    "module mb;",
    "public data Box<T> {\n  MkBox(T)\n}",
    "public fn boxed(@Int -> @Box<Int>)\n" + _C + "{\n  MkBox(@Int.0)\n}",
)
_I1550_MAIN = _source(
    "import mb(boxed, Box);",
    "public fn main(@Unit -> @String)\n" + _C
    + "{\n  show(option_unwrap_or(Some(boxed(5)), boxed(5)))\n}",
)
_I1550_ONE = _source(
    "private data Box<T> {\n  MkBox(T)\n}",
    "public fn main(@Unit -> @String)\n" + _C
    + "{\n  show(option_unwrap_or(Some(MkBox(5)), MkBox(6)))\n}",
)
_I1555 = _source(
    "private data Duo<A, B> {\n  MkDuo(A, B)\n}",
    "private fn duo(@Int -> @Duo<Int, Int>)\n  requires(true)\n"
    "  ensures(@Duo<Int, Int>.result == MkDuo(@Int.0, 3))\n  effects(pure)\n"
    "{\n  MkDuo(@Int.0, 3)\n}",
    "private fn same(@Int -> @Bool)\n  requires(true)\n"
    "  ensures(@Bool.result)\n  effects(pure)\n"
    "{\n  duo(@Int.0) == duo(@Int.0)\n}",
    "public fn main(@Unit -> @Bool)\n" + _C + "{\n  same(7)\n}",
)
_I1555_OPTION = _source(
    "private fn mo(@Int -> @Option<Int>)\n" + _C + "{\n  Some(@Int.0)\n}",
    "public fn main(@Unit -> @Bool)\n" + _C + "{\n  mo(7) == mo(7)\n}",
)
_I1564 = _source(
    "public fn main(@Unit -> @Bool)\n" + _C + "{\n  [true][0]\n}",
)
_I1564_GENERIC = _source(
    "private forall<T> fn id(@T -> @T)\n" + _C + "{\n  @T.0\n}",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  id([4, 5])[1]\n}",
)
_I1572_MB = _source(
    "module mb;",
    "public forall<T> fn gen(@T -> @T)\n  requires(true)\n  ensures(false)\n"
    "  effects(pure)\n{\n  @T.0\n}",
)
_I1572_MA = _source(
    "module ma;",
    "import mb(gen);",
    "public fn four(@Int -> @Int)\n  requires(true)\n"
    "  ensures(@Int.result == 0)\n  effects(pure)\n{\n  mb::gen(@Int.0) * 4\n}",
)
_I1572_MAIN = _source(
    "import ma(four);",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  four(3)\n}",
)
_I1575_MA = _source(
    "module ma;",
    "private forall<T> fn pg2(@T -> @T)\n" + _C + "{\n  @T.0\n}",
    "public forall<T> fn pub_g(@T -> @T)\n" + _C + "{\n  pg2(@T.0)\n}",
    "private forall<T> fn pg(@T -> @T)\n" + _C + "{\n  pub_g(@T.0)\n}",
    "public fn four(@Int -> @Int)\n" + _C + "{\n  pg(@Int.0) * 4\n}",
)
_I1575_MAIN = _source(
    "import ma(four, pub_g);",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  four(3)\n}",
)
_I1578 = _source(
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  match array_fold([1, 2], 0, fn(@Int, @Int -> @Int) effects(pure) "
    "{ @Int.1 + @Int.0 }) {\n    @Int -> @Int.0\n  }\n}",
)
_I1609 = _source(
    "private fn get_b(@Byte -> @Byte)\n" + _C + "{\n  @Byte.0\n}",
    "public fn classify(@Byte -> @Int)\n" + _C + "{\n"
    "  match get_b(@Byte.0) {\n    65 -> 1,\n    _ -> 0\n  }\n}",
)
_I1638_MB = _source(
    "module mb;",
    "private forall<T> fn mid(@T -> @T)\n" + _C + "{\n  @T.0\n}",
    "public fn run(@Int -> @Int)\n" + _C
    + "{\n  if @Int.0 > 0 then { mid(@Int.0) } else { mid(0) }\n}",
)
_I1638_MAIN = _source(
    "import mb(run);",
    "public fn f(@Int -> @Int)\n" + _C + "{\n  run(@Int.0)\n}",
)
_I1686 = _source(
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  handle[State<Map<String, Int>>](@Map<String, Int> = map_new()) {\n"
    "    get(@Unit) -> { resume(@Map<String, Int>.0) },\n"
    "    put(@Map<String, Int>) -> { resume(()) }\n"
    "  } in {\n"
    "    put(map_insert(map_new(), \"k\", 5));\n"
    "    match map_get(get(()), \"k\") {\n"
    "      Some(@Int) -> @Int.0,\n"
    "      None -> 0\n"
    "    }\n"
    "  }\n}",
)
_I1730 = _source(
    "private fn b(@Byte -> @Byte)\n  requires(true)\n"
    "  ensures(@Byte.result == @Byte.0)\n  effects(pure)\n{\n  @Byte.0\n}",
    "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
    "  effects(<IO>)\n{\n"
    "  let @Array<Byte> = [b(7), b(200), b(255), b(3)];\n"
    "  IO.print(match array_find(@Array<Byte>.0, fn(@Byte -> @Bool) "
    "effects(pure) { byte_to_int(@Byte.0) > 200 }) {\n"
    "    Some(@Byte) -> int_to_string(byte_to_int(@Byte.0)),\n"
    "    None -> \"not found\"\n  });\n"
    "  IO.print(\" \");\n"
    "  let @Array<Bool> = [false, true, false];\n"
    "  IO.print(match array_find(@Array<Bool>.0, fn(@Bool -> @Bool) "
    "effects(pure) { @Bool.0 }) {\n"
    "    Some(@Bool) -> bool_to_string(@Bool.0),\n"
    "    None -> \"not found\"\n  });\n"
    "  IO.print(\" \");\n"
    "  let @Array<Option<Int>> = [None, Some(5)];\n"
    "  IO.print(match array_find(@Array<Option<Int>>.0, "
    "fn(@Option<Int> -> @Bool) effects(pure) {\n"
    "    match @Option<Int>.0 { Some(@Int) -> true, None -> false }\n"
    "  }) {\n"
    "    Some(@Option<Int>) -> match @Option<Int>.0 { Some(@Int) -> "
    "int_to_string(@Int.0), None -> \"none\" },\n"
    "    None -> \"not found\"\n  });\n"
    "  IO.print(\"\\n\")\n}",
)
_I1730_WIDE = _source(
    "private data Point {\n  Point(Int, Int)\n}",
    "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
    "  effects(<IO>)\n{\n"
    "  let @Array<Point> = [Point(1, 2), Point(3, 4)];\n"
    "  IO.print(match array_find(@Array<Point>.0, fn(@Point -> @Bool) "
    "effects(pure) { match @Point.0 { Point(@Int, @Int) -> @Int.1 == 3 } }) {\n"
    "    Some(@Point) -> match @Point.0 { Point(@Int, @Int) -> "
    "int_to_string(@Int.1 * 10 + @Int.0) },\n"
    "    None -> \"not found\"\n  });\n"
    "  IO.print(\" \");\n"
    "  let @Array<String> = [\"a\", \"bc\"];\n"
    "  IO.print(match array_find(@Array<String>.0, fn(@String -> @Bool) "
    "effects(pure) { string_length(@String.0) == 2 }) {\n"
    "    Some(@String) -> @String.0,\n"
    "    None -> \"not found\"\n  });\n"
    "  IO.print(\"\\n\")\n}",
)
_I1594 = _source(
    "public fn f(@Nat -> @Tuple<Int, Int>)\n" + _C + "{\n"
    "  let @Option<Tuple<Int, Int>> = Some(Tuple(@Nat.0, @Nat.0));\n"
    "  match @Option<Tuple<Int, Int>>.0 {\n"
    "    Some(@Tuple<Int, Int>) -> @Tuple<Int, Int>.0,\n"
    "    None -> Tuple(1, 1)\n  }\n}",
)
_I1767 = _source(
    "private fn foo(@Int, @Int -> @Int)\n"
    "  requires(@Int.1 == 3 && @Int.0 == 4)\n"
    "  ensures(@Int.result < 0)\n  effects(pure)\n{\n  @Int.1 + 10\n}",
)


def _counterexample_in_source_order(verified: pipeline.Verified) -> None:
    found = [d for d in verified.errors if d.error_code == "E500"]
    assert found, [d.format() for d in verified.diagnostics]
    text = found[0].description
    assert re.search(r"@Int\.1 = 3\b", text), text
    assert re.search(r"@Int\.0 = 4\b", text), text


def _same_clones_verified_and_compiled(path: Path) -> None:
    """The clones the verifier verifies are the clones the module holds."""
    from vera.verifier import ContractVerifier

    checked = pipeline.check(path)
    assert checked.ok, [d.format() for d in checked.diagnostics]
    compiled = pipeline.compile(path)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    emitted = {
        name for name in re.findall(r"\(func \$:([^\s()]+)", compiled.wat)
        if "$" in name and "$where$" not in name and not name.startswith("mod$ma$bar")
    }
    verifier = ContractVerifier(
        checked.typed, source=checked.source, file=checked.file)
    verifier.register_program(checked.program)
    from vera.monomorphize import Monomorphizer
    verified = {
        Monomorphizer._mangle_fn_name(name, types)
        for name, cts in verifier._instances.items() for types in cts
    }
    assert verified == emitted, (verified, emitted)


_I1551_MA = _source(
    "module ma;",
    "private forall<T> fn idm(@T -> @T)\n" + _C + "{\n  @T.0\n}",
    "public fn bar(@Int -> @Int)\n" + _C
    + "{\n  if idm(foo(@Int.0)) then { 1 } else { 2 }\n}\nwhere {\n"
    "  fn foo(@Int -> @Bool)\n    requires(true)\n    ensures(true)\n"
    "    effects(pure)\n  {\n    @Int.0 > 0\n  }\n}",
)
_I1551_MAIN = _source(
    "import ma(bar);",
    "private forall<T> fn foo(@T -> @T)\n" + _C + "{\n  @T.0\n}",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  bar(1) + foo(0)\n}",
)


# ---------------------------------------------------------------------
# The unnumbered lines (14, 21 and 22 October)
# ---------------------------------------------------------------------

_NEG_NAT_INTERPOLATION = _source(
    "public fn show_neg(@Nat -> @String)\n" + _C
    + "{\n  \"\\(-@Nat.0)\"\n}",
)
_SORTS = _source(
    "public data Gauge {\n  Bravo(Int)\n}",
    "private fn four(@Gauge -> @Nat)\n  requires(true)\n"
    "  ensures(@Nat.result == 4)\n  effects(pure)\n{\n  4\n}",
    "private fn pos(@Int -> @Int)\n  requires(@Int.0 > 0)\n  ensures(true)\n"
    "  effects(pure)\n{\n  @Int.0\n}",
    "public fn lost(@Int -> @Nat)\n  requires(true)\n"
    "  ensures(@Nat.result == 4)\n  effects(pure)\n{\n  four(Bravo(@Int.0))\n}",
    "public fn refused(@Int -> @Int)\n" + _C
    + "{\n  let @Int = four(Bravo(@Int.0));\n  pos(@Int.0)\n}",
    "public fn named_in_let(@Int -> @Int)\n" + _C
    + "{\n  let @Gauge = Bravo(1);\n  let @Int = four(Bravo(@Int.0));\n"
    "  pos(@Int.0)\n}",
)


def _every_obligation_tier1(verified: pipeline.Verified) -> None:
    statuses = {(o.fn_name, o.kind.value if hasattr(o.kind, "value") else o.kind,
                 o.status.value if hasattr(o.status, "value") else o.status)
                for o in verified.obligations}
    assert all(status == "verified" for _f, _k, status in statuses), sorted(statuses)


_INTERPOLATION_CONVERTER = _source(
    "private fn byte_id(@Byte -> @Byte)\n" + _C + "{\n  @Byte.0\n}",
    "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
    "  effects(<IO>)\n{\n"
    "  IO.print(\"call \\(byte_id(65))\\n\");\n"
    "  let @Byte = byte_id(65);\n"
    "  IO.print(\"bound \\(@Byte.0)\\n\")\n}",
)
_ALIAS_WIDTH = _source(
    "type W<T> = String;",
    "private fn first(@W<Int> -> @Int)\n" + _C
    + "{\n  nat_to_int(string_length(@W<Int>.0)) + 39\n}",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  first(\"abc\")\n}",
)
_ALIAS_WIDTH_LET = _source(
    "type Wrap<T> = Array<T>;",
    "public fn main(@Unit -> @Int)\n" + _C
    + "{\n  let @Wrap<Int> = [41];\n  @Wrap<Int>.0[0] + 1\n}",
)


# ---------------------------------------------------------------------
# The lines #1679 reported that are a re-derived type (routed to #1525)
# ---------------------------------------------------------------------

_FUTURE_CELL = _source(
    "public fn main(@Unit -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(<Async>)\n{\n"
    "  handle[State<Future<Int>>](@Future<Int> = async(0)) {\n"
    "    get(@Unit) -> { resume(@Future<Int>.0) },\n"
    "    put(@Future<Int>) -> { resume(()) }\n"
    "  } in {\n    put(async(5));\n    1\n  }\n}",
)
_WRAP_INDEX = _source(
    "private forall<T> fn wrap(@T -> @Array<T>)\n" + _C + "{\n  [@T.0]\n}",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n  wrap(3)[0]\n}",
)
_SHOW_REVERSE = _source(
    "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
    "  effects(<IO>)\n{\n"
    "  let @Array<Int> = array_reverse(array_range(1, 4));\n"
    '  IO.print("\\(show(@Array<Int>.0))\\n");\n'
    '  IO.print("\\(show(array_reverse(array_range(1, 4))))\\n")\n}',
)
_MATCH_FOLD = _source(
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  match array_fold([Some(1), None], 0, fn(@Int, @Option<Int> -> @Int) "
    "effects(pure) { @Int.0 }) {\n    0 -> 1,\n    _ -> 2\n  }\n}",
)


# ---------------------------------------------------------------------
# The lines of 22 and 23 October: the generator's, the reviews', and the
# ones routed here from #1680
# ---------------------------------------------------------------------

_IF_THROW_FOLD = _source(
    "public fn throw_fold(@Bool -> @Int)\n" + _C + "{\n"
    "  let @Array<Int> = [0, 1, 8];\n"
    "  handle[Exn<Int>] {\n    throw(@Int) -> { 2 }\n  } in {\n"
    "    if @Bool.0 then {\n      throw(1)\n    } else {\n"
    "      array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) "
    "{ @Int.1 + @Int.0 })\n    }\n  }\n}",
)
_IF_TWO_CELLS = _source(
    "public fn one_cell(@Bool -> @Int)\n" + _C + "{\n"
    "  if @Bool.0 then {\n"
    "    handle[State<Int>](@Int = 0) {\n"
    "      get(@Unit) -> { resume(@Int.0) },\n"
    "      put(@Int) -> { resume(()) }\n"
    "    } in {\n      put(3);\n      get(())\n    }\n"
    "  } else {\n"
    "    handle[State<Int>](@Int = -2) {\n"
    "      get(@Unit) -> { resume(@Int.0) },\n"
    "      put(@Int) -> { resume(()) }\n"
    "    } in {\n      put(4);\n      get(())\n    }\n  }\n}",
)
_CLOSURE_ARRAY = _source(
    "type IntToInt = fn(Int -> Int) effects(pure);",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  let @Array<IntToInt> = [fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }, "
    "fn(@Int -> @Int) effects(pure) { @Int.0 * 2 }];\n"
    "  apply_fn(@Array<IntToInt>.0[1], 20) + apply_fn(@Array<IntToInt>.0[0], 1)\n}",
)
_WRAP_EQ = _source(
    "private data Box<T> {\n  MkBox(T)\n}",
    "private forall<T> fn wrap(@T -> @Box<T>)\n" + _C + "{\n  MkBox(@T.0)\n}",
    "public fn main(@Unit -> @Bool)\n" + _C + "{\n  wrap(1) == wrap(1)\n}",
)
_INDEX_LITERAL_ARGUMENT = _source(
    "private forall<T> fn pick(@T, @T -> @T)\n" + _C + "{\n  @T.1\n}",
    "public fn f(@Nat -> @Int)\n  requires(@Nat.0 < 2)\n  ensures(true)\n"
    "  effects(pure)\n{\n  pick([1, 2][@Nat.0], 5)\n}",
)
_LITERAL_SUBPATTERN = _source(
    "public fn f(@Int -> @Int)\n" + _C + "{\n"
    "  match Some(@Int.0) {\n    Some(3) -> 1,\n    _ -> 0\n  }\n}",
)
_TUPLE_WILDCARD = _source(
    "public fn f(@Int -> @Int)\n" + _C + "{\n"
    "  match Tuple(@Int.0, true) {\n    Tuple(@Int, _) -> @Int.0 + 1\n  }\n}",
)
_GENERIC_ALIAS_LET = _source(
    "type Two<T> = Tuple<T, T>;",
    "public fn f(@Int -> @Int)\n" + _C + "{\n"
    "  let @Two<Int> = Tuple(@Int.0, 2);\n"
    "  match @Two<Int>.0 {\n    Tuple(@Int, @Int) -> @Int.1 + @Int.0\n  }\n}",
)
_CTOR_OF_MAP_RESULT = _source(
    "private data Bag {\n  Big(Array<String>)\n}",
    "public fn main(@Unit -> @Int)\n" + _C + "{\n"
    "  match Big(array_map(array_range(0, 3), fn(@Int -> @String) effects(pure) "
    "{ int_to_string(@Int.0) })) {\n"
    "    Big(@Array<String>) -> nat_to_int(array_length(@Array<String>.0))\n  }\n}",
)
_MAP_KEYS_OF_AN_IF = _source(
    "public fn main(@Unit -> @Unit)\n  requires(true)\n  ensures(true)\n"
    "  effects(<IO>)\n{\n"
    "  let @Array<String> = map_keys(if true then { map_insert(map_new(), \"a\", 1) } "
    "else { map_new() });\n"
    "  IO.print(@Array<String>.0[0]);\n  IO.print(\"\\n\")\n}",
)


REPROS: dict[str, Repro] = {
    "1514_let_through_parameterised_alias": Repro(
        {"main.vera": _I1514_LET}, _runs("main", None, 5)),
    "1514_silent_drop": Repro(
        {"main.vera": _I1514_SILENT}, _runs("main", None, 4)),
    "1514_match_binder": Repro(
        {"main.vera": _I1514_BINDER}, _runs("main", None, 5)),
    "1515_nested_prelude_generic_argument": Repro(
        {"main.vera": _I1515}, _runs("main", None, 3)),
    "1516_apply_fn_on_returned_closure": Repro(
        {"main.vera": _I1516}, _runs("main", None, 42)),
    "1516_apply_fn_on_cell_read": Repro(
        {"main.vera": _I1516_CELL}, _runs("main", None, 5)),
    "1550_show_generic_data_from_module": Repro(
        {"mb.vera": _I1550_MB, "main.vera": _I1550_MAIN},
        _runs("main", None, "MkBox(5)")),
    "1550_show_generic_data_one_file": Repro(
        {"main.vera": _I1550_ONE}, _runs("main", None, "MkBox(5)")),
    "1551_verified_clone_is_emitted_clone": Repro(
        {"ma.vera": _I1551_MA, "main.vera": _I1551_MAIN},
        _same_clones_verified_and_compiled),
    "1555_eq_of_generic_data_calls": Repro(
        {"main.vera": _I1555}, _runs("main", None, 1)),
    "1555_eq_of_option_calls": Repro(
        {"main.vera": _I1555_OPTION}, _runs("main", None, 1)),
    "1564_index_array_literal": Repro(
        {"main.vera": _I1564}, _runs("main", None, 1)),
    "1564_index_generic_call_result": Repro(
        {"main.vera": _I1564_GENERIC}, _runs("main", None, 5)),
    "1572_qualified_call_to_module_generic_is_verified": Repro(
        {"mb.vera": _I1572_MB, "ma.vera": _I1572_MA, "main.vera": _I1572_MAIN},
        _verify_refuses("E500")),
    "1575_module_generic_through_generic_calls_private_sibling": Repro(
        {"ma.vera": _I1575_MA, "main.vera": _I1575_MAIN},
        _runs("main", None, 12)),
    "1578_match_on_array_fold": Repro(
        {"main.vera": _I1578}, _runs("main", None, 3)),
    "1609_integer_match_over_byte_call": Repro(
        {"main.vera": _I1609}, _runs("classify", [65], 1)),
    "1638_module_if_over_generic_arms": Repro(
        {"mb.vera": _I1638_MB, "main.vera": _I1638_MAIN},
        _runs("f", [7], 7)),
    "1686_map_get_on_cell_read": Repro(
        {"main.vera": _I1686}, _runs("main", None, 5)),
    "1730_array_find_i32_class_payload": Repro(
        {"main.vera": _I1730}, _runs("main", None, stdout="255 true 5\n")),
    "1730_array_find_record_and_string": Repro(
        {"main.vera": _I1730_WIDE}, _runs("main", None, stdout="34 bc\n")),
    "1594_nat_built_tuple_sort": Repro(
        {"main.vera": _I1594}, _verifies()),
    "1767_counterexample_names_in_source_order": Repro(
        {"main.vera": _I1767}, lambda path: _counterexample_in_source_order(
            pipeline.verify(path))),
    "neg_nat_interpolation": Repro(
        {"main.vera": _NEG_NAT_INTERPOLATION},
        _runs("show_neg", [5], "-5")),
    "sorts_from_expression_types": Repro(
        {"main.vera": _SORTS}, _verifies(_every_obligation_tier1)),
    "interpolation_converter_from_checker_type": Repro(
        {"main.vera": _INTERPOLATION_CONVERTER},
        _runs("main", None, stdout="call A\nbound A\n")),
    "parameterised_alias_width_parameter": Repro(
        {"main.vera": _ALIAS_WIDTH}, _runs("main", None, 42)),
    "parameterised_alias_width_let": Repro(
        {"main.vera": _ALIAS_WIDTH_LET}, _runs("main", None, 42)),
    # #1685 (through #1680): a `State<Future<Int>>` cell loads.
    "1685_future_cell_loads": Repro(
        {"main.vera": _FUTURE_CELL}, _runs("main", None, 1)),
    # PR #1700's review: an index into a generic call's `Array` result.
    "index_into_generic_array_result": Repro(
        {"main.vera": _WRAP_INDEX}, _runs("main", None, 3)),
    # The v0.2.5 lanes' sightings.
    "show_of_generic_builtin_result": Repro(
        {"main.vera": _SHOW_REVERSE},
        _runs("main", None, stdout="[3, 2, 1]\n[3, 2, 1]\n")),
    "match_on_generic_fold_scrutinee": Repro(
        {"main.vera": _MATCH_FOLD}, _runs("main", None, 1)),
    # The generator's (PR #1784): an `if` whose block result code
    # generation derived from its arms, neither of which it could type.
    "if_of_a_throw_and_a_fold": Repro(
        {"main.vera": _IF_THROW_FOLD}, _runs("throw_fold", [1], 2)),
    "if_of_two_cell_handlers": Repro(
        {"main.vera": _IF_TWO_CELLS}, _runs("one_cell", [1], 3)),
    # PR #1791's review.
    "array_literal_of_closures": Repro(
        {"main.vera": _CLOSURE_ARRAY}, _runs("main", None, 42)),
    "eq_of_generic_call_results": Repro(
        {"main.vera": _WRAP_EQ}, _runs("main", None, 1)),
    # Routed from #1680: PR #1700's review, PR #1705's body, the reviews of
    # PRs #1721, #1722 and #1737.
    "index_into_array_literal_as_argument": Repro(
        {"main.vera": _INDEX_LITERAL_ARGUMENT}, _runs("f", [1], 5)),
    "literal_subpattern_in_constructor_pattern": Repro(
        {"main.vera": _LITERAL_SUBPATTERN}, _runs("f", [3], 1)),
    "wildcard_subpattern_in_tuple_pattern": Repro(
        {"main.vera": _TUPLE_WILDCARD}, _runs("f", [3], 4)),
    "generic_alias_as_let_type": Repro(
        {"main.vera": _GENERIC_ALIAS_LET}, _runs("f", [3], 5)),
    "constructor_of_array_map_result": Repro(
        {"main.vera": _CTOR_OF_MAP_RESULT}, _runs("main", None, 3)),
    "map_keys_of_an_if": Repro(
        {"main.vera": _MAP_KEYS_OF_AN_IF}, _runs("main", None, stdout="a\n")),
}


#: The lines that no longer reproduce at 94cef528, each pinned as fixed.
FIXED_AT_BASE = frozenset({
    "1515_nested_prelude_generic_argument",
    "1551_verified_clone_is_emitted_clone",
    "1572_qualified_call_to_module_generic_is_verified",
    "1575_module_generic_through_generic_calls_private_sibling",
    "1638_module_if_over_generic_arms",
})


#: The lines the typed program's own clone naming flips (#1679): the clone
#: of a generic over a data type is named, and so emitted, at the type's
#: arguments.  The backend's reads of the typed program flip the rest.
FIXED_BY_THE_TYPED_PROGRAM = frozenset({
    "1550_show_generic_data_from_module",
    "1550_show_generic_data_one_file",
})


#: The lines code generation's reads of the typed program flip (#1525):
#: each value's width is its checked type's (an `if`, a `match` or a
#: handler block's result the join's, a call's result the call's), and an
#: `apply_fn`'s closure is the function type the checker gave it.
FIXED_BY_THE_BACKEND_READS = frozenset({
    "1516_apply_fn_on_cell_read",
    "1516_apply_fn_on_returned_closure",
    "1578_match_on_array_fold",
    "constructor_of_array_map_result",
    "if_of_a_throw_and_a_fold",
    "if_of_two_cell_handlers",
    "match_on_generic_fold_scrutinee",
})


@pytest.mark.parametrize("name", [
    name if name in (FIXED_AT_BASE | FIXED_BY_THE_TYPED_PROGRAM
                     | FIXED_BY_THE_BACKEND_READS)
    else pytest.param(name, marks=pytest.mark.xfail(strict=True, reason="red at f1bc772d: a backend reader of the typed program flips it"))
    for name in sorted(REPROS)
])
def test_repro_type_level_line(name: str, tmp_path: Path) -> None:
    repro = REPROS[name]
    path = pipeline.write_tree(tmp_path, repro.files)
    repro.expect(path)
