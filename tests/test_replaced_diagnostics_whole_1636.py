"""Every diagnostic whose placement #1636 rebuilt, pinned whole.

#1636 placed every diagnostic through one constructor (`vera.errors.locate`
and `locate_at`), and so changed the two lines above some forty diagnostic
sites.  The Mutation (diff) lane selects every node within two lines of a
changed line, which made each of those sites' message text, and the
decisions around it, a mutant, and the suite asserted no such message
whole.  Each test here raises one diagnostic site with a real program or
command, through the stage the command runs, and asserts every diagnostic
of that code whole: `description`, `location`, `source_line`, `rationale`,
`fix`, `spec_ref`, `severity` and `error_code`, as `--json` carries them,
and the text a command prints where the site has its own.  A path under
the test's directory reads `<tmp>/`, one in the repository `<root>/`.
"""

from __future__ import annotations

import os
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from tests import pipeline

ROOT = Path(__file__).resolve().parent.parent


def _roots(tmp_path: Path | None) -> list[tuple[str, str]]:
    """The test's directory and the repository, as a diagnostic names them,
    each with the name it reads by here."""
    roots = []
    if tmp_path is not None:
        roots += [(p + os.sep, "<tmp>/")
                  for p in {str(tmp_path), str(tmp_path.resolve())}]
    roots.append((str(ROOT) + os.sep, "<root>/"))
    return sorted(roots, key=lambda r: -len(r[0]))


def _shown_file(value: str, roots: list[tuple[str, str]]) -> str:
    """A diagnostic's `file` (a location's or a frame's) as it is compared:
    under a root, the root's name and the rest relative to it in POSIX form,
    so `tests\\probes\\x.vera` on Windows reads as `tests/probes/x.vera`;
    outside every root, the path in POSIX form."""
    for real, shown in roots:
        if value.startswith(real):
            return shown + Path(value).relative_to(real).as_posix()
    return Path(value).as_posix()


def _norm(value: Any, roots: list[tuple[str, str]]) -> Any:
    if isinstance(value, str):
        for real, shown in roots:
            value = value.replace(real, shown)
        return value
    if isinstance(value, dict):
        return {k: (_shown_file(v, roots) if k == "file" and isinstance(v, str)
                    else _norm(v, roots))
                for k, v in value.items()}
    if isinstance(value, list):
        return [_norm(v, roots) for v in value]
    return value


def _as_dict(d: Any) -> dict[str, Any]:
    return d if isinstance(d, dict) else d.to_dict()


def _found(result: Any, code: str, tmp_path: Path | None = None
           ) -> list[dict[str, Any]]:
    """Every diagnostic of *code* the stage reported, as `--json` carries
    it, with the test's directory and the repository's named."""
    return [_norm(d, _roots(tmp_path)) for d in map(_as_dict, result.diagnostics)
            if d.get("error_code") == code]


class _cli:
    """`vera <args> --json <path>`'s diagnostics and warnings."""

    def __init__(self, *args: Any) -> None:
        envelope = pipeline.cli(args[0], "--json", *args[1:]).json()
        self.diagnostics = (envelope.get("diagnostics", [])
                            + envelope.get("warnings", []))


def _reported(diagnostics: Any) -> SimpleNamespace:
    """What a stage reported, as `_found` reads it, for a call that is not
    a stage's."""
    return SimpleNamespace(diagnostics=list(diagnostics))


def _entry_bytes(tmp_path: Path, data: bytes) -> Path:
    entry = tmp_path / "main.vera"
    entry.write_bytes(data)
    return entry


def _entry(tmp_path: Path, files: dict[str, str]) -> Path:
    return pipeline.write_tree(tmp_path, files)

_E002_A_CLAUSE_THE_CONTRACT_DOES_NOT_HAVE = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  invariant(true)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E005_AN_OPERATOR_WITH_NO_OPERAND = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 +\n'
 '}\n')

_E005_A_MISSING_CLOSING_BRACE = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n')

_E006_AN_UNKNOWN_CHARACTER = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 $ 1\n'
 '}\n')

_E008_A_MODULE_CALL_WITH_A_DOT = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  m.g(@Int.0)\n'
 '}\n')

_E008_A_DOTTED_MODULE_CALL = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  vera.math.abs(@Int.0)\n'
 '}\n')

_E024_A_BYTE_THAT_IS_NOT_UTF8 = (b'public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n  effects'
 b'(pure)\n{\n  -- \xff\n  @Int.0\n}\n')

_E032_A_CLAUSE_AFTER_EFFECTS = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  effects(pure)\n'
 '  ensures(true)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E032_A_REQUIRES_AFTER_EFFECTS = ('public fn f(@Int -> @Int)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '  requires(true)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E009_AN_INVALID_ESCAPE = ('public fn f(@Int -> @String)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  "bad \\q escape"\n'
 '}\n')

_E009_AN_EMPTY_INTERPOLATION = ('public fn f(@Int -> @String)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  "a \\() b"\n'
 '}\n')

_E040_A_PIPE_INTO_A_LITERAL = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 |> 1\n'
 '}\n')

_E011_A_CIRCULAR_IMPORT = {'a.vera': 'import main;\n'
           'public fn g(@Int -> @Int)\n'
           '  requires(true)\n'
           '  ensures(true)\n'
           '  effects(pure)\n'
           '{\n'
           '  @Int.0\n'
           '}\n',
 'main.vera': 'import a;\n'
              'public fn f(@Int -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  @Int.0\n'
              '}\n'}

_E012_AN_IMPORT_WITH_NO_FILE = {'main.vera': 'import nothere;\n'
              'public fn f(@Int -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  @Int.0\n'
              '}\n'}

_E013_AN_IMPORTED_MODULE_THAT_DOES_NOT_PARSE = {'a.vera': 'public fn g(@Int -> @Int)\n'
           '  requires(true)\n'
           '  ensures(true)\n'
           '  effects(pure)\n'
           '{\n'
           '  @Int.0 +\n'
           '}\n',
 'main.vera': 'import a;\n'
              'public fn f(@Int -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  @Int.0\n'
              '}\n'}

_E135_WRITTEN_MAP_KEY = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Map<Array<Int>, Int> = map_new();\n'
 '  nat_to_int(map_size(@Map<Array<Int>, Int>.0))\n'
 '}\n')

_E135_WRITTEN_MAP_VALUE = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Map<String, Array<Int>> = map_new();\n'
 '  nat_to_int(map_size(@Map<String, Array<Int>>.0))\n'
 '}\n')

_E135_WRITTEN_SET_ELEMENT = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Set<Array<Int>> = set_new();\n'
 '  nat_to_int(set_size(@Set<Array<Int>>.0))\n'
 '}\n')

_E135_A_MAP_WHOSE_KEY_AND_VALUE_ARE_BOTH_ARRAYS = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Map<Array<Int>, Array<Int>> = map_new();\n'
 '  nat_to_int(map_size(@Map<Array<Int>, Array<Int>>.0))\n'
 '}\n')

_E135_INFERRED_MAP_KEY = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(map_size(map_insert(map_new(), [1, 2], 5)))\n'
 '}\n')

_E135_INFERRED_MAP_VALUE = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(map_size(map_insert(map_new(), "k", [1, 2])))\n'
 '}\n')

_E135_INFERRED_SET_ELEMENT = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(set_size(set_add(set_new(), [1, 2])))\n'
 '}\n')

_E135_INFERRED_ZERO_SIZE_VALUE = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(map_size(map_insert(map_new(), "k", ())))\n'
 '}\n')

_E613_AN_ORD_CONSTRAINT_AT_BOOL = ('public forall<T where Ord<T>> fn lt(@T, @T -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match compare(@T.1, @T.0) {\n'
 '    Less -> true,\n'
 '    _ -> false\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  if lt(true, false) then {\n'
 '    1\n'
 '  } else {\n'
 '    0\n'
 '  }\n'
 '}\n')

_E613_AN_EQ_CONSTRAINT_AT_AN_ARRAY = ('public forall<T where Eq<T>> fn same(@T, @T -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @T.1 == @T.0\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  same([1], [1])\n'
 '}\n')

_E613_A_VARIABLE_NO_ARGUMENT_FIXES = ('private forall<T where Ord<T>> fn none_ord(@Unit -> @Option<T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  None\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match none_ord(()) {\n'
 '    None -> 7,\n'
 '    Some(@Int) -> @Int.0\n'
 '  }\n'
 '}\n')

_E607_A_STATE_CELL_AT_A_STRING = ('private forall<T> fn f(@T -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[State<T>](@T = @T.0) {\n'
 '    get(@Unit) -> { resume(@T.0) },\n'
 '    put(@T) -> { resume(()) }\n'
 '  } in {\n'
 '    1\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  f("abc")\n'
 '}\n')

_E612_AN_EXCEPTION_PAYLOAD_AT_UNIT = ('public forall<T> fn g(@T -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[Exn<T>] {\n'
 '    throw(@T) -> { 0 }\n'
 '  } in {\n'
 '    1\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  g(())\n'
 '}\n')

_E533_A_STATE_DECLARED_AT_ANOTHER_TYPE = ('private forall<T> fn sneak(@T -> @T)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[State<T>](@Nat = 3) {\n'
 '    put(@T) -> { resume(()) }\n'
 '  } in {\n'
 '    put(@T.0);\n'
 '    get(())\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn go(@Int, @Float64 -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Float64 = sneak(@Float64.0);\n'
 '  sneak(@Int.0)\n'
 '}\n')

_E139_A_MUTUAL_CYCLE = ('private forall<T> fn f(@T, @Nat -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    0\n'
 '  } else {\n'
 '    g(Some(@T.0), @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 '\n'
 'private forall<U> fn g(@U, @Nat -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    1\n'
 '  } else {\n'
 '    f(Some(@U.0), @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  f(7, 3)\n'
 '}\n')

_E139_A_SELF_CYCLE = ('private forall<T where Eq<T>> fn same_deep(@T, @T, @Nat -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    @T.1 == @T.0\n'
 '  } else {\n'
 '    same_deep(Some(@T.1), Some(@T.0), @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  same_deep(7, 7, 1)\n'
 '}\n')

_E139_A_UNCALLED_CYCLE = ('private forall<T> fn deepen(@T, @Nat -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    0\n'
 '  } else {\n'
 '    deepen([@T.0], @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  1\n'
 '}\n')

_E139_A_GROWING_CALL_IN_A_WHERE_HELPER = ('private forall<T> fn gw(@T, @Nat -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    0\n'
 '  } else {\n'
 '    helper(@T.0, @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 'where {\n'
 '  fn helper(@T, @Nat -> @Int)\n'
 '    requires(true)\n'
 '    ensures(true)\n'
 '    decreases(@Nat.0)\n'
 '    effects(pure)\n'
 '  {\n'
 '    gw(Some(@T.0), @Nat.0)\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  gw(1, 2)\n'
 '}\n')

_E202_A_CLOSURE_COMPILED_AT_ITS_OWN_TYPE = ('type Conv = fn(Option<Nat> -> Option<String>) effects(pure);\n'
 'type Endo<T> = fn(T -> T) effects(pure);\n'
 '\n'
 'private forall<T> fn mk(@Unit -> @Endo<T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  fn(@T -> @T) effects(pure) { @T.0 }\n'
 '}\n'
 '\n'
 'private fn use(@Conv -> @Unit)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(<IO>)\n'
 '{\n'
 '  match apply_fn(@Conv.0, Some(0)) {\n'
 '    Some(@String) -> IO.print(string_concat("[", '
 'string_concat(@String.0, "]"))),\n'
 '    None -> IO.print("none")\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Unit)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(<IO>)\n'
 '{\n'
 '  use(mk(()))\n'
 '}\n')

_E202_CLOSURE_DIFF_NOWHERE = ('type Endo<T> = fn(T -> T) effects(pure);\n'
 'type P<A, B> = fn(A -> B) effects(pure);\n'
 '\n'
 'public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Endo<T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  fn(@T -> @T) effects(pure) { @T.0 }\n'
 '}\n'
 '\n'
 'private fn take(@P<Int, String> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  0\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None))\n'
 '}\n')

_E202_HELD_CLOSURE_DIFF_NOWHERE = ('type IntEndo = fn(Int -> Int) effects(pure);\n'
 '\n'
 'public data Conv2<A, B> {\n'
 '  Conv2(fn(A -> B) effects(pure))\n'
 '}\n'
 '\n'
 'public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Conv2<T, T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Conv2(fn(@T -> @T) effects(pure) { @T.0 })\n'
 '}\n'
 '\n'
 'private fn take(@Conv2<Int, String> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  0\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None))\n'
 '}\n')

_E202_FN_PARAM_RESULT_DIFF_NOWHERE = ('type Lift<T> = fn(Option<T> -> Array<T>) effects(pure);\n'
 'type Q<A, B> = fn(Option<A> -> Array<B>) effects(pure);\n'
 '\n'
 'public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Lift<T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  fn(@Option<T> -> @Array<T>) effects(pure) { [] }\n'
 '}\n'
 '\n'
 'private fn take(@Q<Int, String> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  array_length(apply_fn(@Q<Int, String>.0, None)) + 3\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None))\n'
 '}\n')

_E202_DATA_FIELDS_DIFF_ARGUMENT = ('public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Two<T, T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Two(@Option<T>.0, @Option<T>.0)\n'
 '}\n'
 '\n'
 'private fn take(@Two<Int, String> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Two<Int, String>.0 {\n'
 '    Two(Some(@Int), _) -> 10,\n'
 '    Two(None, _) -> 20\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(Some(@Int.0)))\n'
 '}\n')

_E202_TUPLE_DIFF_ARGUMENT = ('public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Tuple<Option<T>, Option<T>>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Tuple(@Option<T>.0, @Option<T>.0)\n'
 '}\n'
 '\n'
 'private fn take(@Tuple<Option<Int>, Option<String>> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Tuple<Option<Int>, Option<String>>.0 {\n'
 '    Tuple(@Option<Int>, @Option<String>) -> match @Option<Int>.0 {\n'
 '      Some(@Int) -> @Int.0,\n'
 '      None -> 20\n'
 '    }\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(Some(@Int.0)))\n'
 '}\n')

_E202_NESTED_DIFF_EXPECTED = ('public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Tuple<Array<Option<T>>, '
 'Option<Option<T>>>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Tuple([@Option<T>.0], Some(@Option<T>.0))\n'
 '}\n'
 '\n'
 'private fn take(@Tuple<Array<Option<Int>>, Option<Option<String>>> -> '
 '@Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Tuple<Array<Option<Int>>, Option<Option<String>>>.0 {\n'
 '    Tuple(@Array<Option<Int>>, @Option<Option<String>>) -> '
 'array_length(@Array<Option<Int>>.0) + 30\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(Some(5)))\n'
 '}\n')

_E202_CLOSURE_VAR_NOWHERE = ('type Endo<T> = fn(T -> T) effects(pure);\n'
 'type P<A, B> = fn(A -> B) effects(pure);\n'
 '\n'
 'public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Endo<T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  fn(@T -> @T) effects(pure) { @T.0 }\n'
 '}\n'
 '\n'
 'private forall<U> fn take(@P<Int, U>, @Option<U> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  0\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None), None)\n'
 '}\n')

_W005_ONE_TYPED_HOLE = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  ?\n'
 '}\n')

_W005_TWO_TYPED_HOLES = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  ?\n'
 '}\n'
 '\n'
 'public fn g(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  ?\n'
 '}\n')

_E700_A_GUARD_ON_AN_ADMITTED_INPUT = ('public fn pick(@Nat -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(@Nat.result == @Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Array<Int> = [10, 20, 30];\n'
 '  if @Array<Int>.0[@Nat.0] > 0 then {\n'
 '    @Nat.0\n'
 '  } else {\n'
 '    @Nat.0\n'
 '  }\n'
 '}\n')

_E700_A_GUARD_WITHOUT_DISTRUST = ('public fn tricky(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(exists(@Int, 1, fn(@Int -> @Bool) effects(pure) { false }))\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E701_A_GENERATOR_THAT_CANNOT_SERVE_THE_REQUIRES = ('private fn is_small(@Int -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(@Bool.result == (@Int.0 >= 0 && @Int.0 < 100))\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 >= 0 && @Int.0 < 100\n'
 '}\n'
 '\n'
 'public fn h(@Int -> @Int)\n'
 '  requires(is_small(@Int.0))\n'
 '  ensures(@Int.result > 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 + 1\n'
 '}\n')

_E701_NO_INPUT_WITHIN_THE_BOUNDS = ('public fn above_bound(@Int -> @Int)\n'
 '  requires(@Int.0 > 10000000000000000)\n'
 '  ensures(@Int.result > 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E701_SKIPPED_PROOFS = ('public fn opt_pos(@Option<Int> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result >= 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Option<Int>.0 {\n'
 '    Some(@Int) -> if @Int.0 >= 0 then { @Int.0 } else { 0 },\n'
 '    None -> 0\n'
 '  }\n'
 '}\n'
 '\n'
 'public forall<T> fn same(@T -> @T)\n'
 '  requires(true)\n'
 '  ensures(@T.result == @T.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  @T.0\n'
 '}\n'
 '\n'
 'private fn use_same(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  same(@Int.0)\n'
 '}\n'
 '\n'
 'public forall<T> fn const_one(@T -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result == 1)\n'
 '  effects(pure)\n'
 '{\n'
 '  1\n'
 '}\n'
 '\n'
 'public fn safe_idx(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Array<Int> = [1, 2, 3];\n'
 '  @Array<Int>.0[1]\n'
 '}\n')

_E702_A_PROGRAM_THAT_DOES_NOT_COMPILE = ('public fn add1(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result == @Int.0 + 1)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 + 1\n'
 '}\n'
 '\n'
 'private fn later(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  ?\n'
 '}\n')

_E702_A_PROOF_NO_CHECK_STANDS_FOR = ('public fn s(@Int -> @String)\n'
 '  requires(true)\n'
 '  ensures(@String.result == "neg")\n'
 '  effects(pure)\n'
 '{\n'
 '  if mo(7) >= 0 then { "neg" } else { "pos" }\n'
 '}\n'
 '\n'
 'type IntToNat = fn(Int -> Nat) effects(pure);\n'
 'type IntToInt = fn(Int -> Int) effects(pure);\n'
 '\n'
 'private fn apply_nat(@IntToNat, @Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  apply_fn(@IntToNat.0, @Int.0)\n'
 '}\n'
 '\n'
 'private fn mo(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @IntToInt = fn(@Int -> @Int) effects(pure) { -7 };\n'
 '  apply_nat(@IntToInt.0, @Int.0)\n'
 '}\n')

_E702_ONLY_A_REQUIRES = ('public fn keep(@Int -> @Int)\n'
 '  requires(@Int.0 > 0)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E703_A_FALSE_PROOF = ('public fn main(-> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result < 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if mo(7) >= 0 then { 0 - 1 } else { 1 }\n'
 '}\n'
 '\n'
 'type IntToNat = fn(Int -> Nat) effects(pure);\n'
 'type IntToInt = fn(Int -> Int) effects(pure);\n'
 '\n'
 'private fn apply_nat(@IntToNat, @Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  apply_fn(@IntToNat.0, @Int.0)\n'
 '}\n'
 '\n'
 'private fn mo(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @IntToInt = fn(@Int -> @Int) effects(pure) { -7 };\n'
 '  apply_nat(@IntToInt.0, @Int.0)\n'
 '}\n')

_E136_FN_IS_NOT_A_TYPE = ('public fn f(@Fn -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  0\n'
 '}\n')

_E136_AN_IMPORT_THAT_DID_NOT_RESOLVE = {'main.vera': 'import lib.nothere(Foo);\n'
              '\n'
              'public fn f(@Foo -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  0\n'
              '}\n'}

_E136_A_PRIVATE_DATA_TYPE = {'lib/types.vera': 'module lib.types;\n'
                   '\n'
                   'public data Other {\n'
                   '  O\n'
                   '}\n'
                   '\n'
                   'private data Foo {\n'
                   '  F\n'
                   '}\n',
 'main.vera': 'import lib.types;\n'
              '\n'
              'public fn f(@Foo -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  0\n'
              '}\n'}

_E136_A_DATA_TYPE_NOT_IMPORTED = {'lib/types.vera': 'module lib.types;\n'
                   '\n'
                   'public data Other {\n'
                   '  O\n'
                   '}\n'
                   '\n'
                   'public data Foo {\n'
                   '  F\n'
                   '}\n'
                   '\n'
                   'public fn mk(@Unit -> @Int)\n'
                   '  requires(true)\n'
                   '  ensures(true)\n'
                   '  effects(pure)\n'
                   '{\n'
                   '  0\n'
                   '}\n',
 'main.vera': 'import lib.types(mk);\n'
              '\n'
              'public fn f(@Foo -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  0\n'
              '}\n'}

_E136_AN_ALIAS_IN_A_MODULE = {'lib/types.vera': 'module lib.types;\n'
                   '\n'
                   'public data Other {\n'
                   '  O\n'
                   '}\n'
                   '\n'
                   'type Pos={@Int|@Int.0>0};\n',
 'main.vera': 'import lib.types;\n'
              '\n'
              'public fn f(@Pos -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  0\n'
              '}\n'}

_E136_A_FUNCTION_TYPE_ALIAS_IN_A_MODULE = {'lib/types.vera': 'module lib.types;\n'
                   '\n'
                   'public data Other {\n'
                   '  O\n'
                   '}\n'
                   '\n'
                   'type Handler = fn(Option<Array<String>>, '
                   'Option<Array<String>>, Option<Array<String>>, '
                   'Option<Array<String>> -> Option<Array<String>>) '
                   'effects(pure);\n',
 'main.vera': 'import lib.types;\n'
              '\n'
              'public fn f(@Handler -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  0\n'
              '}\n'}

_E136_AN_IMPORT_LIST_NAMING_NO_TYPE = {'lib/types.vera': 'module lib.types;\n\npublic data Other {\n  O\n}\n\n',
 'main.vera': 'import lib.types(Foo);\n'
              '\n'
              'public fn f(@Foo -> @Int)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  0\n'
              '}\n'}

_E202_DATA_FIELDS_DIFF_NOWHERE = ('public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Two<T, T>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Two(@Option<T>.0, @Option<T>.0)\n'
 '}\n'
 '\n'
 'private fn take(@Two<Int, String> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Two<Int, String>.0 {\n'
 '    Two(Some(@Int), _) -> 10,\n'
 '    Two(None, _) -> 20\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None))\n'
 '}\n')

_E202_TUPLE_DIFF_NOWHERE = ('public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Tuple<Option<T>, Option<T>>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Tuple(@Option<T>.0, @Option<T>.0)\n'
 '}\n'
 '\n'
 'private fn take(@Tuple<Option<Int>, Option<String>> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Tuple<Option<Int>, Option<String>>.0 {\n'
 '    Tuple(@Option<Int>, @Option<String>) -> match @Option<Int>.0 {\n'
 '      Some(@Int) -> @Int.0,\n'
 '      None -> 20\n'
 '    }\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None))\n'
 '}\n')

_E202_NESTED_DIFF_NOWHERE = ('public data Two<A, B> {\n'
 '  Two(Option<A>, Option<B>)\n'
 '}\n'
 '\n'
 'private forall<T> fn make(@Option<T> -> @Tuple<Array<Option<T>>, '
 'Option<Option<T>>>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Tuple([@Option<T>.0], Some(@Option<T>.0))\n'
 '}\n'
 '\n'
 'private fn take(@Tuple<Array<Option<Int>>, Option<Option<String>>> -> '
 '@Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Tuple<Array<Option<Int>>, Option<Option<String>>>.0 {\n'
 '    Tuple(@Array<Option<Int>>, @Option<Option<String>>) -> '
 'array_length(@Array<Option<Int>>.0) + 30\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  take(make(None))\n'
 '}\n')

_TRAP_LOCAL = ('public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  boom(7)\n'
 '}\n'
 '\n'
 'private fn boom(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 / 0\n'
 '}\n')

_TRAP_MAIN = ('import lib(boom);\n'
 '\n'
 'public fn main(@Unit -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  boom(7)\n'
 '}\n')

_TRAP_LIB = ('module lib;\n'
 '\n'
 'public fn boom(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0 / 0\n'
 '}\n')

_OK = ('public fn f(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n')

_E703_A_FALSE_PROOF_BEHIND_A_PARAMETER = ('public fn below_min(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result < 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if mo(7) >= 0 then { 0 - 1 } else { 1 }\n'
 '}\n'
 '\n'
 'type IntToNat = fn(Int -> Nat) effects(pure);\n'
 'type IntToInt = fn(Int -> Int) effects(pure);\n'
 '\n'
 'private fn apply_nat(@IntToNat, @Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  apply_fn(@IntToNat.0, @Int.0)\n'
 '}\n'
 '\n'
 'private fn mo(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @IntToInt = fn(@Int -> @Int) effects(pure) { -7 };\n'
 '  apply_nat(@IntToInt.0, @Int.0)\n'
 '}\n')

_E703_A_PROOF_RESTING_ON_AN_ASSUME = ('public fn trusting(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result > 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  assume(@Int.0 > 0);\n'
 '  @Int.0\n'
 '}\n'
 '\n'
 'private fn helper(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result > 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  assume(@Int.0 > 0);\n'
 '  @Int.0\n'
 '}\n'
 '\n'
 'public fn via_callee(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(@Int.result > 0)\n'
 '  effects(pure)\n'
 '{\n'
 '  helper(@Int.0)\n'
 '}\n')

_E543_A_DECREASES_ON_AN_EXN_ROW = ('public fn f(@Nat -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(<Exn<Int>>)\n'
 '{\n'
 '  if @Nat.0 > 5 then { 0 } else { f(@Nat.0 + 1) }\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[Exn<Int>] {\n'
 '    throw(@Int) -> { 0 }\n'
 '  } in {\n'
 '    f(1)\n'
 '  }\n'
 '}\n')

_E543_AN_ENSURES_OVER_A_STRING_RESULT = ('public fn f(@Int -> @String)\n'
 '  requires(true)\n'
 '  ensures(@String.result == show(@Int.0))\n'
 '  effects(pure)\n'
 '{\n'
 '  "not the number"\n'
 '}\n')

_E506_A_NESTED_REFINEMENT = ('type Pos = { @Int | @Int.0 > 0 };\n'
 'type Small = { @Pos | @Pos.0 < 10 };\n'
 '\n'
 'public fn mk(@Float64 -> @Option<Small>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  Some(float_to_int(@Float64.0))\n'
 '}\n')

_E504_A_DISCLOSED_NARROWING_IN_AN_IMPORTED_MODULE = {'cb.vera': 'type NonNeg = { @Int | @Int.0 >= 0 };\n'
            '\n'
            '\n'
            'public fn mk(@Int -> @Option<NonNeg>)\n'
            '  requires(true)\n'
            '  ensures(true)\n'
            '  effects(pure)\n'
            '{\n'
            '  let @Option<Int> = Some(apply_fn(fn(@Int -> @Int) '
            'effects(pure) { @Int.0 }, @Int.0)); @Option<Int>.0\n'
            '}\n',
 'main.vera': 'import cb;\n'
              '\n'
              'type NonNeg = { @Int | @Int.0 >= 0 };\n'
              '\n'
              '\n'
              'public fn relay(@Int -> @Option<NonNeg>)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  match cb::mk(@Int.0) {\n'
              '    Some(@NonNeg) -> {\n'
              '      let @String = string_slice("ab", @NonNeg.0, 1);\n'
              '      Some(@NonNeg.0)\n'
              '    },\n'
              '    None -> None\n'
              '  }\n'
              '}\n'}

_E503_A_LATER_ARRAY_ELEMENT = ('public fn f(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  let @Nat = 3;\n'
 '  [@Int.0, @Nat.0][0]\n'
 '}\n')

_E505_A_REFUTED_VALUE_INSIDE_A_HANDLE = ('type PosInt = { @Int | @Int.0 > 0 };\n'
 '\n'
 'public fn f(@Float64 -> @Option<PosInt>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[State<Int>](@Int = 1) {\n'
 '    get(@Unit) -> { resume(@Int.0) },\n'
 '    put(@Int) -> { resume(()) }\n'
 '  } in {\n'
 '    Some(0 - 5)\n'
 '  }\n'
 '}\n')

_E506_A_VALUE_INSIDE_A_HANDLE_CLAUSE = ('type PosInt = { @Int | @Int.0 > 0 };\n'
 '\n'
 'public fn f(@Float64 -> @Option<PosInt>)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[Exn<Int>] {\n'
 '    throw(@Int) -> { Some(0 - 5) }\n'
 '  } in {\n'
 '    throw(1)\n'
 '  }\n'
 '}\n')

_E503_E505_A_BINDER_AFTER_A_WILDCARD = ('type Pos = { @Int | @Int.0 > 0 };\n'
 '\n'
 'private data P {\n'
 '  MkP(Int, Int, Int)\n'
 '}\n'
 '\n'
 'public fn f(@Option<P> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Option<P>.0 {\n'
 '    Some(MkP(_, @Nat, @Pos)) -> nat_to_int(@Nat.0) + @Pos.0,\n'
 '    None -> 0\n'
 '  }\n'
 '}\n')

_E506_AN_IMPORTED_GENERIC_CLONE = {'glib.vera': 'module glib;\n'
              '\n'
              'type NonNeg = { @Int | @Int.0 >= 0 };\n'
              '\n'
              '\n'
              'public forall<T> fn gen(@T, @Int -> @Option<NonNeg>)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  let @Option<Int> = Some(apply_fn(fn(@Int -> @Int) '
              'effects(pure) { @Int.0 }, @Int.0)); @Option<Int>.0\n'
              '}\n',
 'main.vera': 'import glib;\n'
              '\n'
              'type NonNeg = { @Int | @Int.0 >= 0 };\n'
              '\n'
              '\n'
              'private fn gen(@Int -> @Option<NonNeg>)\n'
              '  requires(true)\n'
              '  ensures(true)\n'
              '  effects(pure)\n'
              '{\n'
              '  if @Int.0 >= 0 then { Some(@Int.0) } else { None }\n'
              '}\n'
              '\n'
              'public fn use_it(@Int -> @Int)\n'
              '  requires(true)\n'
              '  ensures(@Int.result >= 0)\n'
              '  effects(pure)\n'
              '{\n'
              '  match glib::gen("x", @Int.0) {\n'
              '    Some(@NonNeg) -> @NonNeg.0,\n'
              '    None -> 0\n'
              '  }\n'
              '}\n'}

_STR_ESCAPE = ('public fn f(@Int -> @String)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  "bad \\q escape"\n'
 '}\n')

_E533_A_STATE_AT_A_VARIABLE_NO_PARAMETER_HOLDS = ('private forall<T> fn sneak(@Array<T> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  handle[State<T>](@Nat = 3) {\n'
 '    put(@T) -> { resume(()) }\n'
 '  } in {\n'
 '    1\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn go(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  sneak([@Int.0])\n'
 '}\n')

_E613_A_FORMAL_WITH_NO_EXAMPLE = ('private forall<T where Eq<T>> fn same_t(@Tuple<T, Int> -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  true\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  same_t(Tuple([1], 2))\n'
 '}\n')

_E613_A_VARIABLE_IN_THE_SECOND_FORMAL = ('private forall<T where Eq<T>> fn same2(@Int, @T -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  true\n'
 '}\n'
 '\n'
 'public fn main(@Unit -> @Bool)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  same2(1, [1])\n'
 '}\n')

_E503_E505_A_BINDER_AFTER_A_WILDCARD_E503 = ('type Pos = { @Int | @Int.0 > 0 };\n'
 '\n'
 'private data P {\n'
 '  MkP(Int, Int, Int)\n'
 '}\n'
 '\n'
 'public fn f(@Option<P> -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  match @Option<P>.0 {\n'
 '    Some(MkP(_, @Nat, @Pos)) -> nat_to_int(@Nat.0) + @Pos.0,\n'
 '    None -> 0\n'
 '  }\n'
 '}\n')

_E543_STRING = ('public fn f(@Int -> @String)\n'
 '  requires(true)\n'
 '  ensures(@String.result == show(@Int.0))\n'
 '  effects(pure)\n'
 '{\n'
 '  "not the number"\n'
 '}\n')

_E503_A_NARROWING_AT_A_TAIL_CALL_MUTUAL_PAIR = ('private fn wrap(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n'
 '\n'
 'private fn ev(@Int, @Nat -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    wrap(@Int.0)\n'
 '  } else {\n'
 '    od(@Int.0, @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 '\n'
 'private fn od(@Int, @Nat -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  decreases(@Nat.0)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Nat.0 == 0 then {\n'
 '    wrap(@Int.0)\n'
 '  } else {\n'
 '    ev(@Int.0, @Nat.0 - 1)\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  ev(@Int.0, 3)\n'
 '}\n'
 '\n'
 'public fn show(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(f(@Int.0))\n'
 '}\n')

_E503_A_NARROWING_AT_A_TAIL_CALL_IF_ARM = ('private fn wrap(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  if @Int.0 > 100 then {\n'
 '    wrap(0)\n'
 '  } else {\n'
 '    wrap(@Int.0)\n'
 '  }\n'
 '}\n'
 '\n'
 'public fn show(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(f(@Int.0))\n'
 '}\n')

_E503_A_NARROWING_AT_A_TAIL_CALL_LAST = ('private fn wrap(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  @Int.0\n'
 '}\n'
 '\n'
 'public fn f(@Int -> @Nat)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  wrap(@Int.0)\n'
 '}\n'
 '\n'
 'public fn show(@Int -> @Int)\n'
 '  requires(true)\n'
 '  ensures(true)\n'
 '  effects(pure)\n'
 '{\n'
 '  nat_to_int(f(@Int.0))\n'
 '}\n')


def test_e002_a_clause_the_contract_does_not_have(tmp_path: Path) -> None:
    """missing_effect_clause: an `invariant` where `effects` belongs."""
    assert _found(
        pipeline.check(_E002_A_CLAUSE_THE_CONTRACT_DOES_NOT_HAVE, file="main.vera"),
        "E002", tmp_path) == (
        [{'severity': 'error',
          'description': 'Function is missing its effects() declaration. Every '
                         'function in Vera must declare its effects '
                         'explicitly.',
          'location': {'line': 4, 'column': 3, 'file': 'main.vera'},
          'source_line': '  invariant(true)',
          'rationale': 'Vera is pure by default. All side effects must be '
                       'declared in the function signature so the compiler can '
                       'track them.',
          'fix': 'Add an effects clause after the contract block:\n'
                 '\n'
                 '  effects(pure)              -- for pure functions\n'
                 '  effects(<IO>)              -- for functions with IO\n'
                 '  effects(<State<Int>>)      -- for stateful functions\n'
                 '  effects(<State<Int>, IO>)  -- for multiple effects',
          'spec_ref': 'Chapter 5, Section 5.5 "Effect Declaration"',
          'error_code': 'E002'}])


def test_e005_an_operator_with_no_operand(tmp_path: Path) -> None:
    """unexpected_token: a binary operator with nothing after it."""
    assert _found(
        pipeline.check(_E005_AN_OPERATOR_WITH_NO_OPERAND, file="main.vera"),
        "E005", tmp_path) == (
        [{'severity': 'error',
          'description': 'Unexpected "}" at this position. Expected one of: '
                         '"!", "(", "-", "?", "@", "[", "{", FLOAT_LIT, ...',
          'location': {'line': 7, 'column': 1, 'file': 'main.vera'},
          'source_line': '}',
          'rationale': 'The parser reached this position expecting one of the '
                       'listed tokens; the token found does not begin any '
                       'construct valid here.',
          'fix': 'Replace the unexpected token with one of the expected '
                 "tokens, or check for a missing delimiter (such as '}', ')', "
                 "or ',') earlier in the construct.",
          'spec_ref': 'Chapter 10, "Formal Grammar"',
          'error_code': 'E005'}])


def test_e005_a_missing_closing_brace(tmp_path: Path) -> None:
    """unexpected_token: the end of the file inside a body."""
    assert _found(
        pipeline.check(_E005_A_MISSING_CLOSING_BRACE, file="main.vera"),
        "E005", tmp_path) == (
        [{'severity': 'error',
          'description': 'Unexpected "" at this position. Expected one of: '
                         '"!=", "%", "&&", ")", "*", "+", ",", "-", ...',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  @Int.0',
          'rationale': 'The parser reached this position expecting one of the '
                       'listed tokens; the token found does not begin any '
                       'construct valid here.',
          'fix': 'Replace the unexpected token with one of the expected '
                 "tokens, or check for a missing delimiter (such as '}', ')', "
                 "or ',') earlier in the construct.",
          'spec_ref': 'Chapter 10, "Formal Grammar"',
          'error_code': 'E005'}])


def test_e006_an_unknown_character(tmp_path: Path) -> None:
    """diagnose_lark_error: a character no token begins with."""
    assert _found(
        pipeline.check(_E006_AN_UNKNOWN_CHARACTER, file="main.vera"),
        "E006", tmp_path) == (
        [{'severity': 'error',
          'description': 'Unexpected character "$". This character is not '
                         'valid in Vera source code at this position.',
          'location': {'line': 6, 'column': 10, 'file': 'main.vera'},
          'source_line': '  @Int.0 $ 1',
          'rationale': "Vera's lexical grammar accepts only a fixed alphabet "
                       'of characters; this character is not part of any '
                       'token.',
          'fix': 'Remove the invalid character, or replace it with valid '
                 'syntax (for example, use a string literal if the character '
                 'was intended as text).',
          'spec_ref': 'Chapter 1, "Lexical Structure"',
          'error_code': 'E006'}])


def test_e007_an_exception_the_parser_does_not_raise(tmp_path: Path) -> None:
    """diagnose_lark_error: the fallback for an exception that is no Lark
    error.  The LALR parser raises only UnexpectedToken and
    UnexpectedCharacters, so no source reaches it: it is read from the
    function, with an exception of another type."""
    from vera.errors import diagnose_lark_error

    assert _found(
        _reported([diagnose_lark_error(ValueError("something weird"), _OK,
                                       "main.vera")]),
        "E007", tmp_path) == (
        [{'severity': 'error',
          'description': 'Internal parser error: something weird',
          'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
          'error_code': 'E007'}])


def test_e008_a_module_call_with_a_dot(tmp_path: Path) -> None:
    """module_call_dot_syntax: `m.g(...)` where `m::g(...)` is meant."""
    assert _found(
        pipeline.check(_E008_A_MODULE_CALL_WITH_A_DOT, file="main.vera"),
        "E008", tmp_path) == (
        [{'severity': 'error',
          'description': "Module-qualified calls use '::' between the module "
                         "path and the function name, not '.'. Did you mean to "
                         "use '::' syntax?",
          'location': {'line': 6, 'column': 6, 'file': 'main.vera'},
          'source_line': '  m.g(@Int.0)',
          'rationale': "Vera uses '::' to separate the module path from the "
                       'function name in module-qualified calls. The '
                       'dot-separated module path is ambiguous with the '
                       "function name in an LALR(1) grammar, so '::' provides "
                       'an unambiguous delimiter.',
          'fix': "Use '::' between the module path and the function name:\n"
                 '\n'
                 '  vera.math::abs(-5)\n'
                 '  collections::sort([3, 1, 2])',
          'spec_ref': 'Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
          'error_code': 'E008'}])


def test_e008_a_dotted_module_call(tmp_path: Path) -> None:
    """module_call_dot_syntax: a two-segment module path."""
    assert _found(
        pipeline.check(_E008_A_DOTTED_MODULE_CALL, file="main.vera"),
        "E008", tmp_path) == (
        [{'severity': 'error',
          'description': "Module-qualified calls use '::' between the module "
                         "path and the function name, not '.'. Did you mean to "
                         "use '::' syntax?",
          'location': {'line': 6, 'column': 16, 'file': 'main.vera'},
          'source_line': '  vera.math.abs(@Int.0)',
          'rationale': "Vera uses '::' to separate the module path from the "
                       'function name in module-qualified calls. The '
                       'dot-separated module path is ambiguous with the '
                       "function name in an LALR(1) grammar, so '::' provides "
                       'an unambiguous delimiter.',
          'fix': "Use '::' between the module path and the function name:\n"
                 '\n'
                 '  vera.math::abs(-5)\n'
                 '  collections::sort([3, 1, 2])',
          'spec_ref': 'Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
          'error_code': 'E008'}])


def test_e024_a_byte_that_is_not_utf8(tmp_path: Path) -> None:
    """source_not_utf8: a Latin-1 byte in a comment."""
    assert _found(
        _cli("check", _entry_bytes(tmp_path, _E024_A_BYTE_THAT_IS_NOT_UTF8)),
        "E024", tmp_path) == (
        [{'severity': 'error',
          'description': 'Source file is not valid UTF-8: the byte 0xFF at '
                         'offset 82 (line 6, column 6) does not begin a valid '
                         'UTF-8 sequence.',
          'location': {'line': 6, 'column': 6, 'file': '<tmp>/main.vera'},
          'source_line': '  -- �',
          'rationale': 'Vera source is UTF-8: every command reads the program, '
                       'and each module it imports, as UTF-8. A byte sequence '
                       'that is not UTF-8 names no character, so what the file '
                       'says is undefined; a file saved in another encoding, '
                       'such as Latin-1 or UTF-16, converts to UTF-8 with its '
                       'text unchanged.',
          'fix': 'Save the file as UTF-8: in its directory, `iconv -f '
                 'ISO-8859-1 -t UTF-8 main.vera > main.utf8.vera` writes a '
                 'UTF-8 copy, which then replaces main.vera. That command '
                 'reads the source as Latin-1 (ISO-8859-1); a source in '
                 'another encoding names its own after `-f`. In a string '
                 'literal, a character can also be written as an escape of its '
                 'code point, such as `\\u{E9}` for é.',
          'spec_ref': 'Chapter 1, Section 1.1 "Source Encoding"',
          'error_code': 'E024'}])


def test_e032_a_clause_after_effects(tmp_path: Path) -> None:
    """contract_clause_after_effects: an `ensures` after `effects`."""
    assert _found(
        pipeline.check(_E032_A_CLAUSE_AFTER_EFFECTS, file="main.vera"),
        "E032", tmp_path) == (
        [{'severity': 'error',
          'description': "Contract clause 'ensures' appears after the "
                         "'effects' clause. Every contract clause comes first, "
                         "then 'effects', then the body.",
          'location': {'line': 4, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(true)',
          'rationale': 'A function declaration has a fixed clause order: the '
                       "signature, then its contract clauses ('requires', "
                       "'ensures' and 'decreases') in any order among "
                       "themselves, then exactly one 'effects' clause, then "
                       "the body. Once 'effects' has been read the parser "
                       'expects the body, so a contract keyword here begins no '
                       'construct it can accept.',
          'fix': "Move the 'ensures(...)' clause above the 'effects' clause, "
                 'so the declaration reads: requires / ensures / decreases, '
                 'then effects, then the body in braces.',
          'spec_ref': 'Chapter 5, Section 5.2 "Function Declaration Syntax"',
          'error_code': 'E032'}])


def test_e032_a_requires_after_effects(tmp_path: Path) -> None:
    """contract_clause_after_effects: a `requires` after `effects`."""
    assert _found(
        pipeline.check(_E032_A_REQUIRES_AFTER_EFFECTS, file="main.vera"),
        "E032", tmp_path) == (
        [{'severity': 'error',
          'description': "Contract clause 'requires' appears after the "
                         "'effects' clause. Every contract clause comes first, "
                         "then 'effects', then the body.",
          'location': {'line': 4, 'column': 3, 'file': 'main.vera'},
          'source_line': '  requires(true)',
          'rationale': 'A function declaration has a fixed clause order: the '
                       "signature, then its contract clauses ('requires', "
                       "'ensures' and 'decreases') in any order among "
                       "themselves, then exactly one 'effects' clause, then "
                       "the body. Once 'effects' has been read the parser "
                       'expects the body, so a contract keyword here begins no '
                       'construct it can accept.',
          'fix': "Move the 'requires(...)' clause above the 'effects' clause, "
                 'so the declaration reads: requires / ensures / decreases, '
                 'then effects, then the body in braces.',
          'spec_ref': 'Chapter 5, Section 5.2 "Function Declaration Syntax"',
          'error_code': 'E032'}])


def test_e009_an_invalid_escape(tmp_path: Path) -> None:
    """_placed: an escape the literal does not have."""
    assert _found(
        pipeline.check(_E009_AN_INVALID_ESCAPE, file="main.vera"),
        "E009", tmp_path) == (
        [{'severity': 'error',
          'description': 'Invalid escape sequence: \\q',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  "bad \\q escape"',
          'rationale': 'Vera strings accept a closed set of escape sequences '
                       'so string literals are unambiguous; an unrecognised '
                       'escape is more likely a typo than an intention, and '
                       "silently passing it through would change the string's "
                       'meaning.',
          'fix': 'Use one of the valid escapes — \\\\, \\", \\n, \\t, \\r, '
                 '\\0, \\u{XXXX} (1-6 hex digits), or \\( for interpolation — '
                 'or escape the backslash itself (\\\\) if a literal backslash '
                 'is intended.',
          'spec_ref': 'Chapter 1, Section 1.6 "Literals"',
          'error_code': 'E009'}])


def test_e009_an_empty_interpolation(tmp_path: Path) -> None:
    """_placed: an interpolation with nothing in it."""
    assert _found(
        pipeline.check(_E009_AN_EMPTY_INTERPOLATION, file="main.vera"),
        "E009", tmp_path) == (
        [{'severity': 'error',
          'description': "Empty expression in string interpolation '\\()'.",
          'location': {'line': 6, 'column': 6, 'file': 'main.vera'},
          'source_line': '  "a \\() b"',
          'rationale': 'String interpolation embeds a full Vera expression '
                       'inside \\(...); a malformed or empty segment cannot be '
                       'parsed as one, so the string has no well-defined '
                       'value.',
          'fix': 'Close every \\( with a matching ) and put exactly one '
                 'expression (not a statement) inside it.',
          'spec_ref': 'Chapter 4, Section 4.13.1 "String Interpolation"',
          'error_code': 'E009'}])


def test_e040_a_pipe_into_a_literal(tmp_path: Path) -> None:
    """_placed: `|>` whose right is no call."""
    assert _found(
        pipeline.check(_E040_A_PIPE_INTO_A_LITERAL, file="main.vera"),
        "E040", tmp_path) == (
        [{'severity': 'error',
          'description': "The right operand of '|>' must be a call; this one "
                         'is an integer literal.',
          'location': {'line': 6, 'column': 13, 'file': 'main.vera'},
          'source_line': '  @Int.0 |> 1',
          'rationale': "'a |> f(b)' is the call 'f(a, b)': the pipe passes its "
                       'left operand as the first argument of the call on its '
                       'right.  Only a call written with its argument list — a '
                       'function, a built-in, a constructor, an effect '
                       'operation or a module-qualified function — has an '
                       'argument list for the piped value to join.',
          'fix': "Write the right operand as a call, as in 'a |> abs()', or "
                 "apply the function directly: 'abs(a)'.  Every other operator "
                 "binds tighter than '|>', so 'a |> f() + 1' pipes into 'f() + "
                 "1'; write '(a |> f()) + 1' to add to the call's result.  To "
                 "chain calls, write the stages in order: 'a |> f() |> g()' is "
                 "'g(f(a))'.",
          'spec_ref': 'Chapter 4, Section 4.11.2 "Pipe Operator"',
          'error_code': 'E040'}])


def test_e011_a_circular_import(tmp_path: Path) -> None:
    """ModuleResolver._placed: a cycle of imports."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E011_A_CIRCULAR_IMPORT)),
        "E011", tmp_path) == (
        [{'severity': 'error',
          'description': "Circular import detected: 'a' is already being "
                         'resolved.',
          'location': {'line': 1, 'column': 1, 'file': '<tmp>/main.vera'},
          'source_line': 'import a;',
          'rationale': 'Circular imports are not allowed. The module '
                       'dependency graph must be acyclic.',
          'fix': 'Break the cycle: remove one of the imports, or extract the '
                 'shared declarations into a third module that both modules '
                 'import.',
          'spec_ref': 'Chapter 8, Section 8.6.3 "Circular Import Detection"',
          'error_code': 'E011'}])


def test_e012_an_import_with_no_file(tmp_path: Path) -> None:
    """ModuleResolver._placed: no such module."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E012_AN_IMPORT_WITH_NO_FILE)),
        "E012", tmp_path) == (
        [{'severity': 'error',
          'description': "Cannot resolve import 'nothere': no file found.",
          'location': {'line': 1, 'column': 1, 'file': '<tmp>/main.vera'},
          'source_line': 'import nothere;',
          'rationale': "Looked for 'nothere.vera' relative to the importing "
                       'file and project root.',
          'fix': "Create the file 'nothere.vera' or check the import path.",
          'spec_ref': 'Chapter 8, Section 8.6.1 "Path Mapping"',
          'error_code': 'E012'}])


def test_e013_an_imported_module_that_does_not_parse(tmp_path: Path) -> None:
    """ModuleResolver._placed: the module's parse error, named at the import."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E013_AN_IMPORTED_MODULE_THAT_DOES_NOT_PARSE)),
        "E013", tmp_path) == (
        [{'severity': 'error',
          'description': "Error parsing imported module 'a': [E005] Error at "
                         '<tmp>/a.vera, line 7, column 1:\n'
                         '\n'
                         '    }\n'
                         '    ^\n'
                         '\n'
                         '  Unexpected "}" at this position. Expected one of: '
                         '"!", "(", "-", "?", "@", "[", "{", FLOAT_LIT, ...\n'
                         '\n'
                         '  The parser reached this position expecting one of '
                         'the listed tokens; the token found does not begin '
                         'any construct valid here.\n'
                         '\n'
                         '  Fix:\n'
                         '\n'
                         '    Replace the unexpected token with one of the '
                         'expected tokens, or check for a missing delimiter '
                         "(such as '}', ')', or ',') earlier in the "
                         'construct.\n'
                         '\n'
                         '  See: Chapter 10, "Formal Grammar"',
          'location': {'line': 1, 'column': 1, 'file': '<tmp>/main.vera'},
          'source_line': 'import a;',
          'rationale': 'An imported module must itself parse and transform '
                       'successfully before its declarations can be used by '
                       'the importing program.',
          'fix': 'Run `vera check a.vera` directly to see the detailed syntax '
                 'diagnostic, then correct the imported module.',
          'spec_ref': 'Chapter 8, Section 8.6.5 "Resolution Errors"',
          'error_code': 'E013'}])


def test_e135_written_map_key(tmp_path: Path) -> None:
    """_refuse_array_component: written map key."""
    assert _found(
        pipeline.check(_E135_WRITTEN_MAP_KEY, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "'Map' with an Array key type 'Array<Int>' is not "
                         'supported.',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  let @Map<Array<Int>, Int> = map_new();',
          'rationale': 'A Map key is stored through an operation generated for '
                       'its representation, and none is generated for an '
                       'Array, a (ptr, len) pair, so the map operations would '
                       'not compile.',
          'fix': 'Key the map by a type it compares by content, such as '
                 "String, the array's show text: replace 'Map<Array<Int>, "
                 "Int>' with 'Map<String, Int>'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_written_map_value(tmp_path: Path) -> None:
    """_refuse_array_component: written map value."""
    assert _found(
        pipeline.check(_E135_WRITTEN_MAP_VALUE, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "'Map' with an Array value type 'Array<Int>' is not "
                         'supported.',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  let @Map<String, Array<Int>> = map_new();',
          'rationale': 'A Map value is stored through an operation generated '
                       'for its representation, and none is generated for an '
                       'Array, a (ptr, len) pair, so the map operations would '
                       'not compile.',
          'fix': 'Store the array by reference, in an Option, which a map '
                 "holds as a value: replace 'Map<String, Array<Int>>' with "
                 "'Map<String, Option<Array<Int>>>'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_written_set_element(tmp_path: Path) -> None:
    """_refuse_array_component: written set element."""
    assert _found(
        pipeline.check(_E135_WRITTEN_SET_ELEMENT, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "'Set' with an Array element type 'Array<Int>' is not "
                         'supported.',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  let @Set<Array<Int>> = set_new();',
          'rationale': 'A Set element is stored through an operation generated '
                       'for its representation, and none is generated for an '
                       'Array, a (ptr, len) pair, so the set operations would '
                       'not compile.',
          'fix': 'Hold the set by a type it compares by content, such as '
                 "String, the array's show text: replace 'Set<Array<Int>>' "
                 "with 'Set<String>'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_a_map_whose_key_and_value_are_both_arrays(tmp_path: Path) -> None:
    """_refuse_array_component: each component replaced by its position."""
    assert _found(
        pipeline.check(_E135_A_MAP_WHOSE_KEY_AND_VALUE_ARE_BOTH_ARRAYS, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "'Map' with an Array key type 'Array<Int>' is not "
                         'supported.',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  let @Map<Array<Int>, Array<Int>> = map_new();',
          'rationale': 'A Map key is stored through an operation generated for '
                       'its representation, and none is generated for an '
                       'Array, a (ptr, len) pair, so the map operations would '
                       'not compile.',
          'fix': 'Key the map by a type it compares by content, such as '
                 "String, the array's show text: replace 'Map<Array<Int>, "
                 "Array<Int>>' with 'Map<String, Array<Int>>'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'},
         {'severity': 'error',
          'description': "'Map' with an Array value type 'Array<Int>' is not "
                         'supported.',
          'location': {'line': 6, 'column': 8, 'file': 'main.vera'},
          'source_line': '  let @Map<Array<Int>, Array<Int>> = map_new();',
          'rationale': 'A Map value is stored through an operation generated '
                       'for its representation, and none is generated for an '
                       'Array, a (ptr, len) pair, so the map operations would '
                       'not compile.',
          'fix': 'Store the array by reference, in an Option, which a map '
                 "holds as a value: replace 'Map<Array<Int>, Array<Int>>' with "
                 "'Map<Array<Int>, Option<Array<Int>>>'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_inferred_map_key(tmp_path: Path) -> None:
    """typed._diagnostic, _component_fix: inferred map key."""
    assert _found(
        pipeline.check(_E135_INFERRED_MAP_KEY, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "The 'map_insert' call's key is 'Array<Int>', an "
                         'Array, and code generation lowers no Map or Set '
                         'operation over an Array.',
          'location': {'line': 6, 'column': 23, 'file': 'main.vera'},
          'source_line': '  nat_to_int(map_size(map_insert(map_new(), [1, 2], '
                         '5)))',
          'rationale': 'A Map or Set operation is lowered through an operation '
                       'generated for the representation of its key, value or '
                       'element, and none is generated for an Array (a (ptr, '
                       'len) pair) or for a type with no value (Unit, or a '
                       'Future of one).  A component typed by a type parameter '
                       'is judged at each type it is instantiated at, at the '
                       'call whose arguments choose it.',
          'fix': "Key the map by the value's show text, which it compares by "
                 "content: replace 'map_insert(map_new(), [1, 2], 5)' with "
                 "'map_insert(map_new(), show([1, 2]), 5)'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_inferred_map_value(tmp_path: Path) -> None:
    """typed._diagnostic, _component_fix: inferred map value."""
    assert _found(
        pipeline.check(_E135_INFERRED_MAP_VALUE, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "The 'map_insert' call's value is 'Array<Int>', an "
                         'Array, and code generation lowers no Map or Set '
                         'operation over an Array.',
          'location': {'line': 6, 'column': 23, 'file': 'main.vera'},
          'source_line': '  nat_to_int(map_size(map_insert(map_new(), "k", [1, '
                         '2])))',
          'rationale': 'A Map or Set operation is lowered through an operation '
                       'generated for the representation of its key, value or '
                       'element, and none is generated for an Array (a (ptr, '
                       'len) pair) or for a type with no value (Unit, or a '
                       'Future of one).  A component typed by a type parameter '
                       'is judged at each type it is instantiated at, at the '
                       'call whose arguments choose it.',
          'fix': 'Store the value by reference in an Option: replace '
                 '\'map_insert(map_new(), "k", [1, 2])\' with '
                 '\'map_insert(map_new(), "k", Some([1, 2]))\'.',
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_inferred_set_element(tmp_path: Path) -> None:
    """typed._diagnostic, _component_fix: inferred set element."""
    assert _found(
        pipeline.check(_E135_INFERRED_SET_ELEMENT, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "The 'set_add' call's element is 'Array<Int>', an "
                         'Array, and code generation lowers no Map or Set '
                         'operation over an Array.',
          'location': {'line': 6, 'column': 23, 'file': 'main.vera'},
          'source_line': '  nat_to_int(set_size(set_add(set_new(), [1, 2])))',
          'rationale': 'A Map or Set operation is lowered through an operation '
                       'generated for the representation of its key, value or '
                       'element, and none is generated for an Array (a (ptr, '
                       'len) pair) or for a type with no value (Unit, or a '
                       'Future of one).  A component typed by a type parameter '
                       'is judged at each type it is instantiated at, at the '
                       'call whose arguments choose it.',
          'fix': "Hold the set by the value's show text, which it compares by "
                 "content: replace 'set_add(set_new(), [1, 2])' with "
                 "'set_add(set_new(), show([1, 2]))'.",
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e135_inferred_zero_size_value(tmp_path: Path) -> None:
    """typed._diagnostic, _component_fix: inferred zero size value."""
    assert _found(
        pipeline.check(_E135_INFERRED_ZERO_SIZE_VALUE, file="main.vera"),
        "E135", tmp_path) == (
        [{'severity': 'error',
          'description': "The 'map_insert' call's value is 'Unit', a zero-size "
                         'type, and code generation lowers no Map or Set '
                         'operation over a zero-size type.',
          'location': {'line': 6, 'column': 23, 'file': 'main.vera'},
          'source_line': '  nat_to_int(map_size(map_insert(map_new(), "k", '
                         '())))',
          'rationale': 'A Map or Set operation is lowered through an operation '
                       'generated for the representation of its key, value or '
                       'element, and none is generated for an Array (a (ptr, '
                       'len) pair) or for a type with no value (Unit, or a '
                       'Future of one).  A component typed by a type parameter '
                       'is judged at each type it is instantiated at, at the '
                       'call whose arguments choose it.',
          'fix': 'Store the value by reference in an Option: replace '
                 '\'map_insert(map_new(), "k", ())\' with '
                 '\'map_insert(map_new(), "k", Some(()))\'.',
          'spec_ref': 'Chapter 9, Section 9.4 "Built-in Collections"',
          'error_code': 'E135'}])


def test_e613_an_ord_constraint_at_bool(tmp_path: Path) -> None:
    """typed._diagnostic: E613 at a call."""
    assert _found(
        pipeline.check(_E613_AN_ORD_CONSTRAINT_AT_BOOL, file="main.vera"),
        "E613", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'lt(true, false)' instantiates 'lt' at T = "
                         "Bool, where type 'Bool' does not satisfy ability "
                         "'Ord', which 'lt' requires of T: only the orderable "
                         'primitive types (Int, Nat, Float64, String, Byte) '
                         'support Ord.',
          'location': {'line': 17, 'column': 6, 'file': 'main.vera'},
          'source_line': '  if lt(true, false) then {',
          'rationale': "A generic's ability constraint holds for every type "
                       'argument it is instantiated at.  The check infers each '
                       "call's type arguments and holds each constraint "
                       'against the type it is instantiated at, at the call '
                       'whose arguments choose it.',
          'fix': "Instantiate 'lt' at a type that supports 'Ord', Int for "
                 "example: replace 'lt(true, false)' with 'lt(0, 0)'.",
          'spec_ref': 'Chapter 9, Section 9.8 "Abilities"',
          'error_code': 'E613'}])


def test_e613_an_eq_constraint_at_an_array(tmp_path: Path) -> None:
    """typed._diagnostic: E613, Eq."""
    assert _found(
        pipeline.check(_E613_AN_EQ_CONSTRAINT_AT_AN_ARRAY, file="main.vera"),
        "E613", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'same([1], [1])' instantiates 'same' at T = "
                         "Array<Int>, where type 'Array<Int>' does not satisfy "
                         "ability 'Eq', which 'same' requires of T: only "
                         'primitive types (Int, Bool, Float64, String, Byte, '
                         'Nat, Unit) and ADTs whose fields are themselves Eq '
                         '(structural derivation) support Eq.',
          'location': {'line': 14, 'column': 3, 'file': 'main.vera'},
          'source_line': '  same([1], [1])',
          'rationale': "A generic's ability constraint holds for every type "
                       'argument it is instantiated at.  The check infers each '
                       "call's type arguments and holds each constraint "
                       'against the type it is instantiated at, at the call '
                       'whose arguments choose it.',
          'fix': "Instantiate 'same' at a type that supports 'Eq', Int for "
                 "example: replace 'same([1], [1])' with 'same(0, 0)'.",
          'spec_ref': 'Chapter 9, Section 9.8 "Abilities"',
          'error_code': 'E613'}])


def test_e613_a_variable_no_argument_fixes(tmp_path: Path) -> None:
    """typed._call_fix: E613 at a variable no argument mentions."""
    assert _found(
        pipeline.check(_E613_A_VARIABLE_NO_ARGUMENT_FIXES, file="main.vera"),
        "E613", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'none_ord(())' instantiates 'none_ord' at T "
                         "= Bool, where type 'Bool' does not satisfy ability "
                         "'Ord', which 'none_ord' requires of T: only the "
                         'orderable primitive types (Int, Nat, Float64, '
                         'String, Byte) support Ord.',
          'location': {'line': 14, 'column': 9, 'file': 'main.vera'},
          'source_line': '  match none_ord(()) {',
          'rationale': "A generic's ability constraint holds for every type "
                       'argument it is instantiated at.  The check infers each '
                       "call's type arguments and holds each constraint "
                       'against the type it is instantiated at, at the call '
                       'whose arguments choose it.',
          'fix': "No argument of 'none_ord(())' fixes T, so the call "
                 "instantiates 'none_ord' at Bool, nothing giving its result a "
                 "type: bind its result at a type that supports 'Ord' (a `let` "
                 "of that type), or give 'none_ord' a parameter that carries T "
                 "('@T' for example) and pass it a value at a type that "
                 "supports 'Ord', Int for example.",
          'spec_ref': 'Chapter 9, Section 9.8 "Abilities"',
          'error_code': 'E613'}])


def test_e607_a_state_cell_at_a_string(tmp_path: Path) -> None:
    """typed._diagnostic: E607."""
    assert _found(
        pipeline.check(_E607_A_STATE_CELL_AT_A_STRING, file="main.vera"),
        "E607", tmp_path) == (
        [{'severity': 'error',
          'description': 'The call \'f("abc")\' instantiates \'f\' at T = '
                         'String, where its State<T> cell is a State<String>, '
                         'which code generation cannot lower: its value is a '
                         "(ptr, len) pair, and a cell's host imports carry one "
                         'word.',
          'location': {'line': 19, 'column': 3, 'file': 'main.vera'},
          'source_line': '  f("abc")',
          'rationale': "A State<T> cell's value crosses host imports that "
                       'carry one word, so a cell whose value is a (ptr, len) '
                       'pair (String, Array<T>) or has no representation '
                       '(Unit, Never) is not lowered.  A cell typed by a type '
                       'parameter is judged at each type it is instantiated '
                       'at, at the call whose arguments choose it.',
          'fix': "Instantiate 'f' at a type that a State cell holds, Int for "
                 'example: replace \'f("abc")\' with \'f(0)\'.',
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E607'}])


def test_e612_an_exception_payload_at_unit(tmp_path: Path) -> None:
    """typed._diagnostic: E612."""
    assert _found(
        pipeline.check(_E612_AN_EXCEPTION_PAYLOAD_AT_UNIT, file="main.vera"),
        "E612", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'g(())' instantiates 'g' at T = Unit, where "
                         'its Exn<T> payload is an Exn<Unit>, which code '
                         'generation cannot lower: Unit has no runtime '
                         'representation to throw.',
          'location': {'line': 18, 'column': 3, 'file': 'main.vera'},
          'source_line': '  g(())',
          'rationale': "An Exn<E> payload is thrown as a WebAssembly tag's "
                       'parameters, so a payload with no representation (Unit, '
                       'Never) has nothing to throw.  A payload typed by a '
                       'type parameter is judged at each type it is '
                       'instantiated at, at the call whose arguments choose '
                       'it.',
          'fix': "Instantiate 'g' at a type that an Exn payload carries, Int "
                 "for example: replace 'g(())' with 'g(0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E612'}])


def test_e533_a_state_declared_at_another_type(tmp_path: Path) -> None:
    """typed._state_fix: the replacement at the generic's parameter."""
    assert _found(
        pipeline.check(_E533_A_STATE_DECLARED_AT_ANOTHER_TYPE, file="main.vera"),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak(@Int.0)' instantiates 'sneak' at T = "
                         "Int, where its handler's state is declared @Nat but "
                         'its cell is State<Int>.',
          'location': {'line': 20, 'column': 3, 'file': 'main.vera'},
          'source_line': '  sneak(@Int.0)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'},
         {'severity': 'error',
          'description': "The call 'sneak(@Float64.0)' instantiates 'sneak' at "
                         "T = Float64, where its handler's state is declared "
                         '@Nat but its cell is State<Float64>.',
          'location': {'line': 19, 'column': 18, 'file': 'main.vera'},
          'source_line': '  let @Float64 = sneak(@Float64.0);',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_import_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_import probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_import.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak(@Int.0)' instantiates 'sneak' at T = "
                         "Int, where its handler's state is declared @Nat but "
                         'its cell is State<Int>.',
          'location': {'line': 8,
                       'column': 3,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_import.vera'},
          'source_line': '  sneak(@Int.0)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_indirect_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_indirect probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_indirect.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'outer(@Int.0)' instantiates 'outer' at T = "
                         "Int, which calls 'sneak' at T = Int, where its "
                         "handler's state is declared @Nat but its cell is "
                         'State<Int>.',
          'location': {'line': 27,
                       'column': 3,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_indirect.vera'},
          'source_line': '  outer(@Int.0)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_match_arm_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_match_arm probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_match_arm.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak(@Int.0, true)' instantiates 'sneak' "
                         "at T = Int, where its handler's state is declared "
                         '@Nat but its cell is State<Int>.',
          'location': {'line': 24,
                       'column': 3,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_match_arm.vera'},
          'source_line': '  sneak(@Int.0, true)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_mixed_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_mixed probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_mixed.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak(@Nat.0)' instantiates 'sneak' at T = "
                         "Nat, where its handler's state is declared @Int but "
                         'its cell is State<Nat>.',
          'location': {'line': 19,
                       'column': 14,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_mixed.vera'},
          'source_line': '  let @Nat = sneak(@Nat.0);',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Int = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_nat_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_nat probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_nat.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak(@Int.0)' instantiates 'sneak' at T = "
                         "Int, where its handler's state is declared @Nat but "
                         'its cell is State<Int>.',
          'location': {'line': 19,
                       'column': 3,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_nat.vera'},
          'source_line': '  sneak(@Int.0)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_two_fail_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_two_fail probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_two_fail.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak(@Int.0)' instantiates 'sneak' at T = "
                         "Int, where its handler's state is declared @Nat but "
                         'its cell is State<Int>.',
          'location': {'line': 20,
                       'column': 3,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_two_fail.vera'},
          'source_line': '  sneak(@Int.0)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'},
         {'severity': 'error',
          'description': "The call 'sneak(@Float64.0)' instantiates 'sneak' at "
                         "T = Float64, where its handler's state is declared "
                         '@Nat but its cell is State<Float64>.',
          'location': {'line': 19,
                       'column': 18,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_two_fail.vera'},
          'source_line': '  let @Float64 = sneak(@Float64.0);',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e533_where_probe(tmp_path: Path) -> None:
    """typed._state_fix: the e533_where probe."""
    assert _found(
        pipeline.check(ROOT / 'tests/probes/state_handlers/checker_gates/e533_where.vera'),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'ghelper(@Int.0)' instantiates 'ghelper' at "
                         "T = Int, where its handler's state is declared @Nat "
                         'but its cell is State<Int>.',
          'location': {'line': 6,
                       'column': 3,
                       'file': '<root>/tests/probes/state_handlers/checker_gates/e533_where.vera'},
          'source_line': '  ghelper(@Int.0)',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, the type "
                 "parameter T, so every instantiation's state is its cell: "
                 "replace '(@Nat = 3)' with '(@T = @T.0)'.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e139_a_mutual_cycle(tmp_path: Path) -> None:
    """typed._growth_diagnostic, _growth_fix: mutual."""
    assert _found(
        pipeline.check(_E139_A_MUTUAL_CYCLE, file="main.vera"),
        "E139", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'g(Some(@T.0), @Nat.0 - 1)' in 'f' "
                         "instantiates 'g' at U = Option<T>, and the cycle of "
                         'calls it closes grows that type at every turn: f<T> '
                         '-> g<Option<T>> -> f<Option<Option<T>>> -> ..., so '
                         'no finite set of instances compiles the program.',
          'location': {'line': 10, 'column': 5, 'file': 'main.vera'},
          'source_line': '    g(Some(@T.0), @Nat.0 - 1)',
          'rationale': 'A generic is compiled once for each type it is '
                       'instantiated at.  A call that instantiates a generic '
                       'of its own cycle of calls at a type strictly larger '
                       "than one of the cycle's type variables needs, for "
                       'every instance, an instance at a larger type, so the '
                       'instances never end and no module can hold them: the '
                       "rule a data declaration's recursion keeps (E129).",
          'fix': "Call 'g' at the caller's type variable itself, not at a type "
                 'built from it, or carry the nesting in a value of a '
                 "recursive data type: replace 'g(Some(@T.0), @Nat.0 - 1)' "
                 "with 'g(@T.0, @Nat.0 - 1)'.",
          'spec_ref': 'Chapter 11, Section 11.4.1 "Compilable Subset"',
          'error_code': 'E139'},
         {'severity': 'error',
          'description': "The call 'f(Some(@U.0), @Nat.0 - 1)' in 'g' "
                         "instantiates 'f' at T = Option<U>, and the cycle of "
                         'calls it closes grows that type at every turn: g<U> '
                         '-> f<Option<U>> -> g<Option<Option<U>>> -> ..., so '
                         'no finite set of instances compiles the program.',
          'location': {'line': 23, 'column': 5, 'file': 'main.vera'},
          'source_line': '    f(Some(@U.0), @Nat.0 - 1)',
          'rationale': 'A generic is compiled once for each type it is '
                       'instantiated at.  A call that instantiates a generic '
                       'of its own cycle of calls at a type strictly larger '
                       "than one of the cycle's type variables needs, for "
                       'every instance, an instance at a larger type, so the '
                       'instances never end and no module can hold them: the '
                       "rule a data declaration's recursion keeps (E129).",
          'fix': "Call 'f' at the caller's type variable itself, not at a type "
                 'built from it, or carry the nesting in a value of a '
                 "recursive data type: replace 'f(Some(@U.0), @Nat.0 - 1)' "
                 "with 'f(@U.0, @Nat.0 - 1)'.",
          'spec_ref': 'Chapter 11, Section 11.4.1 "Compilable Subset"',
          'error_code': 'E139'}])


def test_e139_a_self_cycle(tmp_path: Path) -> None:
    """typed._growth_diagnostic, _growth_fix: self."""
    assert _found(
        pipeline.check(_E139_A_SELF_CYCLE, file="main.vera"),
        "E139", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'same_deep(Some(@T.1), Some(@T.0), @Nat.0 - "
                         "1)' in 'same_deep' instantiates 'same_deep' at T = "
                         'Option<T>, and the cycle of calls it closes grows '
                         'that type at every turn: same_deep<T> -> '
                         'same_deep<Option<T>> -> ..., so no finite set of '
                         'instances compiles the program.',
          'location': {'line': 10, 'column': 5, 'file': 'main.vera'},
          'source_line': '    same_deep(Some(@T.1), Some(@T.0), @Nat.0 - 1)',
          'rationale': 'A generic is compiled once for each type it is '
                       'instantiated at.  A call that instantiates a generic '
                       'of its own cycle of calls at a type strictly larger '
                       "than one of the cycle's type variables needs, for "
                       'every instance, an instance at a larger type, so the '
                       'instances never end and no module can hold them: the '
                       "rule a data declaration's recursion keeps (E129).",
          'fix': "Call 'same_deep' at the caller's type variable itself, not "
                 'at a type built from it, or carry the nesting in a value of '
                 "a recursive data type: replace 'same_deep(Some(@T.1), "
                 "Some(@T.0), @Nat.0 - 1)' with 'same_deep(@T.1, @T.0, @Nat.0 "
                 "- 1)'.",
          'spec_ref': 'Chapter 11, Section 11.4.1 "Compilable Subset"',
          'error_code': 'E139'}])


def test_e139_a_uncalled_cycle(tmp_path: Path) -> None:
    """typed._growth_diagnostic, _growth_fix: uncalled."""
    assert _found(
        pipeline.check(_E139_A_UNCALLED_CYCLE, file="main.vera"),
        "E139", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'deepen([@T.0], @Nat.0 - 1)' in 'deepen' "
                         "instantiates 'deepen' at T = Array<T>, and the cycle "
                         'of calls it closes grows that type at every turn: '
                         'deepen<T> -> deepen<Array<T>> -> ..., so no finite '
                         'set of instances compiles the program.',
          'location': {'line': 10, 'column': 5, 'file': 'main.vera'},
          'source_line': '    deepen([@T.0], @Nat.0 - 1)',
          'rationale': 'A generic is compiled once for each type it is '
                       'instantiated at.  A call that instantiates a generic '
                       'of its own cycle of calls at a type strictly larger '
                       "than one of the cycle's type variables needs, for "
                       'every instance, an instance at a larger type, so the '
                       'instances never end and no module can hold them: the '
                       "rule a data declaration's recursion keeps (E129).",
          'fix': "Call 'deepen' at the caller's type variable itself, not at a "
                 'type built from it, or carry the nesting in a value of a '
                 "recursive data type: replace 'deepen([@T.0], @Nat.0 - 1)' "
                 "with 'deepen(@T.0, @Nat.0 - 1)'.",
          'spec_ref': 'Chapter 11, Section 11.4.1 "Compilable Subset"',
          'error_code': 'E139'}])


def test_e139_a_growing_call_in_a_where_helper(tmp_path: Path) -> None:
    """typed._growth_diagnostic: the helper named."""
    assert _found(
        pipeline.check(_E139_A_GROWING_CALL_IN_A_WHERE_HELPER, file="main.vera"),
        "E139", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'gw(Some(@T.0), @Nat.0)' in 'helper' "
                         "instantiates 'gw' at T = Option<T>, and the cycle of "
                         'calls it closes grows that type at every turn: gw<T> '
                         '-> gw<Option<T>> -> ..., so no finite set of '
                         'instances compiles the program.',
          'location': {'line': 20, 'column': 5, 'file': 'main.vera'},
          'source_line': '    gw(Some(@T.0), @Nat.0)',
          'rationale': 'A generic is compiled once for each type it is '
                       'instantiated at.  A call that instantiates a generic '
                       'of its own cycle of calls at a type strictly larger '
                       "than one of the cycle's type variables needs, for "
                       'every instance, an instance at a larger type, so the '
                       'instances never end and no module can hold them: the '
                       "rule a data declaration's recursion keeps (E129).",
          'fix': "Call 'gw' at the caller's type variable itself, not at a "
                 'type built from it, or carry the nesting in a value of a '
                 "recursive data type: replace 'gw(Some(@T.0), @Nat.0)' with "
                 "'gw(@T.0, @Nat.0)'.",
          'spec_ref': 'Chapter 11, Section 11.4.1 "Compilable Subset"',
          'error_code': 'E139'}])


def test_e202_a_closure_compiled_at_its_own_type(tmp_path: Path) -> None:
    """_open_variable_refusal: the issue's closure."""
    assert _found(
        pipeline.check(_E202_A_CLOSURE_COMPILED_AT_ITS_OWN_TYPE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'use' has type fn(T -> T) "
                         'effects(pure), expected fn(Option<Nat> -> '
                         'Option<String>) effects(pure): no argument of the '
                         'call that made the closure gives T a type, so its '
                         'code was compiled at a type of its own, and the '
                         "parameter's type gives T Option<Nat> at the "
                         'parameter.',
          'location': {'line': 28, 'column': 7, 'file': 'main.vera'},
          'source_line': '  use(mk(()))',
          'rationale': 'A closure a generic call returns is compiled at the '
                       "types its call's arguments give its type variables; "
                       'one they give no type is compiled at a type of its '
                       'own, so the closure cannot stand where the parameter '
                       'asks another type for that variable.',
          'fix': "Write the closure at the parameter's type, `fn(@Option<Nat> "
                 '-> @Option<String>) effects(pure) { ... }`, and pass it in '
                 'place of `mk(())`.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e202_closure_diff_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: closure, diff, fixed nowhere."""
    assert _found(
        pipeline.check(_E202_CLOSURE_DIFF_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type fn(T -> T) "
                         'effects(pure), expected fn(Int -> String) '
                         'effects(pure): no argument of the call that made the '
                         'closure gives T a type, so its code was compiled at '
                         "a type of its own, and the parameter's type gives T "
                         'Int at the parameter.',
          'location': {'line': 29, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None))',
          'rationale': 'A closure a generic call returns is compiled at the '
                       "types its call's arguments give its type variables; "
                       'one they give no type is compiled at a type of its '
                       'own, so the closure cannot stand where the parameter '
                       'asks another type for that variable.',
          'fix': "Write the closure at the parameter's type, `fn(@Int -> "
                 '@String) effects(pure) { ... }`, and pass it in place of '
                 '`make(None)`.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e202_held_closure_diff_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: held_closure, diff, fixed nowhere."""
    assert _found(
        pipeline.check(_E202_HELD_CLOSURE_DIFF_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type Conv2<T, T>, expected "
                         'Conv2<Int, String>: no argument of the call that '
                         'made the value gives T a type, so a function a value '
                         'of this type holds is compiled at a type of its own, '
                         "and the parameter's type gives T Int at type "
                         'argument 1 of Conv2.',
          'location': {'line': 32, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None))',
          'rationale': 'A function a generic call builds is compiled at the '
                       "types its call's arguments give its type variables; "
                       'one they give no type is compiled at a type of its '
                       'own.  A value whose type holds a function over such a '
                       'variable may hold one compiled so, whatever this value '
                       'holds, so it cannot stand where the parameter asks '
                       'another type for that variable.',
          'fix': "Build the value at the parameter's type, writing any "
                 'function it holds at that type, in place of `make(None)`.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e202_fn_param_result_diff_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: fn_param_result, diff, fixed nowhere."""
    assert _found(
        pipeline.check(_E202_FN_PARAM_RESULT_DIFF_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type fn(Option<T> -> "
                         'Array<T>) effects(pure), expected fn(Option<Int> -> '
                         'Array<String>) effects(pure): no argument of the '
                         'call that made the closure gives T a type, so its '
                         'code was compiled at a type of its own, and the '
                         "parameter's type gives T Int at the type argument of "
                         'Option in the parameter.',
          'location': {'line': 29, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None))',
          'rationale': 'A closure a generic call returns is compiled at the '
                       "types its call's arguments give its type variables; "
                       'one they give no type is compiled at a type of its '
                       'own, so the closure cannot stand where the parameter '
                       'asks another type for that variable.',
          'fix': "Write the closure at the parameter's type, `fn(@Option<Int> "
                 '-> @Array<String>) effects(pure) { ... }`, and pass it in '
                 'place of `make(None)`.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e202_data_fields_diff_argument(tmp_path: Path) -> None:
    """_open_variable_refusal: data_fields, diff, fixed argument."""
    assert _found(
        pipeline.check(_E202_DATA_FIELDS_DIFF_ARGUMENT, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type Two<Int, Int>, "
                         'expected Two<Int, String>.',
          'location': {'line': 29, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(Some(@Int.0)))',
          'rationale': "Each argument's type must be a subtype of the "
                       'corresponding declared parameter type.',
          'fix': 'Pass a value of type `Two<Int, String>` for argument 0, or '
                 'convert the current value (e.g. int_to_nat(...), '
                 'int_to_float(...)) to `Two<Int, String>`.',
          'spec_ref': 'Chapter 5, Section 5.2 "Function Declaration Syntax"',
          'error_code': 'E202'}])


def test_e202_tuple_diff_argument(tmp_path: Path) -> None:
    """_open_variable_refusal: tuple, diff, fixed argument."""
    assert _found(
        pipeline.check(_E202_TUPLE_DIFF_ARGUMENT, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type Tuple<Option<Int>, "
                         'Option<Int>>, expected Tuple<Option<Int>, '
                         'Option<String>>.',
          'location': {'line': 31, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(Some(@Int.0)))',
          'rationale': "Each argument's type must be a subtype of the "
                       'corresponding declared parameter type.',
          'fix': 'Pass a value of type `Tuple<Option<Int>, Option<String>>` '
                 'for argument 0, or convert the current value (e.g. '
                 'int_to_nat(...), int_to_float(...)) to `Tuple<Option<Int>, '
                 'Option<String>>`.',
          'spec_ref': 'Chapter 5, Section 5.2 "Function Declaration Syntax"',
          'error_code': 'E202'}])


def test_e202_nested_diff_expected(tmp_path: Path) -> None:
    """_open_variable_refusal: nested, diff, fixed expected."""
    assert _found(
        pipeline.check(_E202_NESTED_DIFF_EXPECTED, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type "
                         'Tuple<Array<Option<Int>>, Option<Option<Int>>>, '
                         'expected Tuple<Array<Option<Int>>, '
                         'Option<Option<String>>>.',
          'location': {'line': 28, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(Some(5)))',
          'rationale': "Each argument's type must be a subtype of the "
                       'corresponding declared parameter type.',
          'fix': 'Pass a value of type `Tuple<Array<Option<Int>>, '
                 'Option<Option<String>>>` for argument 0, or convert the '
                 'current value (e.g. int_to_nat(...), int_to_float(...)) to '
                 '`Tuple<Array<Option<Int>>, Option<Option<String>>>`.',
          'spec_ref': 'Chapter 5, Section 5.2 "Function Declaration Syntax"',
          'error_code': 'E202'}])


def test_e202_closure_var_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: closure, var, fixed nowhere."""
    assert _found(
        pipeline.check(_E202_CLOSURE_VAR_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type fn(T -> T) "
                         'effects(pure), expected fn(Int -> ?) effects(pure): '
                         'no argument of the call that made the closure gives '
                         'T a type, so its code was compiled at a type of its '
                         "own, and the parameter's type gives T Int at the "
                         'parameter.',
          'location': {'line': 29, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None), None)',
          'rationale': 'A closure a generic call returns is compiled at the '
                       "types its call's arguments give its type variables; "
                       'one they give no type is compiled at a type of its '
                       'own, so the closure cannot stand where the parameter '
                       'asks another type for that variable.',
          'fix': "Write the closure at the parameter's type, with each of its "
                 'type variables fixed, and pass it in place of `make(None)`.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_w005_one_typed_hole(tmp_path: Path) -> None:
    """_holes_skip: a hole."""
    assert _found(
        pipeline.verify(_W005_ONE_TYPED_HOLE, file="main.vera", reconcile=True),
        "W005", tmp_path) == (
        [{'severity': 'warning',
          'description': 'The runtime checks are not reconciled: the program '
                         'holds a typed hole, and code generation compiles a '
                         'program only once every hole is filled (E614), so '
                         'there is no compiled module to hold its Tier 3 '
                         'claims to.',
          'location': {'line': 6, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ?',
          'rationale': '`vera verify` compiles the program in process and '
                       'joins each runtime-check claim (`tier3`, `timeout`) '
                       'with the check the compiled module holds for it.  A '
                       'typed hole has no runtime behaviour, so code '
                       'generation refuses the program, and the verification '
                       'of the rest of it stands on its own: every proof and '
                       "every disclosure above is the verifier's, and no Tier "
                       '3 claim has been held to a compiled check.',
          'fix': 'Fill each hole with an expression of the type its W001 '
                 'warning names; `vera verify` then compiles the program and '
                 'reconciles its runtime checks.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'W005'}])


def test_w005_two_typed_holes(tmp_path: Path) -> None:
    """_holes_skip: two holes."""
    assert _found(
        pipeline.verify(_W005_TWO_TYPED_HOLES, file="main.vera", reconcile=True),
        "W005", tmp_path) == (
        [{'severity': 'warning',
          'description': 'The runtime checks are not reconciled: the program '
                         'holds 2 typed holes, and code generation compiles a '
                         'program only once every hole is filled (E614), so '
                         'there is no compiled module to hold its Tier 3 '
                         'claims to.',
          'location': {'line': 6, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ?',
          'rationale': '`vera verify` compiles the program in process and '
                       'joins each runtime-check claim (`tier3`, `timeout`) '
                       'with the check the compiled module holds for it.  A '
                       'typed hole has no runtime behaviour, so code '
                       'generation refuses the program, and the verification '
                       'of the rest of it stands on its own: every proof and '
                       "every disclosure above is the verifier's, and no Tier "
                       '3 claim has been held to a compiled check.',
          'fix': 'Fill each hole with an expression of the type its W001 '
                 'warning names; `vera verify` then compiles the program and '
                 'reconciles its runtime checks.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'W005'}])


def test_e700_a_guard_on_an_admitted_input(tmp_path: Path) -> None:
    """run: E700, attributed."""
    assert _found(
        pipeline.contract_test(_E700_A_GUARD_ON_AN_ADMITTED_INPUT, file="main.vera", trials=9, distrust=True),
        "E700", tmp_path) == (
        [{'severity': 'error',
          'description': "Contract violation in 'pick': Array index out of "
                         'bounds (line 7): `@Array<Int>.0[@Nat.0]` needs `0 <= '
                         '@Nat.0` and `@Nat.0 < array_length(@Array<Int>.0)`.\n'
                         '  the runtime check of an obligation the verifier '
                         'did not prove: the index_bounds obligation on '
                         '`@Array<Int>.0[@Nat.0]` (line 7)',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn pick(@Nat -> @Nat)',
          'rationale': 'Contract-driven testing ran the compiled function on '
                       'Z3-generated inputs satisfying its `requires`; on a '
                       'real result it either violated an `ensures` clause or '
                       'trapped at runtime.',
          'fix': 'Correct the implementation so the postcondition holds, or '
                 'adjust the contract (strengthen `requires` / weaken '
                 '`ensures`) to match the intended behaviour.',
          'spec_ref': 'Chapter 6, "Contracts"',
          'error_code': 'E700'},
         {'severity': 'error',
          'description': "Contract violation in 'pick': Array index out of "
                         'bounds (line 7): `@Array<Int>.0[@Nat.0]` needs `0 <= '
                         '@Nat.0` and `@Nat.0 < array_length(@Array<Int>.0)`.\n'
                         '  the runtime check of an obligation the verifier '
                         'did not prove: the index_bounds obligation on '
                         '`@Array<Int>.0[@Nat.0]` (line 7)',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn pick(@Nat -> @Nat)',
          'rationale': 'Contract-driven testing ran the compiled function on '
                       'Z3-generated inputs satisfying its `requires`; on a '
                       'real result it either violated an `ensures` clause or '
                       'trapped at runtime.',
          'fix': 'Correct the implementation so the postcondition holds, or '
                 'adjust the contract (strengthen `requires` / weaken '
                 '`ensures`) to match the intended behaviour.',
          'spec_ref': 'Chapter 6, "Contracts"',
          'error_code': 'E700'},
         {'severity': 'error',
          'description': "Contract violation in 'pick': Array index out of "
                         'bounds (line 7): `@Array<Int>.0[@Nat.0]` needs `0 <= '
                         '@Nat.0` and `@Nat.0 < array_length(@Array<Int>.0)`.\n'
                         '  the runtime check of an obligation the verifier '
                         'did not prove: the index_bounds obligation on '
                         '`@Array<Int>.0[@Nat.0]` (line 7)',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn pick(@Nat -> @Nat)',
          'rationale': 'Contract-driven testing ran the compiled function on '
                       'Z3-generated inputs satisfying its `requires`; on a '
                       'real result it either violated an `ensures` clause or '
                       'trapped at runtime.',
          'fix': 'Correct the implementation so the postcondition holds, or '
                 'adjust the contract (strengthen `requires` / weaken '
                 '`ensures`) to match the intended behaviour.',
          'spec_ref': 'Chapter 6, "Contracts"',
          'error_code': 'E700'}])


def test_e700_a_guard_without_distrust(tmp_path: Path) -> None:
    """run: E700, no attribution."""
    assert _found(
        pipeline.contract_test(_E700_A_GUARD_WITHOUT_DISTRUST, file="main.vera", trials=9),
        "E700", tmp_path) == (
        [{'severity': 'error',
          'description': "Contract violation in 'tricky': Postcondition "
                         'violation in tricky(@Int -> @Int)\n'
                         '  ensures(exists(@Int, 1, fn(@Int -> @Bool) '
                         'effects(pure) { false })) failed',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn tricky(@Int -> @Int)',
          'rationale': 'Contract-driven testing ran the compiled function on '
                       'Z3-generated inputs satisfying its `requires`; on a '
                       'real result it either violated an `ensures` clause or '
                       'trapped at runtime.',
          'fix': 'Correct the implementation so the postcondition holds, or '
                 'adjust the contract (strengthen `requires` / weaken '
                 '`ensures`) to match the intended behaviour.',
          'spec_ref': 'Chapter 6, "Contracts"',
          'error_code': 'E700'},
         {'severity': 'error',
          'description': "Contract violation in 'tricky': Postcondition "
                         'violation in tricky(@Int -> @Int)\n'
                         '  ensures(exists(@Int, 1, fn(@Int -> @Bool) '
                         'effects(pure) { false })) failed',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn tricky(@Int -> @Int)',
          'rationale': 'Contract-driven testing ran the compiled function on '
                       'Z3-generated inputs satisfying its `requires`; on a '
                       'real result it either violated an `ensures` clause or '
                       'trapped at runtime.',
          'fix': 'Correct the implementation so the postcondition holds, or '
                 'adjust the contract (strengthen `requires` / weaken '
                 '`ensures`) to match the intended behaviour.',
          'spec_ref': 'Chapter 6, "Contracts"',
          'error_code': 'E700'},
         {'severity': 'error',
          'description': "Contract violation in 'tricky': Postcondition "
                         'violation in tricky(@Int -> @Int)\n'
                         '  ensures(exists(@Int, 1, fn(@Int -> @Bool) '
                         'effects(pure) { false })) failed',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn tricky(@Int -> @Int)',
          'rationale': 'Contract-driven testing ran the compiled function on '
                       'Z3-generated inputs satisfying its `requires`; on a '
                       'real result it either violated an `ensures` clause or '
                       'trapped at runtime.',
          'fix': 'Correct the implementation so the postcondition holds, or '
                 'adjust the contract (strengthen `requires` / weaken '
                 '`ensures`) to match the intended behaviour.',
          'spec_ref': 'Chapter 6, "Contracts"',
          'error_code': 'E700'}])


def test_e701_a_generator_that_cannot_serve_the_requires(tmp_path: Path) -> None:
    """run: E701, an untranslatable constraint."""
    assert _found(
        pipeline.contract_test(_E701_A_GENERATOR_THAT_CANNOT_SERVE_THE_REQUIRES, file="main.vera", trials=9, distrust=True),
        "E701", tmp_path) == (
        [{'severity': 'warning',
          'description': "Skipping test generation for 'h': cannot generate "
                         'inputs satisfying `is_small(@Int.0)` (see #1229).',
          'location': {'line': 9, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn h(@Int -> @Int)',
          'rationale': 'Contract-driven testing generates inputs with Z3 from '
                       "each parameter's type, its refinement predicate, and "
                       "the function's `requires` clauses. A constraint the "
                       'SMT layer cannot translate reaches the solver as '
                       'nothing at all, so the inputs it produces may violate '
                       'it and the compiled function traps on its own guard — '
                       'which is a limit of the generator, not a falsified '
                       'contract, so the function is skipped rather than '
                       'reported as failing.',
          'fix': 'Restate the constraint in terms the SMT layer models (for '
                 'example compare a `string_length` against a literal rather '
                 'than a computed value), or exercise this function with a '
                 'hand-written test instead.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E701'}])


def test_e701_no_input_within_the_bounds(tmp_path: Path) -> None:
    """run: E701, out of bounds."""
    assert _found(
        pipeline.contract_test(_E701_NO_INPUT_WITHIN_THE_BOUNDS, file="main.vera", trials=9, distrust=True),
        "E701", tmp_path) == (
        [{'severity': 'warning',
          'description': "Cannot generate test inputs for 'above_bound': no "
                         "input within the generator's bounds satisfies the "
                         'precondition, so its proof is not exercised.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn above_bound(@Int -> @Int)',
          'rationale': 'Contract-driven testing asks Z3 for inputs that '
                       'satisfy the precondition, drawing `@Int` and `@Nat` '
                       'from [-2^53, 2^53] and strings of at most 50 '
                       'characters.  It got none for this function, so `vera '
                       'test --distrust` has nothing to run the proved '
                       'function on.',
          'fix': 'Exercise this function with a hand-written test, or restate '
                 'the precondition so it admits inputs the generator reaches.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E701'}])


def test_e701_skipped_proofs(tmp_path: Path) -> None:
    """run: E701, a generic and an Option parameter."""
    assert _found(
        pipeline.contract_test(_E701_SKIPPED_PROOFS, file="main.vera", trials=9, distrust=True),
        "E701", tmp_path) == (
        [{'severity': 'warning',
          'description': "Cannot generate test inputs for 'opt_pos': the "
                         'generator encodes no Option<Int> value (see #169), '
                         'so its proof is not exercised.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn opt_pos(@Option<Int> -> @Int)',
          'rationale': 'Contract-driven testing generates each input with Z3 '
                       "from its parameter's type, and encodes only `Int`, "
                       '`Nat`, `Bool`, `Byte`, `String` and `Float64` values; '
                       'a type variable names no type to generate.  So `vera '
                       'test --distrust` has no input to run this proved '
                       'function on, and its proof stands but is not '
                       'exercised.',
          'fix': 'Exercise the proof through a public function whose '
                 'parameters the generator encodes and which calls this one — '
                 "its trials run this function's checks too — or with a "
                 'hand-written test.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E701'},
         {'severity': 'warning',
          'description': "Cannot generate test inputs for 'same': it is "
                         'generic, so its proof is not exercised.',
          'location': {'line': 12, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public forall<T> fn same(@T -> @T)',
          'rationale': 'Contract-driven testing generates each input with Z3 '
                       "from its parameter's type, and encodes only `Int`, "
                       '`Nat`, `Bool`, `Byte`, `String` and `Float64` values; '
                       'a type variable names no type to generate.  So `vera '
                       'test --distrust` has no input to run this proved '
                       'function on, and its proof stands but is not '
                       'exercised.',
          'fix': 'Exercise the proof through a public function whose '
                 'parameters the generator encodes and which calls this one — '
                 "its trials run this function's checks too — or with a "
                 'hand-written test.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E701'}])


def test_e702_a_program_that_does_not_compile(tmp_path: Path) -> None:
    """run: E702, compile errors."""
    assert _found(
        pipeline.contract_test(_E702_A_PROGRAM_THAT_DOES_NOT_COMPILE, file="main.vera", trials=9, distrust=True),
        "E702", tmp_path) == (
        [{'severity': 'warning',
          'description': "Cannot run 'add1' to test its proof: compilation "
                         'errors.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn add1(@Int -> @Int)',
          'rationale': '`vera test --distrust` executes the functions the '
                       'verifier proved, and this one has no executable form '
                       'in the compiled module, so its proof stands but is not '
                       'exercised.',
          'fix': 'Run `vera compile` on the program and resolve the error it '
                 'reports, or the code generation warning the reason names; '
                 'the function then compiles and its proof is run.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E702'}])


@pytest.mark.usefixtures("injected_false_proof")
def test_e702_a_proof_no_check_stands_for(tmp_path: Path) -> None:
    """run: E702, no check."""
    assert _found(
        pipeline.contract_test(_E702_A_PROOF_NO_CHECK_STANDS_FOR, file="main.vera", trials=9, distrust=True),
        "E702", tmp_path) == (
        [{'severity': 'warning',
          'description': "Cannot test the proof of 's': code generation emits "
                         'no runtime check for `ensures(@String.result == '
                         '"neg")`.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn s(@Int -> @String)',
          'rationale': '`vera test --distrust` tests a proof by running the '
                       'function against the runtime checks code generation '
                       'emits for what the verifier proved: its contract '
                       'clauses, the operations in its body, and those of the '
                       'functions it calls.  A run of this function reaches '
                       'none — code generation emits no check for a '
                       'postcondition over a `String` or `Array` result, nor '
                       'for a clause it cannot compile, and a `requires` is '
                       'met by the generated arguments — so no trial can '
                       'contradict the proof, and the function is not run: its '
                       'proof stands but is not exercised.',
          'fix': 'Exercise the property through a caller whose own contract '
                 'has a check — a function returning an `Int` computed from '
                 "this one's result, with an `ensures` over that value — or "
                 'with a hand-written test.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E702'}])


def test_e702_only_a_requires(tmp_path: Path) -> None:
    """run: E702, only a requires."""
    assert _found(
        pipeline.contract_test(_E702_ONLY_A_REQUIRES, file="main.vera", trials=9, distrust=True),
        "E702", tmp_path) == (
        [{'severity': 'warning',
          'description': "Cannot test the proof of 'keep': no runtime check a "
                         'run of it reaches stands for an obligation the '
                         'verifier proved.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn keep(@Int -> @Int)',
          'rationale': '`vera test --distrust` tests a proof by running the '
                       'function against the runtime checks code generation '
                       'emits for what the verifier proved: its contract '
                       'clauses, the operations in its body, and those of the '
                       'functions it calls.  A run of this function reaches '
                       'none — code generation emits no check for a '
                       'postcondition over a `String` or `Array` result, nor '
                       'for a clause it cannot compile, and a `requires` is '
                       'met by the generated arguments — so no trial can '
                       'contradict the proof, and the function is not run: its '
                       'proof stands but is not exercised.',
          'fix': 'Exercise the property through a caller whose own contract '
                 'has a check — a function returning an `Int` computed from '
                 "this one's result, with an `ensures` over that value — or "
                 'with a hand-written test.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E702'}])


@pytest.mark.usefixtures("injected_false_proof")
def test_e703_a_false_proof(tmp_path: Path) -> None:
    """run: E703, the refuted proof."""
    assert _found(
        pipeline.contract_test(_E703_A_FALSE_PROOF, file="main.vera", trials=9, distrust=True),
        "E703", tmp_path) == (
        [{'severity': 'error',
          'description': "Tier 1 proof refuted in 'main': ensures(@Int.result "
                         '< 0) was proved, but the trial on no arguments '
                         'failed it at run time: Postcondition violation in '
                         'main( -> @Int)',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result < 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       "discharged at Tier 1, and the trial's arguments "
                       "satisfy the function's `requires` in the verifier's "
                       'own model, so the proof and the compiled program '
                       'disagree: unless an `assume` the proof rests on is '
                       'false, the verifier proved something about a program '
                       'other than the one that runs.',
          'fix': 'If a callee this proof relies on contains an `assume`, check '
                 'that first: an `assume` is taken on trust (W003), so a false '
                 'one lets the verifier prove a contract the program then '
                 'violates.  Otherwise this is a soundness defect in Vera, not '
                 'in the program: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.  Until it is fixed, treat the '
                 'obligation as checked at run time rather than proved: the '
                 'compiled program carries the check, so it traps here instead '
                 'of continuing past the violation.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'}])


def test_e136_fn_is_not_a_type(tmp_path: Path) -> None:
    """_unknown_type_advice: `@Fn` as a type."""
    assert _found(
        pipeline.check(_E136_FN_IS_NOT_A_TYPE, file="main.vera"),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Fn': nothing in scope declares it.",
          'location': {'line': 1, 'column': 14, 'file': 'main.vera'},
          'source_line': 'public fn f(@Fn -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       "code generation has no representation for it.  'Fn' is "
                       "how a function-typed binding's slot is referenced "
                       '(`@Fn.0`); it is not a type.',
          'fix': "Write the function type itself — e.g. '@fn(Int -> Int) "
                 "effects(pure)' — or a type alias for it.",
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e136_an_import_that_did_not_resolve(tmp_path: Path) -> None:
    """_unknown_type_advice: the module of a dotted path did not resolve."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E136_AN_IMPORT_THAT_DID_NOT_RESOLVE)),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Foo': nothing in scope declares it.",
          'location': {'line': 3, 'column': 14, 'file': '<tmp>/main.vera'},
          'source_line': 'public fn f(@Foo -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       'code generation has no representation for it.  It is '
                       "imported from module 'lib.nothere', which did not "
                       'resolve.',
          'fix': "Fix the import of 'lib.nothere' first (see the diagnostic at "
                 "that import); 'Foo' is in scope once the module resolves and "
                 'declares it public.',
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e136_a_private_data_type(tmp_path: Path) -> None:
    """_unknown_type_advice: a module declares it privately, after another."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E136_A_PRIVATE_DATA_TYPE)),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Foo': nothing in scope declares it.",
          'location': {'line': 3, 'column': 14, 'file': '<tmp>/main.vera'},
          'source_line': 'public fn f(@Foo -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       'code generation has no representation for it.  Module '
                       "'lib.types' declares a data type 'Foo', but privately, "
                       'so only that module can name it.',
          'fix': "Make 'Foo' public in module 'lib.types' and import it with "
                 "'import lib.types(Foo);', or declare a type of your own.",
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e136_a_data_type_not_imported(tmp_path: Path) -> None:
    """_unknown_type_advice: a module declares it, the import list omits it."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E136_A_DATA_TYPE_NOT_IMPORTED)),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Foo': nothing in scope declares it.",
          'location': {'line': 3, 'column': 14, 'file': '<tmp>/main.vera'},
          'source_line': 'public fn f(@Foo -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       'code generation has no representation for it.  Module '
                       "'lib.types' declares it, but this file does not import "
                       'it: a value of the type can reach a file through a '
                       'function it imports, and naming the type takes an '
                       'import of its own.',
          'fix': "Import it where it is declared: 'import lib.types(Foo);' (or "
                 "add 'Foo' to an existing import of 'lib.types').",
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e136_an_alias_in_a_module(tmp_path: Path) -> None:
    """_unknown_type_advice, format_decl_canonical: an alias, copied."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E136_AN_ALIAS_IN_A_MODULE)),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Pos': nothing in scope declares it.",
          'location': {'line': 3, 'column': 14, 'file': '<tmp>/main.vera'},
          'source_line': 'public fn f(@Pos -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       'code generation has no representation for it.  Module '
                       "'lib.types' declares a type alias 'Pos', and an alias "
                       'is module-local (Chapter 8, Section 8.4.1): no other '
                       'file can import it.',
          'fix': "Declare your own copy of the alias in this file — 'type Pos "
                 "= { @Int | @Int.0 > 0 };' — or write the type it stands for.",
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e136_a_function_type_alias_in_a_module(tmp_path: Path) -> None:
    """format_decl_canonical: a long alias vera fmt writes over lines."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E136_A_FUNCTION_TYPE_ALIAS_IN_A_MODULE)),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Handler': nothing in scope declares "
                         'it.',
          'location': {'line': 3, 'column': 14, 'file': '<tmp>/main.vera'},
          'source_line': 'public fn f(@Handler -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       'code generation has no representation for it.  Module '
                       "'lib.types' declares a type alias 'Handler', and an "
                       'alias is module-local (Chapter 8, Section 8.4.1): no '
                       'other file can import it.',
          'fix': "Declare your own copy of the alias in this file — 'type "
                 'Handler = fn(Option<Array<String>>, Option<Array<String>>, '
                 'Option<Array<String>>, Option<Array<String>> -> '
                 "Option<Array<String>>) effects(pure);' — or write the type "
                 'it stands for.',
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e136_an_import_list_naming_no_type(tmp_path: Path) -> None:
    """_unknown_type_advice: the import lists a name its module lacks."""
    assert _found(
        pipeline.check(pipeline.write_tree(tmp_path, _E136_AN_IMPORT_LIST_NAMING_NO_TYPE)),
        "E136", tmp_path) == (
        [{'severity': 'error',
          'description': "Unknown type 'Foo': nothing in scope declares it.",
          'location': {'line': 3, 'column': 14, 'file': '<tmp>/main.vera'},
          'source_line': 'public fn f(@Foo -> @Int)',
          'rationale': 'A type name must resolve where it is written: to a '
                       'type parameter in scope, a primitive, a built-in or '
                       'prelude type, a `data` or `type` declaration of this '
                       'module, or a public data type this module imports.  A '
                       'name that resolves to none of them names no type, and '
                       "code generation has no representation for it.  'import "
                       "lib.types(...)' lists it, but module 'lib.types' "
                       'declares no data type of that name.',
          'fix': "Correct 'Foo' in the import of 'lib.types' and here to a "
                 "data type that module declares public, or declare 'Foo' in "
                 'this file.',
          'spec_ref': 'Chapter 2, Section 2.10 "Type Names"',
          'error_code': 'E136'}])


def test_e202_data_fields_diff_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: data_fields, a conflict."""
    assert _found(
        pipeline.check(_E202_DATA_FIELDS_DIFF_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type Two<T, T>, expected "
                         'Two<Int, String>: its type variable T stands at type '
                         'argument 1 of Two and at type argument 2 of Two, '
                         "where the parameter's type gives it Int and String, "
                         'and a type variable takes one type.',
          'location': {'line': 29, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None))',
          'rationale': "A type variable an argument's type leaves open stands "
                       'for one type, so the parameter must give it the same '
                       'type at every position it holds.',
          'fix': 'Pass a value of type Two<Int, String> for this argument: no '
                 'type for T gives Two<T, T> that type.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e202_tuple_diff_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: tuple, a conflict."""
    assert _found(
        pipeline.check(_E202_TUPLE_DIFF_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type Tuple<Option<T>, "
                         'Option<T>>, expected Tuple<Option<Int>, '
                         'Option<String>>: its type variable T stands at the '
                         'type argument of Option in component 1 and at the '
                         'type argument of Option in component 2, where the '
                         "parameter's type gives it Int and String, and a type "
                         'variable takes one type.',
          'location': {'line': 31, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None))',
          'rationale': "A type variable an argument's type leaves open stands "
                       'for one type, so the parameter must give it the same '
                       'type at every position it holds.',
          'fix': 'Pass a value of type Tuple<Option<Int>, Option<String>> for '
                 'this argument: no type for T gives Tuple<Option<T>, '
                 'Option<T>> that type.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e202_nested_diff_nowhere(tmp_path: Path) -> None:
    """_open_variable_refusal: nested, a conflict."""
    assert _found(
        pipeline.check(_E202_NESTED_DIFF_NOWHERE, file="main.vera"),
        "E202", tmp_path) == (
        [{'severity': 'error',
          'description': "Argument 0 of 'take' has type "
                         'Tuple<Array<Option<T>>, Option<Option<T>>>, expected '
                         'Tuple<Array<Option<Int>>, Option<Option<String>>>: '
                         'its type variable T stands at the type argument of '
                         'Option in the type argument of Array in component 1 '
                         'and at the type argument of Option in the type '
                         'argument of Option in component 2, where the '
                         "parameter's type gives it Int and String, and a type "
                         'variable takes one type.',
          'location': {'line': 28, 'column': 8, 'file': 'main.vera'},
          'source_line': '  take(make(None))',
          'rationale': "A type variable an argument's type leaves open stands "
                       'for one type, so the parameter must give it the same '
                       'type at every position it holds.',
          'fix': 'Pass a value of type Tuple<Array<Option<Int>>, '
                 'Option<Option<String>>> for this argument: no type for T '
                 'gives Tuple<Array<Option<T>>, Option<Option<T>>> that type.',
          'spec_ref': 'Chapter 5, Section 5.9 "Generic Functions"',
          'error_code': 'E202'}])


def test_e800_a_trap_in_the_program(tmp_path: Path) -> None:
    """runtime_trap: `vera run --json`, the frame's line quoted from the program."""
    entry = _entry(tmp_path, {'main.vera': _TRAP_LOCAL})
    assert _found(
        _cli('run', entry),
        "E800", tmp_path) == (
        [{'severity': 'error',
          'description': 'Integer division by zero',
          'location': {'line': 9, 'column': 1, 'file': '<tmp>/main.vera'},
          'source_line': 'private fn boom(@Int -> @Int)',
          'rationale': 'The program stopped while it ran, and nothing after '
                       'that point ran: a check the compiler emitted failed, '
                       'WebAssembly refused an operation, an exception escaped '
                       "every handler, or a host function failed. The trap's "
                       'kind is `trap_kind` in the `--json` envelope, and the '
                       'source backtrace names the functions it unwound '
                       'through.',
          'fix': 'Add a precondition `requires(divisor != 0)` on the function '
                 'performing the division, or guard the division site with a '
                 'non-zero check.  The Z3 verifier will then prove the '
                 'division is safe at every call site at compile time.',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E800',
          'trap_kind': 'divide_by_zero',
          'frames': [{'func': 'boom',
                      'file': '<tmp>/main.vera',
                      'line_start': 9,
                      'line_end': 15,
                      'is_builtin': False}]}])


def test_e800_a_trap_in_the_program_as_text(tmp_path: Path) -> None:
    """runtime_trap: `vera run`'s text."""
    entry = _entry(tmp_path, {'main.vera': _TRAP_LOCAL})
    assert _norm(pipeline.cli('run', entry).stderr, _roots(tmp_path)) == (
        ('[E800] Error at <tmp>/main.vera, line 9, column 1:\n'
         '\n'
         '    private fn boom(@Int -> @Int)\n'
         '    ^\n'
         '\n'
         '  Integer division by zero\n'
         '\n'
         '  The program stopped while it ran, and nothing after that point '
         'ran: a check the compiler emitted failed, WebAssembly refused an '
         'operation, an exception escaped every handler, or a host function '
         "failed. The trap's kind is `trap_kind` in the `--json` envelope, and "
         'the source backtrace names the functions it unwound through.\n'
         '\n'
         '  Fix:\n'
         '\n'
         '    Add a precondition `requires(divisor != 0)` on the function '
         'performing\n'
         '    the division, or guard the division site with a non-zero check.  '
         'The Z3\n'
         '    verifier will then prove the division is safe at every call site '
         'at\n'
         '    compile time.\n'
         '\n'
         '  See: Chapter 0, Section 0.5.1 "Diagnostic Structure"\n'
         'Source backtrace:\n'
         '  in boom  (<tmp>/main.vera:9-15)\n'))


def test_e800_a_trap_in_an_imported_module(tmp_path: Path) -> None:
    """runtime_trap: the module's line."""
    entry = _entry(tmp_path, {'main.vera': _TRAP_MAIN, 'lib.vera': _TRAP_LIB})
    assert _found(
        _cli('run', entry),
        "E800", tmp_path) == (
        [{'severity': 'error',
          'description': 'Integer division by zero',
          'location': {'line': 3, 'column': 1, 'file': '<tmp>/lib.vera'},
          'source_line': 'public fn boom(@Int -> @Int)',
          'rationale': 'The program stopped while it ran, and nothing after '
                       'that point ran: a check the compiler emitted failed, '
                       'WebAssembly refused an operation, an exception escaped '
                       "every handler, or a host function failed. The trap's "
                       'kind is `trap_kind` in the `--json` envelope, and the '
                       'source backtrace names the functions it unwound '
                       'through.',
          'fix': 'Add a precondition `requires(divisor != 0)` on the function '
                 'performing the division, or guard the division site with a '
                 'non-zero check.  The Z3 verifier will then prove the '
                 'division is safe at every call site at compile time.',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E800',
          'trap_kind': 'divide_by_zero',
          'frames': [{'func': 'boom',
                      'file': '<tmp>/lib.vera',
                      'line_start': 3,
                      'line_end': 9,
                      'is_builtin': False}]}])


def test_e800_a_trap_no_classifier_read(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """runtime_trap: a trap with no backtrace (the backstop's), the file alone and no fix."""
    import vera.codegen

    class Trap(Exception):
        pass

    def execute(*_args: object, **_kwargs: object) -> object:
        raise Trap("wasm trap: unknown")

    monkeypatch.setattr(vera.codegen, "execute", execute)
    entry = _entry(tmp_path, {'main.vera': _TRAP_LOCAL})
    assert _found(
        _cli('run', entry),
        "E800", tmp_path) == (
        [{'severity': 'error',
          'description': 'Unhandled WASM trap: wasm trap: unknown',
          'location': {'line': 0, 'column': 0, 'file': '<tmp>/main.vera'},
          'rationale': 'The program stopped while it ran, and nothing after '
                       'that point ran: a check the compiler emitted failed, '
                       'WebAssembly refused an operation, an exception escaped '
                       "every handler, or a host function failed. The trap's "
                       'kind is `trap_kind` in the `--json` envelope, and the '
                       'source backtrace names the functions it unwound '
                       'through.',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E800'}])


def test_e800_the_first_frame_of_the_program_s_own(tmp_path: Path) -> None:
    """runtime_trap: helpers and unknown names passed over, the first program frame taken, its line quoted from its own file's text."""
    from vera import command_errors
    from vera.runtime.traps import TrapFrame

    frames = [TrapFrame("alloc", "<builtin>", None, None, True),
              TrapFrame("anon_0", "<unknown>", None, None, False),
              TrapFrame("pick", "lib.vera", 2, 4, False),
              TrapFrame("main", "main.vera", 1, 3, False)]
    sources = {"lib.vera": "-- lib\nfn pick\n", "main.vera": "fn main\n"}

    found = _reported([
        command_errors.runtime_trap(
            "main.vera", "D", frames=frames, sources=sources),
        command_errors.runtime_trap(
            "main.vera", "D", frames=frames[3:], sources={}),
        command_errors.runtime_trap(
            "main.vera", "D", frames=frames[:2], sources=sources)])
    assert _found(
        found,
        "E800", tmp_path) == (
        [{'severity': 'error',
          'description': 'D',
          'location': {'line': 2, 'column': 1, 'file': 'lib.vera'},
          'source_line': 'fn pick',
          'rationale': 'The program stopped while it ran, and nothing after '
                       'that point ran: a check the compiler emitted failed, '
                       'WebAssembly refused an operation, an exception escaped '
                       "every handler, or a host function failed. The trap's "
                       'kind is `trap_kind` in the `--json` envelope, and the '
                       'source backtrace names the functions it unwound '
                       'through.',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E800'},
         {'severity': 'error',
          'description': 'D',
          'location': {'line': 1, 'column': 1, 'file': 'main.vera'},
          'rationale': 'The program stopped while it ran, and nothing after '
                       'that point ran: a check the compiler emitted failed, '
                       'WebAssembly refused an operation, an exception escaped '
                       "every handler, or a host function failed. The trap's "
                       'kind is `trap_kind` in the `--json` envelope, and the '
                       'source backtrace names the functions it unwound '
                       'through.',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E800'},
         {'severity': 'error',
          'description': 'D',
          'location': {'line': 0, 'column': 0, 'file': 'main.vera'},
          'rationale': 'The program stopped while it ran, and nothing after '
                       'that point ran: a check the compiler emitted failed, '
                       'WebAssembly refused an operation, an exception escaped '
                       "every handler, or a host function failed. The trap's "
                       'kind is `trap_kind` in the `--json` envelope, and the '
                       'source backtrace names the functions it unwound '
                       'through.',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E800'}])


def test_e699_a_command_whose_check_raised(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """_internal_error_envelope: `vera run --json`."""
    import vera.checker

    def crash(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("the check fell over")

    monkeypatch.setattr(vera.checker, "typecheck_with_artifacts", crash)
    entry = _entry(tmp_path, {'main.vera': _OK})
    assert _found(
        _cli('run', entry),
        "E699", tmp_path) == (
        [{'severity': 'error',
          'description': 'Internal compiler error while running '
                         "'<tmp>/main.vera': RuntimeError: the check fell over",
          'location': {'line': 0, 'column': 0, 'file': '<tmp>/main.vera'},
          'rationale': 'The compiler raised an unexpected exception. This is a '
                       'bug in the compiler, not a property of the program '
                       'being processed — the input may well be valid.',
          'fix': 'Please file a bug report with the offending program at '
                 'https://github.com/aallan/vera/issues',
          'spec_ref': 'Chapter 0, Section 0.5.1 "Diagnostic Structure"',
          'error_code': 'E699'}])


def test_e699_a_command_whose_check_raised_as_text(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """_internal_error_envelope: `vera compile`'s text."""
    import vera.checker

    def crash(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("the check fell over")

    monkeypatch.setattr(vera.checker, "typecheck_with_artifacts", crash)
    entry = _entry(tmp_path, {'main.vera': _OK})
    assert _norm(pipeline.cli('compile', entry).stderr, _roots(tmp_path)) == (
        ('[E699] Error at <tmp>/main.vera:\n'
         '\n'
         "  Internal compiler error while compiling '<tmp>/main.vera': "
         'RuntimeError: the check fell over\n'
         '\n'
         '  The compiler raised an unexpected exception. This is a bug in the '
         'compiler, not a property of the program being processed — the input '
         'may well be valid.\n'
         '\n'
         '  Fix:\n'
         '\n'
         '    Please file a bug report with the offending program at '
         'https://github.com/aallan/vera/issues\n'
         '\n'
         '  See: Chapter 0, Section 0.5.1 "Diagnostic Structure"\n'))


def test_e699_the_language_server_s_analysis_raised(tmp_path: Path) -> None:
    """analysis_failure: what is published when analysing raised."""
    from lsprotocol import converters

    from vera.lsp.features import analysis_failure

    found = _reported(
        dict(converters.get_converter().unstructure(d), error_code="E699")
        for d in analysis_failure("untitled:x.vera", _OK,
                                  RuntimeError("it fell over")))
    assert _found(
        found,
        "E699", tmp_path) == (
        [{'range': {'start': {'line': 0, 'character': 0},
                    'end': {'line': 0, 'character': 6}},
          'message': 'Internal compiler error while analysing '
                     "'untitled:x.vera': RuntimeError: it fell over\n"
                     '\n'
                     'The compiler raised an unexpected exception. This is a '
                     'bug in the compiler, not a property of the program -- '
                     'the text may well be valid. Until a change the server '
                     'can analyse, it has no analysis of this document: hover, '
                     'go-to-definition and completion answer nothing, a proof '
                     'delta has no baseline, and the edit methods refuse.\n'
                     '\n'
                     'Fix: Please file a bug report with the offending program '
                     'at https://github.com/aallan/vera/issues',
          'severity': 1,
          'code': 'E699',
          'source': 'vera',
          'error_code': 'E699'}])


def test_e624_a_call_with_no_target(tmp_path: Path) -> None:
    """_emit_cross_module_error: code generation's rail for a call with no
    target, module-qualified and bare.  The check refuses such a call
    first (E200, E230, E233, E340), so no command reaches it: it is read
    from the emitter, at the node it is handed."""
    from vera.codegen import CodeGenerator

    node = pipeline.parse(_OK).program.declarations[0].decl
    gen = CodeGenerator(pipeline.typed(), source=_OK, file="main.vera")
    gen._emit_cross_module_error(node, "f", "m::f")
    gen._emit_cross_module_error(node, "g")
    rationale = (
        'The WASM code generator compiles imported functions into the '
        'same binary.  An unresolved call has no target to compile '
        'against.  The checker refuses a call that names nothing '
        '(E200, E230, E233), and a call to an operation of a '
        'user-declared ability (E340), so a call reaching this was '
        'compiled without being checked.')
    assert _found(_reported(gen.diagnostics), "E624", tmp_path) == (
        [{'severity': 'error',
          'description': "Function 'm::f' is not defined in this module and "
                         'was not found in any imported module.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn f(@Int -> @Int)',
          'rationale': rationale,
          'fix': "Ensure 'm::f' names a function exported by a module this "
                 'file imports — check the import path and that the target '
                 'module declares it.',
          'spec_ref': 'Chapter 8, Section 8.5.3 "Module-Qualified Calls"',
          'error_code': 'E624'},
         {'severity': 'error',
          'description': "Function 'g' is not defined in this module and was "
                         'not found in any imported module.',
          'location': {'line': 1, 'column': 8, 'file': 'main.vera'},
          'source_line': 'public fn f(@Int -> @Int)',
          'rationale': rationale,
          'fix': "Define 'g' in this module, or import it from the module "
                 "that declares it with 'import <module>(g);' (replace "
                 "<module> with that module's path, e.g. 'vera.math').",
          'spec_ref': 'Chapter 8, Section 8.5.1 "Bare Calls"',
          'error_code': 'E624'}])


@pytest.mark.usefixtures("injected_false_proof")
def test_e703_a_false_proof_behind_a_parameter(tmp_path: Path) -> None:
    """run: E703 at most three times for nine refuting trials."""
    assert _found(
        pipeline.contract_test(_E703_A_FALSE_PROOF_BEHIND_A_PARAMETER, file="main.vera", trials=9, distrust=True),
        "E703", tmp_path) == (
        [{'severity': 'error',
          'description': "Tier 1 proof refuted in 'below_min': "
                         'ensures(@Int.result < 0) was proved, but the trial '
                         'on @Int.0 = 0 failed it at run time: Postcondition '
                         'violation in below_min(@Int -> @Int)',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result < 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       "discharged at Tier 1, and the trial's arguments "
                       "satisfy the function's `requires` in the verifier's "
                       'own model, so the proof and the compiled program '
                       'disagree: unless an `assume` the proof rests on is '
                       'false, the verifier proved something about a program '
                       'other than the one that runs.',
          'fix': 'If a callee this proof relies on contains an `assume`, check '
                 'that first: an `assume` is taken on trust (W003), so a false '
                 'one lets the verifier prove a contract the program then '
                 'violates.  Otherwise this is a soundness defect in Vera, not '
                 'in the program: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.  Until it is fixed, treat the '
                 'obligation as checked at run time rather than proved: the '
                 'compiled program carries the check, so it traps here instead '
                 'of continuing past the violation.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'below_min': "
                         'ensures(@Int.result < 0) was proved, but the trial '
                         'on @Int.0 = 1 failed it at run time: Postcondition '
                         'violation in below_min(@Int -> @Int)',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result < 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       "discharged at Tier 1, and the trial's arguments "
                       "satisfy the function's `requires` in the verifier's "
                       'own model, so the proof and the compiled program '
                       'disagree: unless an `assume` the proof rests on is '
                       'false, the verifier proved something about a program '
                       'other than the one that runs.',
          'fix': 'If a callee this proof relies on contains an `assume`, check '
                 'that first: an `assume` is taken on trust (W003), so a false '
                 'one lets the verifier prove a contract the program then '
                 'violates.  Otherwise this is a soundness defect in Vera, not '
                 'in the program: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.  Until it is fixed, treat the '
                 'obligation as checked at run time rather than proved: the '
                 'compiled program carries the check, so it traps here instead '
                 'of continuing past the violation.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'below_min': "
                         'ensures(@Int.result < 0) was proved, but the trial '
                         'on @Int.0 = -1 failed it at run time: Postcondition '
                         'violation in below_min(@Int -> @Int)',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result < 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       "discharged at Tier 1, and the trial's arguments "
                       "satisfy the function's `requires` in the verifier's "
                       'own model, so the proof and the compiled program '
                       'disagree: unless an `assume` the proof rests on is '
                       'false, the verifier proved something about a program '
                       'other than the one that runs.',
          'fix': 'If a callee this proof relies on contains an `assume`, check '
                 'that first: an `assume` is taken on trust (W003), so a false '
                 'one lets the verifier prove a contract the program then '
                 'violates.  Otherwise this is a soundness defect in Vera, not '
                 'in the program: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.  Until it is fixed, treat the '
                 'obligation as checked at run time rather than proved: the '
                 'compiled program carries the check, so it traps here instead '
                 'of continuing past the violation.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'}])


@pytest.mark.usefixtures("injected_false_proof")
def test_e703_a_proof_resting_on_an_assume(tmp_path: Path) -> None:
    """run: E703 naming the `assume` the proof rests on."""
    assert _found(
        pipeline.contract_test(_E703_A_PROOF_RESTING_ON_AN_ASSUME, file="main.vera", trials=9, distrust=True),
        "E703", tmp_path) == (
        [{'severity': 'error',
          'description': "Tier 1 proof refuted in 'trusting': "
                         'ensures(@Int.result > 0) was proved, but the trial '
                         'on @Int.0 = 0 failed it at run time: Postcondition '
                         'violation in trusting(@Int -> @Int); the proof rests '
                         'on `assume(@Int.0 > 0)` at line 6, which these '
                         'arguments violate',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result > 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       'discharged at Tier 1, from premises that include the '
                       '`assume` the description names, which the verifier '
                       'takes on trust rather than proving (W003, spec '
                       "§6.2.6).  The trial's arguments satisfy the function's "
                       '`requires` and violate that `assume`, so the proof was '
                       'built on a premise that is false here, and this trial '
                       'cannot tell whether the verifier is also wrong.',
          'fix': 'Replace the `assume` with something the verifier proves or '
                 'the program checks: a `requires` the callers must establish, '
                 'so `vera verify` proves it at every call site, or an '
                 'explicit branch on the condition.  An `assume` is for a fact '
                 'the verifier cannot reach on its own; one these arguments '
                 'violate is not a fact.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'trusting': "
                         'ensures(@Int.result > 0) was proved, but the trial '
                         'on @Int.0 = -1 failed it at run time: Postcondition '
                         'violation in trusting(@Int -> @Int); the proof rests '
                         'on `assume(@Int.0 > 0)` at line 6, which these '
                         'arguments violate',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result > 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       'discharged at Tier 1, from premises that include the '
                       '`assume` the description names, which the verifier '
                       'takes on trust rather than proving (W003, spec '
                       "§6.2.6).  The trial's arguments satisfy the function's "
                       '`requires` and violate that `assume`, so the proof was '
                       'built on a premise that is false here, and this trial '
                       'cannot tell whether the verifier is also wrong.',
          'fix': 'Replace the `assume` with something the verifier proves or '
                 'the program checks: a `requires` the callers must establish, '
                 'so `vera verify` proves it at every call site, or an '
                 'explicit branch on the condition.  An `assume` is for a fact '
                 'the verifier cannot reach on its own; one these arguments '
                 'violate is not a fact.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'trusting': "
                         'ensures(@Int.result > 0) was proved, but the trial '
                         'on @Int.0 = -2 failed it at run time: Postcondition '
                         'violation in trusting(@Int -> @Int); the proof rests '
                         'on `assume(@Int.0 > 0)` at line 6, which these '
                         'arguments violate',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result > 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       'discharged at Tier 1, from premises that include the '
                       '`assume` the description names, which the verifier '
                       'takes on trust rather than proving (W003, spec '
                       "§6.2.6).  The trial's arguments satisfy the function's "
                       '`requires` and violate that `assume`, so the proof was '
                       'built on a premise that is false here, and this trial '
                       'cannot tell whether the verifier is also wrong.',
          'fix': 'Replace the `assume` with something the verifier proves or '
                 'the program checks: a `requires` the callers must establish, '
                 'so `vera verify` proves it at every call site, or an '
                 'explicit branch on the condition.  An `assume` is for a fact '
                 'the verifier cannot reach on its own; one these arguments '
                 'violate is not a fact.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'via_callee': "
                         "ensures(@Int.result > 0) of 'helper' was proved, but "
                         'the trial on @Int.0 = 0 failed it at run time: '
                         'Postcondition violation in helper(@Int -> @Int); the '
                         'proof rests on `assume(@Int.0 > 0)` at line 15, in '
                         "'helper', which the verifier takes on trust (W003)",
          'location': {'line': 12, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result > 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       'discharged at Tier 1, from premises that include the '
                       '`assume` the description names, which the verifier '
                       'takes on trust rather than proving (W003, spec '
                       '§6.2.6).  If the values that reach the `assume` '
                       'violate it, the proof was built on a premise that is '
                       'false there, and the program is wrong; if they satisfy '
                       'it, the proof and the compiled program disagree, which '
                       'is a soundness defect in Vera.',
          'fix': 'Check the `assume` the description names against the values '
                 'that reach it.  If they violate it, replace it with a '
                 '`requires` the callers must establish, or an explicit branch '
                 'on the condition.  If they satisfy it, this is a soundness '
                 'defect in Vera: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'via_callee': "
                         "ensures(@Int.result > 0) of 'helper' was proved, but "
                         'the trial on @Int.0 = -1 failed it at run time: '
                         'Postcondition violation in helper(@Int -> @Int); the '
                         'proof rests on `assume(@Int.0 > 0)` at line 15, in '
                         "'helper', which the verifier takes on trust (W003)",
          'location': {'line': 12, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result > 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       'discharged at Tier 1, from premises that include the '
                       '`assume` the description names, which the verifier '
                       'takes on trust rather than proving (W003, spec '
                       '§6.2.6).  If the values that reach the `assume` '
                       'violate it, the proof was built on a premise that is '
                       'false there, and the program is wrong; if they satisfy '
                       'it, the proof and the compiled program disagree, which '
                       'is a soundness defect in Vera.',
          'fix': 'Check the `assume` the description names against the values '
                 'that reach it.  If they violate it, replace it with a '
                 '`requires` the callers must establish, or an explicit branch '
                 'on the condition.  If they satisfy it, this is a soundness '
                 'defect in Vera: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'},
         {'severity': 'error',
          'description': "Tier 1 proof refuted in 'via_callee': "
                         "ensures(@Int.result > 0) of 'helper' was proved, but "
                         'the trial on @Int.0 = -2 failed it at run time: '
                         'Postcondition violation in helper(@Int -> @Int); the '
                         'proof rests on `assume(@Int.0 > 0)` at line 15, in '
                         "'helper', which the verifier takes on trust (W003)",
          'location': {'line': 12, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@Int.result > 0)',
          'rationale': '`vera test --distrust` runs the functions the verifier '
                       'proved, compiled with the runtime checks code '
                       'generation emits whatever the tier.  The check that '
                       'failed stands for an obligation the verifier '
                       'discharged at Tier 1, from premises that include the '
                       '`assume` the description names, which the verifier '
                       'takes on trust rather than proving (W003, spec '
                       '§6.2.6).  If the values that reach the `assume` '
                       'violate it, the proof was built on a premise that is '
                       'false there, and the program is wrong; if they satisfy '
                       'it, the proof and the compiled program disagree, which '
                       'is a soundness defect in Vera.',
          'fix': 'Check the `assume` the description names against the values '
                 'that reach it.  If they violate it, replace it with a '
                 '`requires` the callers must establish, or an explicit branch '
                 'on the condition.  If they satisfy it, this is a soundness '
                 'defect in Vera: report it at '
                 'https://github.com/aallan/vera/issues/new with this program '
                 'and the arguments above.',
          'spec_ref': 'Chapter 0, Section 0.5.6 "Contract-Driven Testing"',
          'error_code': 'E703'}])


def test_e543_a_decreases_on_an_exn_row(tmp_path: Path) -> None:
    """_disclose_row: E543, a measure."""
    assert _found(
        pipeline.verify(_E543_A_DECREASES_ON_AN_EXN_ROW, file="main.vera"),
        "E543", tmp_path) == (
        [{'severity': 'warning',
          'description': "The termination measure in 'f' could not be verified "
                         'statically, and no runtime check can be emitted for '
                         'it: a decreases on an Exn row has no chain guard: a '
                         'throw unwinds past the restore. It is counted in '
                         'neither tier.',
          'location': {'line': 4, 'column': 3, 'file': 'main.vera'},
          'source_line': '  decreases(@Nat.0)',
          'rationale': 'No runtime check guards this site because a decreases '
                       'on an Exn row has no chain guard: a throw unwinds past '
                       'the restore, so a value that violates it is not caught '
                       'at run time; the verifier discloses it rather than '
                       'claim a runtime check.',
          'fix': 'Restate the obligation so the solver can prove it, or move '
                 'the fact to a site a runtime check guards.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'E543'}])


def test_e543_an_ensures_over_a_string_result(tmp_path: Path) -> None:
    """_disclose_row: E543, a postcondition."""
    assert _found(
        pipeline.verify(_E543_AN_ENSURES_OVER_A_STRING_RESULT, file="main.vera"),
        "E543", tmp_path) == (
        [{'severity': 'warning',
          'description': "The postcondition in 'f' could not be verified "
                         'statically, and no runtime check can be emitted for '
                         'it: an ensures over a String or Array result is not '
                         'lowered. It is counted in neither tier.',
          'location': {'line': 3, 'column': 3, 'file': 'main.vera'},
          'source_line': '  ensures(@String.result == show(@Int.0))',
          'rationale': 'No runtime check guards this site because an ensures '
                       'over a String or Array result is not lowered, so a '
                       'value that violates it is not caught at run time; the '
                       'verifier discloses it rather than claim a runtime '
                       'check.',
          'fix': 'Restate the obligation so the solver can prove it, or move '
                 'the fact to a site a runtime check guards.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'E543'}])


def test_e506_a_nested_refinement(tmp_path: Path) -> None:
    """_disclose_row: E506, the row's reason."""
    assert _found(
        pipeline.verify(_E506_A_NESTED_REFINEMENT, file="main.vera"),
        "E506", tmp_path) == (
        [{'severity': 'warning',
          'description': "The refinement narrowing in 'mk' could not be "
                         'verified statically, and no runtime check can be '
                         'emitted for it: a refinement over a refinement has '
                         'no guard. It is counted in neither tier.',
          'location': {'line': 9, 'column': 8, 'file': 'main.vera'},
          'source_line': '  Some(float_to_int(@Float64.0))',
          'rationale': 'It was not discharged statically: the only '
                       'countermodel ran over an opaque stand-in for a value '
                       'the verifier cannot translate, which refutes nothing '
                       'the program produces.  No runtime check guards this '
                       'site because a refinement over a refinement has no '
                       'guard, so a value that violates it is not caught at '
                       'run time; the verifier discloses it rather than claim '
                       'a runtime check.',
          'fix': 'Restate the obligation so the solver can prove it, or move '
                 'the fact to a site a runtime check guards.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'E506'}])


def test_e504_a_disclosed_narrowing_in_an_imported_module(tmp_path: Path) -> None:
    """_disclose_row: E504, in the module the verifier reads."""
    assert _found(
        pipeline.verify(pipeline.write_tree(tmp_path, _E504_A_DISCLOSED_NARROWING_IN_AN_IMPORTED_MODULE)),
        "E504", tmp_path) == (
        [{'severity': 'warning',
          'description': "The @Nat narrowing in 'relay' could not be verified "
                         'statically, and no runtime check can be emitted for '
                         'it: string_slice clamps its @Nat argument. It is '
                         'counted in neither tier.',
          'location': {'line': 13, 'column': 40, 'file': '<tmp>/main.vera'},
          'source_line': '      let @String = string_slice("ab", @NonNeg.0, '
                         '1);',
          'rationale': 'It was not discharged statically: the only proof '
                       'available leans on a declared-type fact this run '
                       'disclosed as neither proved nor guarded, so it is a '
                       'Tier-3 truth rather than a Tier-1 proof.  No runtime '
                       'check guards this site because string_slice clamps its '
                       '@Nat argument, so a value that violates it is not '
                       'caught at run time; the verifier discloses it rather '
                       'than claim a runtime check.',
          'fix': 'Restate the obligation so the solver can prove it, or move '
                 'the fact to a site a runtime check guards.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'E504'}])


def test_e503_a_later_array_element(tmp_path: Path) -> None:
    """_relocate_diagnostic: E503 at the row."""
    assert _found(
        pipeline.verify(_E503_A_LATER_ARRAY_ELEMENT, file="main.vera"),
        "E503", tmp_path) == (
        [{'severity': 'error',
          'description': "@Int value narrowing into a @Nat return type in 'f' "
                         'may be negative.\n'
                         '  Counterexample:\n'
                         '      @Int.0 = -1',
          'location': {'line': 7, 'column': 3, 'file': 'main.vera'},
          'source_line': '  [@Int.0, @Nat.0][0]',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the bad inputs: '
                 '`requires(@Int.0 >= 0)`.  Alternatively, guard the binding '
                 'with an `if` whose condition holds the value non-negative — '
                 'the path condition discharges the obligation in the '
                 'then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'}])


def test_e505_a_refuted_value_inside_a_handle(tmp_path: Path) -> None:
    """_relocate_diagnostic: E505."""
    assert _found(
        pipeline.verify(_E505_A_REFUTED_VALUE_INSIDE_A_HANDLE, file="main.vera"),
        "E505", tmp_path) == (
        [{'severity': 'error',
          'description': "Value passed as a return type in 'f' may not satisfy "
                         'the refinement `Option<{@Int | ...}>` writes on a '
                         'component of its type.\n'
                         '  Counterexample:\n'
                         '      @Float64.0 = nan()',
          'location': {'line': 12, 'column': 10, 'file': 'main.vera'},
          'source_line': '    Some(0 - 5)',
          'rationale': 'A refinement written inside a type — an ADT payload, a '
                       'tuple component — is an invariant of every value of '
                       'that type, and the receiving function is verified ONCE '
                       'assuming it holds. The obligation to establish it '
                       'therefore belongs to whoever supplies the value: a '
                       'construction site discharges it at construction, and a '
                       'value produced any other way discharges it here.  This '
                       "one is neither established by the argument's own "
                       'declared type nor provable from what is known about '
                       'it.',
          'fix': 'Give the producer a contract that establishes the component '
                 'invariant (an ensures() implying the predicate, or a '
                 'declared return type carrying the same refinement), or '
                 'narrow the value explicitly at a site where the predicate '
                 'can be proved.',
          'spec_ref': 'Chapter 2, Section 2.6 "Refinement Types" and Chapter '
                      '6, Section 6.8 "Summary of Verification Tiers"',
          'error_code': 'E505'}])


def test_e506_a_value_inside_a_handle_clause(tmp_path: Path) -> None:
    """_relocate_diagnostic: E506.  The payload's row is a checked one
    (#1542): the Tier 3 note, where it was the disclosure of a stale reason."""
    assert _found(
        pipeline.verify(_E506_A_VALUE_INSIDE_A_HANDLE_CLAUSE, file="main.vera"),
        "E506", tmp_path) == (
        [{'severity': 'warning',
          'description': "Refinement predicate at a return type in 'f' could "
                         'not be verified statically; it will be checked at '
                         'run time. To prove it statically, add a '
                         '`requires(...)` implying the predicate or guard the '
                         'binding with an `if`.',
          'location': {'line': 9, 'column': 27, 'file': 'main.vera'},
          'source_line': '    throw(@Int) -> { Some(0 - 5) }',
          'rationale': 'The refinement predicate was not discharged '
                       'statically: the only countermodel ran over an opaque '
                       'stand-in for a value the verifier cannot translate, '
                       'which refutes nothing the program produces.  Codegen '
                       'emits a runtime predicate guard at the function '
                       'boundary, so the narrowing is checked at run time '
                       '(Tier 3) rather than silently accepted.',
          'spec_ref': 'Chapter 2, Section 2.6 "Refinement Types" and Chapter '
                      '6, Section 6.8 "Summary of Verification Tiers"',
          'error_code': 'E506',
          'tier': 3}])


def test_e503_e505_a_binder_after_a_wildcard(tmp_path: Path) -> None:
    """_relocate_diagnostic: two narrowings of one sub-pattern."""
    assert _found(
        pipeline.verify(_E503_E505_A_BINDER_AFTER_A_WILDCARD, file="main.vera"),
        "E505", tmp_path) == (
        [{'severity': 'error',
          'description': 'Value narrowing into a refined ADT sub-pattern bind '
                         "in 'f' may violate the refinement predicate `@Int.0 "
                         '> 0`.\n'
                         '  Counterexample:\n'
                         '      @Option<P>.0 = Some(MkP(2, 3, 0))',
          'location': {'line': 13, 'column': 23, 'file': 'main.vera'},
          'source_line': '    Some(MkP(_, @Nat, @Pos)) -> nat_to_int(@Nat.0) + '
                         '@Pos.0,',
          'rationale': 'A refinement type `{ @Base | P }` carries the '
                       'invariant that every inhabitant satisfies its '
                       'predicate P, but the type checker permits the '
                       'underlying base value to narrow into the refined slot '
                       'and defers the proof to verification. The SMT solver '
                       'found inputs where the narrowed value does not satisfy '
                       'the predicate.',
          'fix': 'Add a precondition under which the narrowed value satisfies '
                 'the predicate.  Alternatively, guard the binding with an '
                 '`if` whose condition is the predicate — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.6 "Refinement Types" and Chapter '
                      '6, Section 6.8 "Summary of Verification Tiers"',
          'error_code': 'E505'}])


def test_e522_a_generic_helper_family(tmp_path: Path) -> None:
    """_emit_aggregated_diagnostic: the representative's diagnostic, prefixed with its instantiations."""
    assert _found(
        pipeline.verify(ROOT / 'tests/conformance/ch09_nested_helper_family_op_name.vera'),
        "E522", tmp_path) == (
        [{'severity': 'warning',
          'description': "In generic function 'outer' instantiated at "
                         "outer<Int>: In generic function 'ginner' "
                         'instantiated at ginner<Int>: Cannot statically '
                         "verify postcondition in 'ginner'. The function body "
                         'holds a value the verifier cannot translate, which '
                         'it models as a stand-in, and the postcondition '
                         'depends on it. Contract will be checked at runtime.',
          'location': {'line': 25,
                       'column': 5,
                       'file': '<root>/tests/conformance/ch09_nested_helper_family_op_name.vera'},
          'source_line': '    ensures(@Int.result == 42007)',
          'rationale': 'An expression outside the decidable fragment (an '
                       "effect operation's result, a closure applied, a "
                       'generic call) is modelled as a stand-in that carries '
                       "only its type's facts, so a postcondition that depends "
                       'on it can be neither proven nor refuted statically.',
          'spec_ref': 'Chapter 6, Section 6.8 "Summary of Verification Tiers"',
          'error_code': 'E522',
          'tier': 3},
         {'severity': 'warning',
          'description': "In generic function 'outer' instantiated at "
                         'outer<Int>: Cannot statically verify postcondition '
                         "in 'outer'. The function body holds a value the "
                         'verifier cannot translate, which it models as a '
                         'stand-in, and the postcondition depends on it. '
                         'Contract will be checked at runtime.',
          'location': {'line': 17,
                       'column': 3,
                       'file': '<root>/tests/conformance/ch09_nested_helper_family_op_name.vera'},
          'source_line': '  ensures(@Int.result == 42007)',
          'rationale': 'An expression outside the decidable fragment (an '
                       "effect operation's result, a closure applied, a "
                       'generic call) is modelled as a stand-in that carries '
                       "only its type's facts, so a postcondition that depends "
                       'on it can be neither proven nor refuted statically.',
          'spec_ref': 'Chapter 6, Section 6.8 "Summary of Verification Tiers"',
          'error_code': 'E522',
          'tier': 3}])


def test_e506_an_imported_generic_clone(tmp_path: Path) -> None:
    """_emit_aggregated_diagnostic: E506 of a module's clone."""
    assert _found(
        pipeline.verify(pipeline.write_tree(tmp_path, _E506_AN_IMPORTED_GENERIC_CLONE)),
        "E506", tmp_path) == (
        [{'severity': 'warning',
          'description': "In generic function 'gen' instantiated at "
                         "gen<String>: The refinement narrowing in 'gen' could "
                         'not be verified statically, and no runtime check can '
                         'be emitted for it: a refinement inside a constructor '
                         'payload or below a carrier element is decomposed by '
                         'no boundary. It is counted in neither tier.',
          'location': {'line': 11, 'column': 89, 'file': '<tmp>/glib.vera'},
          'source_line': '  let @Option<Int> = Some(apply_fn(fn(@Int -> @Int) '
                         'effects(pure) { @Int.0 }, @Int.0)); @Option<Int>.0',
          'rationale': 'It was not discharged statically: the only '
                       'countermodel ran over an opaque stand-in for a value '
                       'the verifier cannot translate, which refutes nothing '
                       'the program produces.  No runtime check guards this '
                       'site because a refinement inside a constructor payload '
                       'or below a carrier element is decomposed by no '
                       'boundary, so a value that violates it is not caught at '
                       'run time; the verifier discloses it rather than claim '
                       'a runtime check.',
          'fix': 'Restate the obligation so the solver can prove it, or move '
                 'the fact to a site a runtime check guards.',
          'spec_ref': 'Chapter 6, Section 6.8.1 "Obligation Vocabulary"',
          'error_code': 'E506'}])


def test_lsp_a_module_no_import_reaches_is_placed_at_the_first_token(tmp_path: Path) -> None:
    """head_for: a file no import of the document binds is published at the document's first token, on its first line."""
    from lsprotocol import converters

    from vera.lsp.features import LineIndex, _Placement

    place = _Placement(index=LineIndex("public fn f\nsecond line\n"),
                       path="main.vera")
    assert _norm(converters.get_converter().unstructure(place.head_for('elsewhere.vera')), _roots(tmp_path)) == (
        {'start': {'line': 0, 'character': 0},
         'end': {'line': 0, 'character': 6}})


def test_e009_in_a_tree_parse_did_not_build(tmp_path: Path) -> None:
    """transform._placed: a tree with no origin leaves the error as transform raised it, unplaced."""
    from vera.errors import VeraError
    from vera.lexical import ORIGIN_ATTR
    from vera.parser import parse
    from vera.transform import transform

    tree = parse(_STR_ESCAPE, file="main.vera")
    delattr(tree, ORIGIN_ATTR)

    found = _reported([])
    try:
        transform(tree)
    except VeraError as exc:
        found = _reported([exc.diagnostic])
    assert _found(
        found,
        "E009", tmp_path) == (
        [{'severity': 'error',
          'description': 'Invalid escape sequence: \\q',
          'location': {'line': 6, 'column': 8},
          'rationale': 'Vera strings accept a closed set of escape sequences '
                       'so string literals are unambiguous; an unrecognised '
                       'escape is more likely a typo than an intention, and '
                       "silently passing it through would change the string's "
                       'meaning.',
          'fix': 'Use one of the valid escapes — \\\\, \\", \\n, \\t, \\r, '
                 '\\0, \\u{XXXX} (1-6 hex digits), or \\( for interpolation — '
                 'or escape the backslash itself (\\\\) if a literal backslash '
                 'is intended.',
          'spec_ref': 'Chapter 1, Section 1.6 "Literals"',
          'error_code': 'E009'}])


def test_e533_a_state_at_a_variable_no_parameter_holds(tmp_path: Path) -> None:
    """typed._state_fix: the cell a type parameter, no parameter of it."""
    assert _found(
        pipeline.check(_E533_A_STATE_AT_A_VARIABLE_NO_PARAMETER_HOLDS, file="main.vera"),
        "E533", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'sneak([@Int.0])' instantiates 'sneak' at T "
                         "= Int, where its handler's state is declared @Nat "
                         'but its cell is State<Int>.',
          'location': {'line': 18, 'column': 3, 'file': 'main.vera'},
          'source_line': '  sneak([@Int.0])',
          'rationale': 'For the builtin State effect the handler state '
                       'declaration IS the State<T> cell, and a generic '
                       "handler's cell is its type parameter's instantiation, "
                       'so a declaration that names another type diverges from '
                       'the cell where the instantiation makes them differ: '
                       'the obligations and the runtime guards key off the '
                       'cell.',
          'fix': "Declare the handler's state at its cell's type, `@T`, so "
                 "every instantiation's state is its cell.",
          'spec_ref': 'Chapter 7, Section 7.5.1 "Handler Syntax"',
          'error_code': 'E533'}])


def test_e613_a_formal_with_no_example(tmp_path: Path) -> None:
    """typed._call_fix: a formal no literal stands for."""
    assert _found(
        pipeline.check(_E613_A_FORMAL_WITH_NO_EXAMPLE, file="main.vera"),
        "E613", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'same_t(Tuple([1], 2))' instantiates "
                         "'same_t' at T = Array<Int>, where type 'Array<Int>' "
                         "does not satisfy ability 'Eq', which 'same_t' "
                         'requires of T: only primitive types (Int, Bool, '
                         'Float64, String, Byte, Nat, Unit) and ADTs whose '
                         'fields are themselves Eq (structural derivation) '
                         'support Eq.',
          'location': {'line': 14, 'column': 3, 'file': 'main.vera'},
          'source_line': '  same_t(Tuple([1], 2))',
          'rationale': "A generic's ability constraint holds for every type "
                       'argument it is instantiated at.  The check infers each '
                       "call's type arguments and holds each constraint "
                       'against the type it is instantiated at, at the call '
                       'whose arguments choose it.',
          'fix': "Instantiate 'same_t' at a type that supports 'Eq', Int for "
                 'example, by annotating the value it is fixed from.',
          'spec_ref': 'Chapter 9, Section 9.8 "Abilities"',
          'error_code': 'E613'}])


def test_e613_a_variable_in_the_second_formal(tmp_path: Path) -> None:
    """typed._call_fix: a formal without the variable passed over."""
    assert _found(
        pipeline.check(_E613_A_VARIABLE_IN_THE_SECOND_FORMAL, file="main.vera"),
        "E613", tmp_path) == (
        [{'severity': 'error',
          'description': "The call 'same2(1, [1])' instantiates 'same2' at T = "
                         "Array<Int>, where type 'Array<Int>' does not satisfy "
                         "ability 'Eq', which 'same2' requires of T: only "
                         'primitive types (Int, Bool, Float64, String, Byte, '
                         'Nat, Unit) and ADTs whose fields are themselves Eq '
                         '(structural derivation) support Eq.',
          'location': {'line': 14, 'column': 3, 'file': 'main.vera'},
          'source_line': '  same2(1, [1])',
          'rationale': "A generic's ability constraint holds for every type "
                       'argument it is instantiated at.  The check infers each '
                       "call's type arguments and holds each constraint "
                       'against the type it is instantiated at, at the call '
                       'whose arguments choose it.',
          'fix': "Instantiate 'same2' at a type that supports 'Eq', Int for "
                 "example: replace 'same2(1, [1])' with 'same2(1, 0)'.",
          'spec_ref': 'Chapter 9, Section 9.8 "Abilities"',
          'error_code': 'E613'}])


def test_e503_e505_a_binder_after_a_wildcard_e503(tmp_path: Path) -> None:
    """_relocate_diagnostic: the E503 beside the relocated E505."""
    assert _found(
        pipeline.verify(_E503_E505_A_BINDER_AFTER_A_WILDCARD_E503, file="main.vera"),
        "E503", tmp_path) == (
        [{'severity': 'error',
          'description': '@Int value narrowing into a @Nat ADT sub-pattern '
                         "bind in 'f' may be negative.\n"
                         '  Counterexample:\n'
                         '      @Option<P>.0 = Some(MkP(2, -1, 3))',
          'location': {'line': 13, 'column': 17, 'file': 'main.vera'},
          'source_line': '    Some(MkP(_, @Nat, @Pos)) -> nat_to_int(@Nat.0) + '
                         '@Pos.0,',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the inputs the counterexample '
                 'shows.  Alternatively, guard the binding with an `if` whose '
                 'condition holds the value non-negative — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'}])


def test_e543_every_diagnostic_at_the_disclosed_site(tmp_path: Path) -> None:
    """_disclose_row: the disclosure retracts the run-time claim at its site."""
    verified = pipeline.verify(_E543_STRING, file="main.vera")
    assert _norm([(d.error_code, d.severity, d.location.line, d.location.column) for d in verified.diagnostics], _roots(tmp_path)) == (
        [('E543', 'warning', 3, 3)])


def test_e503_a_narrowing_at_a_tail_call_mutual_pair(tmp_path: Path) -> None:
    """_relocate_diagnostic: each E503 moved to its own row (mutual_pair)."""
    assert _found(
        pipeline.verify(_E503_A_NARROWING_AT_A_TAIL_CALL_MUTUAL_PAIR, file="main.vera"),
        "E503", tmp_path) == (
        [{'severity': 'error',
          'description': "@Int value narrowing into a @Nat return type in 'ev' "
                         'may be negative.\n'
                         '  Counterexample:\n'
                         '      @Int.0 = 0\n'
                         '      @Nat.0 = 0',
          'location': {'line': 16, 'column': 5, 'file': 'main.vera'},
          'source_line': '    wrap(@Int.0)',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the inputs the counterexample '
                 'shows.  Alternatively, guard the binding with an `if` whose '
                 'condition holds the value non-negative — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'},
         {'severity': 'error',
          'description': "@Int value narrowing into a @Nat return type in 'od' "
                         'may be negative.\n'
                         '  Counterexample:\n'
                         '      @Int.0 = 0\n'
                         '      @Nat.0 = 0',
          'location': {'line': 29, 'column': 5, 'file': 'main.vera'},
          'source_line': '    wrap(@Int.0)',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the inputs the counterexample '
                 'shows.  Alternatively, guard the binding with an `if` whose '
                 'condition holds the value non-negative — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'}])


def test_e503_a_narrowing_at_a_tail_call_if_arm(tmp_path: Path) -> None:
    """_relocate_diagnostic: each E503 moved to its own row (if_arm)."""
    assert _found(
        pipeline.verify(_E503_A_NARROWING_AT_A_TAIL_CALL_IF_ARM, file="main.vera"),
        "E503", tmp_path) == (
        [{'severity': 'error',
          'description': "@Int value narrowing into a @Nat return type in 'f' "
                         'may be negative.\n'
                         '  Counterexample:\n'
                         '      @Int.0 = 101',
          'location': {'line': 15, 'column': 5, 'file': 'main.vera'},
          'source_line': '    wrap(0)',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the inputs the counterexample '
                 'shows.  Alternatively, guard the binding with an `if` whose '
                 'condition holds the value non-negative — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'},
         {'severity': 'error',
          'description': "@Int value narrowing into a @Nat return type in 'f' "
                         'may be negative.\n'
                         '  Counterexample:\n'
                         '      @Int.0 = 0',
          'location': {'line': 17, 'column': 5, 'file': 'main.vera'},
          'source_line': '    wrap(@Int.0)',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the inputs the counterexample '
                 'shows.  Alternatively, guard the binding with an `if` whose '
                 'condition holds the value non-negative — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'}])


def test_e503_a_narrowing_at_a_tail_call_last(tmp_path: Path) -> None:
    """_relocate_diagnostic: each E503 moved to its own row (last)."""
    assert _found(
        pipeline.verify(_E503_A_NARROWING_AT_A_TAIL_CALL_LAST, file="main.vera"),
        "E503", tmp_path) == (
        [{'severity': 'error',
          'description': "@Int value narrowing into a @Nat return type in 'f' "
                         'may be negative.\n'
                         '  Counterexample:\n'
                         '      @Int.0 = 0',
          'location': {'line': 14, 'column': 3, 'file': 'main.vera'},
          'source_line': '  wrap(@Int.0)',
          'rationale': 'A @Nat slot carries a non-negativity invariant, but '
                       'the type checker permits Int <: Nat narrowing and '
                       'defers the `>= 0` proof to verification.  The SMT '
                       'solver found inputs where the narrowed value is '
                       'negative — a negative i64 would be stored in a @Nat '
                       "slot, violating the type's invariant.",
          'fix': 'Add a precondition ruling out the inputs the counterexample '
                 'shows.  Alternatively, guard the binding with an `if` whose '
                 'condition holds the value non-negative — the path condition '
                 'discharges the obligation in the then-branch.',
          'spec_ref': 'Chapter 2, Section 2.2.1 "`Int` and `Nat` '
                      'compatibility" and Chapter 11, Section 11.2.1 "Nat as '
                      'i64"',
          'error_code': 'E503'}])
