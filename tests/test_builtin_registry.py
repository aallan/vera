"""The built-in registry, `vera/builtins.py`, held to every phase that reads it (#735).

Every cell over a built-in is generated from `BUILTINS`, so a record added
later is measured the day it lands.  A call to a built-in is generated from
its own signature: a function whose parameters are the built-in's, its type
variables instantiated (`T`, `A` at `Int`; `U`, `B`, `E`, `K` at `String`;
`V` at `Int`, so a map's key and value tags differ), a function-typed
parameter named by a type alias, and a body that calls the built-in with
those parameters.  Each built-in gets these cells:

- the checker accepts the call at the record's arity, and refuses it with
  E201 at one argument more and, for a built-in that takes one, one fewer
  (the six nullary built-ins have no call with one fewer);
- the call compiles, and the host imports the module declares are
  exactly the ones the registry renders for their names, and the imports
  that implement a built-in function are those of this built-in's record:
  one family's, for a `Host` record, and none, for an `Inline` or
  `Prelude` one;
- E151 refuses a declaration of its name, except a `Prelude` record's, whose
  declaration replaces the prelude's body and is accepted;
- its emitter exists on `WasmContext` and takes the arguments its record's
  convention hands it, at the record's arity;
- for a `Host` record, the Python host's `register_<family>` defines each
  import the compiled call declares, and the browser runtime names it.

The cells that pin each reader to the registry change a record and watch
the reader follow: the checker's `FunctionInfo`, the dispatch, the
declarations, `vera builtins --json`, and the two tables the registry
absorbed (`since` and the domain).  The cells after them hold the
dispatch's explicit branches, the ownership rule (#1299) and the ability
intrinsics to their behaviour, which no record decides.
"""

from __future__ import annotations

import ast as pyast
import inspect
import re
from collections.abc import Iterator
from decimal import Decimal as PyDecimal
from pathlib import Path
from typing import Any

import pytest

from tests import pipeline
from tests.module_fixture_helpers import build_multi_module, module_value
from vera import builtins as registry
from vera.builtins import (
    ABILITY_INTRINSICS,
    BUILTINS,
    CELL,
    HOST_FAMILIES,
    HOST_IMPORT_BY_NAME,
    HOST_IMPORTS,
    INTRINSICS,
    TAG_TYPES,
    Binding,
    BuiltinSpec,
    Host,
    Inline,
    Prelude,
    host_import,
    import_line,
)
from vera.types import (
    INT,
    STRING,
    AdtType,
    ConcreteEffectRow,
    FunctionType,
    PrimitiveType,
    PureEffectRow,
    Type,
    substitute,
)
from vera.wasm.context import WasmContext

pytestmark = pytest.mark.matrix(decides=[
    "vera/builtins.py",
    "vera/wasm/calls.py",
    "vera/environment.py",
    "vera/codegen/assembly.py",
    "vera/codegen/compilability.py",
    # The emitters a record names and the conventions they take.
    "vera/wasm/calls_arrays.py",
    "vera/wasm/calls_containers.py",
    "vera/wasm/calls_encoding.py",
    "vera/wasm/calls_handlers.py",
    "vera/wasm/calls_markup.py",
    "vera/wasm/calls_math.py",
    "vera/wasm/calls_parsing.py",
    "vera/wasm/calls_strings.py",
    # The other readers, and the hosts' bindings the cells run.
    "vera/introspect.py",
    "vera/builtin_domains.py",
    "vera/runtime/collections.py",
    "vera/runtime/decimal.py",
    "vera/runtime/html.py",
    "vera/runtime/json.py",
    "vera/runtime/map.py",
    "vera/runtime/math.py",
    "vera/runtime/md.py",
    "vera/runtime/regex.py",
    "vera/runtime/set.py",
    "vera/browser/runtime.mjs",
])

ROOT = Path(__file__).resolve().parent.parent

#: The type each type variable of a built-in is instantiated at.
INSTANCE: dict[str, Type] = {
    "T": INT, "A": INT, "V": INT,
    "U": STRING, "B": STRING, "E": STRING, "K": STRING,
}

_IMPORT_LINE = re.compile(r'^\s*\(import "vera" "([^"]+)" .*$', re.MULTILINE)


# ---------------------------------------------------------------------
# A call to a built-in, generated from its record
# ---------------------------------------------------------------------


def _surface(t: Type, aliases: dict[str, str], prefix: str) -> str:
    """*t* in Vera's surface syntax; a function type through an alias."""
    if isinstance(t, PrimitiveType):
        return t.name
    if isinstance(t, AdtType):
        if not t.type_args:
            return t.name
        args = ", ".join(_surface(a, aliases, prefix) for a in t.type_args)
        return f"{t.name}<{args}>"
    if isinstance(t, FunctionType):
        assert isinstance(t.effect, PureEffectRow), t
        params = ", ".join(_surface(p, aliases, prefix) for p in t.params)
        body = (f"fn({params} -> {_surface(t.return_type, aliases, prefix)})"
                " effects(pure)")
        for name, existing in aliases.items():
            if existing == body:
                return name
        name = f"{prefix}{len(aliases)}"
        aliases[name] = body
        return name
    raise TypeError(f"no surface syntax for {t!r}")


def _effect_clause(spec: BuiltinSpec) -> str:
    effect = spec.signature.effect
    if isinstance(effect, PureEffectRow):
        return "effects(pure)"
    assert isinstance(effect, ConcreteEffectRow), effect
    return "effects(<" + ", ".join(sorted(e.name for e in effect.effects)) + ">)"


#: A value of each type a closure the probes pass returns.
_LITERALS: dict[str, str] = {
    "String": '""', "Bool": "true", "Int": "0", "Nat": "0", "Float64": "0.0",
    "Ordering": "Equal",
}


def _value(t: Type) -> str:
    """A literal of type *t*."""
    if isinstance(t, PrimitiveType):
        return _LITERALS[t.name]
    if isinstance(t, AdtType):
        if t.name == "Option":
            return "None"
        if t.name == "Array":
            return f"[{_value(t.type_args[0])}]"
        if t.name == "Result":
            return f"Err({_value(t.type_args[1])})"
        if not t.type_args and t.name in _LITERALS:
            return _LITERALS[t.name]
    raise TypeError(f"no literal of type {t!r}")


def _closure(t: FunctionType) -> str:
    """A closure of type *t*: its body is its own parameter of the return
    type where it has one (a fold's accumulator), a literal otherwise."""
    params = [_surface(p, {}, "") for p in t.params]
    ret = _surface(t.return_type, {}, "")
    body = f"@{ret}.0" if ret in params else _value(t.return_type)
    formals = ", ".join(f"@{p}" for p in params)
    return f"fn({formals} -> @{ret}) effects(pure) {{ {body} }}"


def probe_parts(
    spec: BuiltinSpec, *, delta: int = 0, prefix: str = "F",
    closures: bool = True,
) -> tuple[dict[str, str], str, str, str]:
    """``(aliases, formals, return type, call)`` of a call to *spec*.

    A function-typed parameter is passed a closure literal, so the module
    holds a closure and its function table (a closure parameter in a module
    with none is dropped, E620); with *closures* off it is a parameter of
    the probe typed by an alias, so the probe's signature is the built-in's.
    *delta* adds an argument (a copy of the last, or ``1`` for a nullary
    built-in) or drops the last one.
    """
    sig = spec.signature
    aliases: dict[str, str] = {}
    formals: list[str] = []
    args: list[str | int] = []
    for param in sig.params:
        t = substitute(param, INSTANCE)
        if closures and isinstance(t, FunctionType):
            args.append(_closure(t))
        else:
            args.append(len(formals))
            formals.append(_surface(t, aliases, prefix))
    ret = _surface(substitute(sig.ret, INSTANCE), aliases, prefix)
    written = [
        a if isinstance(a, str) else f"@{formals[a]}.{formals[a + 1:].count(formals[a])}"
        for a in args
    ]
    if delta > 0:
        written.append(written[-1] if written else "1")
    elif delta < 0:
        written = written[:-1]
    return (aliases, ", ".join(f"@{p}" for p in formals) or "@Unit", ret,
            f"{spec.name}({', '.join(written)})")


def _fn_source(name: str, formals: str, ret: str, effect: str, body: str,
               visibility: str = "public") -> str:
    return (f"{visibility} fn {name}({formals} -> @{ret})\n"
            f"  requires(true)\n  ensures(true)\n  {effect}\n"
            f"{{\n  {body}\n}}\n")


def probe_source(spec: BuiltinSpec, *, delta: int = 0) -> str:
    """A program whose one function calls *spec* with its parameters."""
    aliases, formals, ret, call = probe_parts(spec, delta=delta)
    decls = "".join(f"type {n} = {d};\n\n" for n, d in aliases.items())
    return decls + _fn_source("probe", formals, ret, _effect_clause(spec), call)


def every_builtin_source() -> str:
    """One program calling every built-in once, one function each."""
    out: list[str] = []
    for index, spec in enumerate(BUILTINS.values()):
        aliases, formals, ret, call = probe_parts(spec, prefix=f"P{index}F")
        out.extend(f"type {n} = {d};\n\n" for n, d in aliases.items())
        out.append(_fn_source(f"probe_{index}", formals, ret,
                              _effect_clause(spec), call) + "\n")
    return "".join(out)


def _declared(wat: str) -> dict[str, str]:
    """The module's host imports: name to its declaration line."""
    return {m.group(1): m.group(0) for m in _IMPORT_LINE.finditer(wat)}


_ALL = list(BUILTINS.values())
_IDS = [spec.name for spec in _ALL]
_HOSTED = [spec for spec in _ALL if isinstance(spec.lowering, Host)]
_WITH_ARGS = [spec for spec in _ALL if spec.arity > 0]


def _ids(specs: list[BuiltinSpec]) -> list[str]:
    return [spec.name for spec in specs]


# ---------------------------------------------------------------------
# The checker's view: the record's arity
# ---------------------------------------------------------------------


@pytest.mark.parametrize("spec", _ALL, ids=_IDS)
def test_checker_accepts_the_declared_arity(spec: BuiltinSpec) -> None:
    checked = pipeline.check(probe_source(spec))
    assert checked.ok, [d.description for d in checked.errors]


def _arity_refusal(spec: BuiltinSpec, delta: int) -> None:
    checked = pipeline.check(probe_source(spec, delta=delta))
    e201 = [d for d in checked.errors if d.error_code == "E201"]
    assert len(e201) == 1, [(d.error_code, d.description) for d in checked.errors]
    expected = (f"Function '{spec.name}' expects {spec.arity} argument(s), "
                f"got {spec.arity + delta}.")
    assert e201[0].description == expected


@pytest.mark.parametrize("spec", _ALL, ids=_IDS)
def test_checker_refuses_one_more_argument(spec: BuiltinSpec) -> None:
    _arity_refusal(spec, +1)


@pytest.mark.parametrize("spec", _WITH_ARGS, ids=_ids(_WITH_ARGS))
def test_checker_refuses_one_fewer_argument(spec: BuiltinSpec) -> None:
    _arity_refusal(spec, -1)


def test_every_builtin_in_one_program() -> None:
    """The program that calls every built-in once checks clean, and every
    one of its functions is compiled into the module."""
    source = every_builtin_source()
    checked = pipeline.check(source)
    assert checked.ok, [d.description for d in checked.errors][:5]
    assert not checked.warnings, [d.description for d in checked.warnings][:5]
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics][:5]
    assert set(compiled.exports) >= {f"probe_{i}" for i in range(len(BUILTINS))}


# ---------------------------------------------------------------------
# The order a module declares its imports in
# ---------------------------------------------------------------------


_EVERY_EFFECT = """\
public fn effects_probe(@String, @Nat -> @Int)
  requires(@Nat.0 > 0)
  ensures(true)
  effects(<IO, Http, Inference, Random, DB, Async>)
{
  IO.print(@String.0);
  IO.stderr(@String.0);
  let @String = IO.read_line(());
  let @Result<String, String> = IO.read_char(());
  let @Result<String, String> = IO.read_file(@String.0);
  let @Result<Unit, String> = IO.write_file(@String.1, @String.1);
  let @Array<String> = IO.args(());
  let @Option<String> = IO.get_env(@String.1);
  IO.sleep(@Nat.0);
  let @Nat = IO.time(());
  let @Result<String, String> = Http.get(@String.1);
  let @Result<String, String> = Http.post(@String.1, @String.1);
  let @Future<Result<String, String>> = async(Http.get(@String.1));
  let @Future<Result<String, String>> = async(Http.post(@String.1, @String.1));
  let @Result<String, String> = await(@Future<Result<String, String>>.0);
  let @Result<String, String> = Inference.complete(@String.1);
  let @Int = Random.random_int(1, 6);
  let @Float64 = Random.random_float(());
  let @Bool = Random.random_bool(());
  let @Result<Array<Array<Option<String>>>, String> = DB.query("SELECT 1", []);
  let @Result<Int, String> = DB.execute("DELETE FROM t", []);
  let @Int = handle[State<Int>](@Int = 3) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    put(get(()) + 1);
    get(())
  };
  IO.exit(@Int.0)
}
"""

#: The declarations `every_builtin_source()` makes, line for line and in
#: order, as the base (313c04db) compiled them.
_EVERY_BUILTIN_IMPORTS = (
    '(import "vera" "md_extract_code_blocks" (func $vera.md_extract_code_blocks (param i32 i32 i32) (result i32 i32)))',
    '(import "vera" "md_has_code_block" (func $vera.md_has_code_block (param i32 i32 i32) (result i32)))',
    '(import "vera" "md_has_heading" (func $vera.md_has_heading (param i32 i64) (result i32)))',
    '(import "vera" "md_parse" (func $vera.md_parse (param i32 i32) (result i32)))',
    '(import "vera" "md_render" (func $vera.md_render (param i32) (result i32 i32)))',
    '(import "vera" "regex_find" (func $vera.regex_find (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "regex_find_all" (func $vera.regex_find_all (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "regex_match" (func $vera.regex_match (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "regex_replace" (func $vera.regex_replace (param i32 i32 i32 i32 i32 i32) (result i32)))',
    '(import "vera" "map_contains$ks" (func $vera.map_contains$ks (param i32) (param i32) (param i32) (result i32)))',
    '(import "vera" "map_get$ks_vb" (func $vera.map_get$ks_vb (param i32) (param i32) (param i32) (result i32)))',
    '(import "vera" "map_get$ks_vi" (func $vera.map_get$ks_vi (param i32) (param i32) (param i32) (result i32)))',
    '(import "vera" "map_get$ks_vs" (func $vera.map_get$ks_vs (param i32) (param i32) (param i32) (result i32)))',
    '(import "vera" "map_insert$ks_vi" (func $vera.map_insert$ks_vi (param i32) (param i32) (param i32) (param i64) (result i32)))',
    '(import "vera" "map_keys$ks" (func $vera.map_keys$ks (param i32) (result i32) (result i32)))',
    '(import "vera" "map_new" (func $vera.map_new (result i32)))',
    '(import "vera" "map_remove$ks" (func $vera.map_remove$ks (param i32) (param i32) (param i32) (result i32)))',
    '(import "vera" "map_size" (func $vera.map_size (param i32) (result i64)))',
    '(import "vera" "map_values$vi" (func $vera.map_values$vi (param i32) (result i32) (result i32)))',
    '(import "vera" "set_add$ei" (func $vera.set_add$ei (param i32) (param i64) (result i32)))',
    '(import "vera" "set_contains$ei" (func $vera.set_contains$ei (param i32) (param i64) (result i32)))',
    '(import "vera" "set_new" (func $vera.set_new (result i32)))',
    '(import "vera" "set_remove$ei" (func $vera.set_remove$ei (param i32) (param i64) (result i32)))',
    '(import "vera" "set_size" (func $vera.set_size (param i32) (result i64)))',
    '(import "vera" "set_to_array$ei" (func $vera.set_to_array$ei (param i32) (result i32) (result i32)))',
    '(import "vera" "decimal_abs" (func $vera.decimal_abs (param i32) (result i32)))',
    '(import "vera" "decimal_add" (func $vera.decimal_add (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_compare" (func $vera.decimal_compare (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_div" (func $vera.decimal_div (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_eq" (func $vera.decimal_eq (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_from_float" (func $vera.decimal_from_float (param f64) (result i32)))',
    '(import "vera" "decimal_from_int" (func $vera.decimal_from_int (param i64) (result i32)))',
    '(import "vera" "decimal_from_string" (func $vera.decimal_from_string (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_mul" (func $vera.decimal_mul (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_neg" (func $vera.decimal_neg (param i32) (result i32)))',
    '(import "vera" "decimal_round" (func $vera.decimal_round (param i32) (param i64) (result i32)))',
    '(import "vera" "decimal_sub" (func $vera.decimal_sub (param i32) (param i32) (result i32)))',
    '(import "vera" "decimal_to_float" (func $vera.decimal_to_float (param i32) (result f64)))',
    '(import "vera" "decimal_to_string" (func $vera.decimal_to_string (param i32) (result i32) (result i32)))',
    '(import "vera" "host_decref_handle" (func $vera.host_decref_handle (param i32) (param i32)))',
    '(import "vera" "attach_bucket_to_wrapper" (func $vera.attach_bucket_to_wrapper (param i32) (param i32) (param i32)))',
    '(import "vera" "json_parse" (func $vera.json_parse (param i32 i32) (result i32)))',
    '(import "vera" "json_stringify" (func $vera.json_stringify (param i32) (result i32 i32)))',
    '(import "vera" "html_parse" (func $vera.html_parse (param i32 i32) (result i32)))',
    '(import "vera" "html_to_string" (func $vera.html_to_string (param i32) (result i32 i32)))',
    '(import "vera" "html_query" (func $vera.html_query (param i32 i32 i32) (result i32 i32)))',
    '(import "vera" "html_text" (func $vera.html_text (param i32) (result i32 i32)))',
    '(import "vera" "log" (func $vera.log (param f64) (result f64)))',
    '(import "vera" "log2" (func $vera.log2 (param f64) (result f64)))',
    '(import "vera" "log10" (func $vera.log10 (param f64) (result f64)))',
    '(import "vera" "sin" (func $vera.sin (param f64) (result f64)))',
    '(import "vera" "cos" (func $vera.cos (param f64) (result f64)))',
    '(import "vera" "tan" (func $vera.tan (param f64) (result f64)))',
    '(import "vera" "asin" (func $vera.asin (param f64) (result f64)))',
    '(import "vera" "acos" (func $vera.acos (param f64) (result f64)))',
    '(import "vera" "atan" (func $vera.atan (param f64) (result f64)))',
    '(import "vera" "atan2" (func $vera.atan2 (param f64 f64) (result f64)))',
    '(import "vera" "contract_fail" (func $vera.contract_fail (param i32 i32)))',
    '(import "vera" "trap" (func $vera.trap (param i32 i32 i32)))',
)

#: The declarations `_EVERY_EFFECT` makes, line for line and in order, as
#: the base compiled them.
_EVERY_EFFECT_IMPORTS = (
    '(import "vera" "args" (func $vera.args (result i32 i32)))',
    '(import "vera" "exit" (func $vera.exit (param i64)))',
    '(import "vera" "get_env" (func $vera.get_env (param i32 i32) (result i32)))',
    '(import "vera" "print" (func $vera.print (param i32 i32)))',
    '(import "vera" "read_char" (func $vera.read_char (result i32)))',
    '(import "vera" "read_file" (func $vera.read_file (param i32 i32) (result i32)))',
    '(import "vera" "read_line" (func $vera.read_line (result i32 i32)))',
    '(import "vera" "sleep" (func $vera.sleep (param i64)))',
    '(import "vera" "stderr" (func $vera.stderr (param i32 i32)))',
    '(import "vera" "time" (func $vera.time (result i64)))',
    '(import "vera" "write_file" (func $vera.write_file (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "host_decref_handle" (func $vera.host_decref_handle (param i32) (param i32)))',
    '(import "vera" "attach_bucket_to_wrapper" (func $vera.attach_bucket_to_wrapper (param i32) (param i32) (param i32)))',
    '(import "vera" "http_get" (func $vera.http_get (param i32 i32) (result i32)))',
    '(import "vera" "http_post" (func $vera.http_post (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "async_http_get" (func $vera.async_http_get (param i32 i32) (result i32)))',
    '(import "vera" "async_http_post" (func $vera.async_http_post (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "async_await" (func $vera.async_await (param i32) (result i32)))',
    '(import "vera" "inference_complete" (func $vera.inference_complete (param i32 i32) (result i32)))',
    '(import "vera" "db_query" (func $vera.db_query (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "db_execute" (func $vera.db_execute (param i32 i32 i32 i32) (result i32)))',
    '(import "vera" "random_int" (func $vera.random_int (param i64 i64) (result i64)))',
    '(import "vera" "random_float" (func $vera.random_float (result f64)))',
    '(import "vera" "random_bool" (func $vera.random_bool (result i32)))',
    '(import "vera" "contract_fail" (func $vera.contract_fail (param i32 i32)))',
    '(import "vera" "trap" (func $vera.trap (param i32 i32 i32)))',
    '(import "vera" "state_get_Int" (func $vera.state_get_Int (result i64)))',
    '(import "vera" "state_put_Int" (func $vera.state_put_Int (param i64)))',
    '(import "vera" "state_push_Int" (func $vera.state_push_Int))',
    '(import "vera" "state_pop_Int" (func $vera.state_pop_Int))',
)


@pytest.mark.parametrize(
    ("source", "golden"),
    [
        pytest.param(every_builtin_source(), _EVERY_BUILTIN_IMPORTS, id="every_builtin"),
        pytest.param(_EVERY_EFFECT, _EVERY_EFFECT_IMPORTS, id="every_host_effect"),
    ],
)
def test_the_declaration_order_is_the_bases(source: str, golden: tuple[str, ...]) -> None:
    """Every declaration line as the base wrote it, in the base's order: the
    families in their order, each family's rows in theirs (seven families keep
    theirs unsorted, html, async, db, random and math among them), a
    per-instance row's instances by name, and each line's WAT types, so a row
    whose types are wrong is red here although every reader follows it."""
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics][:5]
    assert tuple(line.strip() for line in _declared(compiled.wat).values()) == golden


def test_the_goldens_declare_every_row() -> None:
    """Between them the two golden programs declare an instance of every row
    of `HOST_IMPORTS`, so every row's types are held to the base's line.  A
    row added later is called from a golden program and its line added to
    that golden."""
    rows: set[str] = set()
    for line in _EVERY_BUILTIN_IMPORTS + _EVERY_EFFECT_IMPORTS:
        found = _IMPORT_LINE.match(line)
        assert found is not None, line
        name = found.group(1)
        row = host_import(name) or next(
            r for r in HOST_IMPORTS
            if r.instance == CELL and name.startswith(r.name + "_"))
        rows.add(row.name)
    assert rows == {row.name for row in HOST_IMPORTS}


# ---------------------------------------------------------------------
# Code generation's view: the imports a call declares
# ---------------------------------------------------------------------


def _prelude_calls() -> frozenset[str]:
    """The built-ins the prelude's injected bodies call: a program that
    mentions `Json` or `HtmlNode` compiles those bodies, and with them
    their calls' imports (the `Map` a `JObject` holds)."""
    from vera import prelude

    source = "".join((prelude._OPTION_COMBINATORS, prelude._RESULT_COMBINATORS,
                      prelude._JSON_COMBINATORS, prelude._HTML_COMBINATORS,
                      prelude._ARRAY_COMBINATORS))
    return frozenset(n for n in BUILTINS if re.search(rf"\b{n}\(", source))


@pytest.mark.parametrize("spec", _ALL, ids=_IDS)
def test_call_declares_its_registry_imports(spec: BuiltinSpec) -> None:
    """Each declaration is the registry's line for its name; a `Host` call
    declares its own family's import, no other call one serving itself, and
    an import serving another built-in serves one the prelude calls."""
    compiled = pipeline.compile(probe_source(spec))
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert "probe" in compiled.exports, "the call's function was dropped"
    declared = _declared(compiled.wat)
    for name, line in declared.items():
        assert host_import(name) is not None, f"{name} is no registry import"
        assert line == import_line(name), name
    serving: dict[str, set[str]] = {}
    for name in declared:
        row = host_import(name)
        assert row is not None
        if row.serves in BUILTINS:
            serving.setdefault(row.serves, set()).add(row.family)
    own = serving.pop(spec.name, set())
    if isinstance(spec.lowering, Host):
        assert own == {spec.lowering.family}
    else:
        assert own == set()
    assert set(serving) <= _prelude_calls(), sorted(serving)


# ---------------------------------------------------------------------
# A declaration of the built-in's name
# ---------------------------------------------------------------------


_PRELUDE_VALUES = {
    "Int": "0", "Bool": "false", "String": '""', "Option": "None",
    "Result": 'Err("")', "Array": '[""]',
}


@pytest.mark.parametrize("spec", _ALL, ids=_IDS)
def test_a_declaration_of_its_name(spec: BuiltinSpec) -> None:
    """E151, or for a prelude body the accepted override."""
    aliases, formals, ret, call = probe_parts(spec, closures=False)
    decls = "".join(f"type {n} = {d};\n\n" for n, d in aliases.items())
    if isinstance(spec.lowering, Prelude):
        # A value of the return type, so the override is not recursive.
        head = ret.split("<", 1)[0]
        body = _PRELUDE_VALUES[head]
    else:
        body = call
    source = decls + _fn_source(
        spec.name, formals, ret, _effect_clause(spec), body, "private")
    checked = pipeline.check(source)
    codes = [d.error_code for d in checked.errors]
    if isinstance(spec.lowering, Prelude):
        assert codes == [], [d.description for d in checked.errors]
    else:
        assert codes == ["E151"], [d.description for d in checked.errors]


# ---------------------------------------------------------------------
# The emitter and its convention
# ---------------------------------------------------------------------


class _Arg:
    """A stand-in argument: binding is checked, nothing is called."""


def _convention_args(name: str, arity: int, lowering: Inline | Host
                     ) -> tuple[tuple[Any, ...], dict[str, Any]]:
    args = tuple(_Arg() for _ in range(arity))
    env, call = _Arg(), _Arg()
    b = lowering.binding
    if b is Binding.ARGS:
        return (*args, env), {}
    if b in (Binding.ARGS_AT, Binding.ARGS_SITE):
        return (*args, env), {"at": call}
    if b is Binding.ARGS_CALL:
        return (*args, env, call), {}
    if b is Binding.CALL:
        return (call, env), {}
    if b is Binding.CALL_EXTRA:
        return (call, env, *lowering.extra), {}
    if b is Binding.NONE:
        return (), {}
    if b is Binding.NAMED:
        return (name, *args, env), {}
    raise AssertionError(f"no convention {b}")


@pytest.mark.parametrize("name", sorted(INTRINSICS))
def test_emitter_takes_its_convention(name: str) -> None:
    intrinsic = INTRINSICS[name]
    emitter = getattr(WasmContext, intrinsic.lowering.emitter, None)
    assert callable(emitter), f"WasmContext has no {intrinsic.lowering.emitter}"
    args, kwargs = _convention_args(name, intrinsic.arity, intrinsic.lowering)
    inspect.signature(emitter).bind(_Arg(), *args, **kwargs)
    # Only a convention with no extra takes none, and only CALL_EXTRA one.
    assert bool(intrinsic.lowering.extra) == (
        intrinsic.lowering.binding is Binding.CALL_EXTRA)


def test_a_decimal_operations_literals_are_its_import() -> None:
    """A unary Decimal operation's literals restate its import's types,
    which its emitter reads to wrap and unwrap: held equal here."""
    seen = 0
    for spec in _HOSTED:
        low = spec.lowering
        if low.emitter != "_translate_decimal_unary":
            continue
        op, param, result = low.extra
        row = HOST_IMPORT_BY_NAME[op]
        assert op == spec.name and row.params == (param,) and row.results == (result,)
        seen += 1
    assert seen > 0


_AT_THE_CALL = [
    spec for spec in _ALL
    if isinstance(spec.lowering, (Inline, Host))
    and spec.lowering.binding in (Binding.ARGS_AT, Binding.ARGS_SITE)
]


@pytest.mark.parametrize("spec", _AT_THE_CALL, ids=_ids(_AT_THE_CALL))
def test_the_call_is_the_site_of_its_checks(spec: BuiltinSpec) -> None:
    """`ARGS_AT` and `ARGS_SITE` hand the call to the emitter as the site of
    the check it compiles, so every check in the probe is recorded at the
    call."""
    source = probe_source(spec)
    _, _, _, call = probe_parts(spec)
    line = source.splitlines().index(f"  {call}") + 1
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    found = pipeline.checks(compiled.result, function="probe")
    assert found, "the call compiled to no check"
    assert {(c.line, c.column) for c in found} == {(line, 3)}


@pytest.mark.parametrize("name", sorted(INTRINSICS))
def test_a_call_at_another_arity_is_an_ordinary_call(name: str) -> None:
    """The dispatch lowers a name in place only at its record's arity: one
    argument more falls through to the ordinary call, which code generation
    without the checker's tables skips as a call to no function (E602)."""
    intrinsic = INTRINSICS[name]
    args = ", ".join(["1"] * (intrinsic.arity + 1))
    source = _fn_source("probe", "@Unit", "Int", "effects(pure)", f"{name}({args})")
    compiled = pipeline.compile(source, checked=False)
    skips = [d for d in compiled.diagnostics if d.error_code == "E602"]
    assert len(skips) == 1, [(d.error_code, d.description) for d in compiled.diagnostics]
    assert f"call target {name!r} not registered" in skips[0].description


# ---------------------------------------------------------------------
# The hosts that bind a host-imported built-in's imports
# ---------------------------------------------------------------------


class _RecordingLinker:
    """Records what a `register_<family>` defines; binds nothing."""

    def __init__(self) -> None:
        self.defined: set[str] = set()

    def define_func(self, module: str, name: str, *_args: object,
                    **_kwargs: object) -> None:
        assert module == "vera"
        self.defined.add(name)


def _python_host_defines(family: str, ops: set[str]) -> set[str]:
    from vera.runtime import decimal, html, json, map, math, md, regex, set as set_mod

    linker: Any = _RecordingLinker()
    if family == "md":
        md.register_md(linker)
    elif family == "regex":
        regex.register_regex(linker)
    elif family == "map":
        map.register_map(linker, ops)
    elif family == "set":
        set_mod.register_set(linker, ops)
    elif family == "decimal":
        store: dict[int, PyDecimal] = {}
        decimal.register_decimal(linker, ops, store, {})
    elif family == "json":
        json.register_json(linker, ops)
    elif family == "html":
        html.register_html(linker, ops)
    elif family == "math":
        math.register_math(linker, ops)
    else:  # pragma: no cover — a family with no binder
        raise AssertionError(f"no Python binder for family {family!r}")
    return linker.defined


def _served_imports(spec: BuiltinSpec) -> set[str]:
    compiled = pipeline.compile(probe_source(spec))
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    return {n for n in _declared(compiled.wat) if host_import(n).serves == spec.name}


@pytest.mark.parametrize("spec", _HOSTED, ids=_ids(_HOSTED))
def test_python_host_binds_the_import(spec: BuiltinSpec) -> None:
    assert isinstance(spec.lowering, Host)
    names = _served_imports(spec)
    assert names
    assert names <= _python_host_defines(spec.lowering.family, names)


def _js_binds(name: str, runtime: str) -> bool:
    n = re.escape(name)
    forms = (
        rf"needed\.has\(['\"]{n}['\"]\)",
        rf"imports\.vera\.{n}\b",
        rf"imports\.vera\[['\"]{n}['\"]\]",
        rf"^\s*{n}\s*:",
        rf"\^{n}\\\$",
    )
    return any(re.search(form, runtime, re.MULTILINE) for form in forms)


@pytest.mark.parametrize("spec", _HOSTED, ids=_ids(_HOSTED))
def test_browser_runtime_names_the_import(spec: BuiltinSpec) -> None:
    runtime = (ROOT / "vera" / "browser" / "runtime.mjs").read_text(encoding="utf-8")
    rows = [row for row in HOST_IMPORTS if row.serves == spec.name]
    assert rows
    for row in rows:
        assert _js_binds(row.name, runtime), row.name


def test_the_python_hosts_tags_are_the_registrys() -> None:
    from vera.runtime.collections import _VAL_WASM_TYPES

    assert set(_VAL_WASM_TYPES) == set(TAG_TYPES)
    for tag, types in TAG_TYPES.items():
        assert [str(t) for t in _VAL_WASM_TYPES[tag]] == list(types)


# ---------------------------------------------------------------------
# Each reader reads the registry
# ---------------------------------------------------------------------


def _replaced(spec: BuiltinSpec, **changes: Any) -> BuiltinSpec:
    import dataclasses

    return dataclasses.replace(spec, **changes)


def test_the_type_env_registers_the_records(monkeypatch: pytest.MonkeyPatch) -> None:
    """A record's signature is the function the checker registers."""
    from vera.environment import TypeEnv

    spec = BUILTINS["string_length"]
    moved = _replaced(spec, signature=_replaced(spec.signature, ret=STRING))
    monkeypatch.setitem(BUILTINS, "string_length", moved)  # type: ignore[arg-type]
    assert TypeEnv().functions["string_length"].return_type == STRING


def test_the_type_env_holds_every_record_in_order() -> None:
    """Every field of each `FunctionInfo` is its record's, the type
    variables namespaced (#970)."""
    from vera.environment import TypeEnv
    from vera.types import BUILTIN_TYPEVAR_MARKER, TypeVar

    functions = TypeEnv().functions
    assert list(functions) == list(BUILTINS)
    for name, spec in BUILTINS.items():
        info, sig = functions[name], spec.signature
        renamed: dict[str, Type] = {
            v: TypeVar(v + BUILTIN_TYPEVAR_MARKER) for v in sig.forall or ()}
        assert info.forall_vars == (
            tuple(v + BUILTIN_TYPEVAR_MARKER for v in sig.forall)
            if sig.forall else None)
        assert info.param_types == tuple(substitute(p, renamed) for p in sig.params)
        assert info.return_type == substitute(sig.ret, renamed)
        assert info.effect == sig.effect
        assert [(c.ability_name, c.type_var) for c in info.forall_constraints] == [
            (a, v + BUILTIN_TYPEVAR_MARKER) for a, v in sig.constraints]


def test_the_dispatch_reads_the_registry(monkeypatch: pytest.MonkeyPatch) -> None:
    """The intrinsic a name lowers through is its record's emitter."""
    calls: list[str] = []

    def spy(self: WasmContext, *args: object, **kwargs: object) -> list[str]:
        calls.append("spy")
        return ["i64.const 7"]

    monkeypatch.setattr(WasmContext, "_spy_emitter", spy, raising=False)
    monkeypatch.setitem(  # type: ignore[arg-type]
        INTRINSICS, "string_length",
        registry.Intrinsic("string_length", 1, Inline("_spy_emitter")))
    compiled = pipeline.compile(probe_source(BUILTINS["string_length"]))
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert calls == ["spy"]
    assert "i64.const 7" in compiled.wat


def test_the_declarations_render_from_the_registry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A family's style is the line the module declares: written apart,
    `md_render`'s two results are the same type, in another text."""
    monkeypatch.setitem(registry._STYLE, "md", registry.Style.SEPARATE)  # type: ignore[index]
    compiled = pipeline.compile(probe_source(BUILTINS["md_render"]))
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    line = _declared(compiled.wat)["md_render"]
    assert line.endswith("(func $vera.md_render (param i32) (result i32) (result i32)))")


def test_the_family_sets_are_the_registrys() -> None:
    """compilability.py's host-import family sets are derived, not written."""
    from vera.codegen.compilability import CompilabilityMixin

    source = (ROOT / "vera" / "codegen" / "compilability.py").read_text(encoding="utf-8")
    tree = pyast.parse(source)
    family_sets = {
        node.targets[0].id: node.value
        for node in pyast.walk(tree)
        if isinstance(node, pyast.Assign) and len(node.targets) == 1
        and isinstance(node.targets[0], pyast.Name)
        and re.fullmatch(r"_[A-Z]+_BUILTINS", node.targets[0].id)
    }
    assert family_sets, "no family set in compilability.py"
    for attr, value in family_sets.items():
        derived = (isinstance(value, pyast.Call)
                   and pyast.unparse(value.func).endswith("host_family_builtins"))
        assert derived, f"{attr} is written by hand"
        family = attr[1:-len("_BUILTINS")].lower()
        assert getattr(CompilabilityMixin, attr) == registry.host_family_builtins(family)
    hosted = {spec.lowering.family for spec in _HOSTED}
    assert {a[1:-len("_BUILTINS")].lower() for a in family_sets} == hosted


def test_builtins_json_reads_the_registry(monkeypatch: pytest.MonkeyPatch) -> None:
    from vera.introspect import builtins_payload

    monkeypatch.setitem(  # type: ignore[arg-type]
        BUILTINS, "abs", _replaced(BUILTINS["abs"], since="9.9.9"))
    by_name = {i["name"]: i for i in builtins_payload()["items"]}
    assert by_name["abs"]["since"] == "9.9.9"


def test_a_builtins_version_lives_in_its_record() -> None:
    """`vera/_since.py` keeps effects, abilities and codes, not built-ins."""
    from vera._since import SINCE

    assert set(SINCE) & set(BUILTINS) == set()
    assert all(re.fullmatch(r"\d+\.\d+\.\d+", spec.since) for spec in _ALL)


def test_the_domain_has_one_source() -> None:
    """A domain is written in its record; `builtin_domains` derives its own."""
    from vera.builtin_domains import BUILTIN_DOMAINS

    with_domain = [spec for spec in _ALL if spec.domain is not None]
    assert [d.name for d in BUILTIN_DOMAINS] == [s.name for s in with_domain]
    for domain, spec in zip(BUILTIN_DOMAINS, with_domain, strict=True):
        assert spec.domain is not None
        assert domain.requires == spec.domain.requires
        assert domain.params == ", ".join(
            f"@{_surface(t, {}, '')}" for t in spec.signature.params)
    # The base wrote this one by hand; the derivation must give its text.
    by_name = {d.name: d for d in BUILTIN_DOMAINS}
    assert by_name["string_char_code"].params == "@String, @Int"
    for spec in with_domain:
        assert spec.domain is not None
        holders = [
            path.relative_to(ROOT).as_posix()
            for path in sorted((ROOT / "vera").rglob("*.py"))
            if spec.domain.requires in path.read_text(encoding="utf-8")
        ]
        assert holders == ["vera/builtins.py"]


def test_a_builtins_trap_rows_are_its_emitters() -> None:
    """The trap kind is `TRAP_EMITTERS`' row for the record's emitter."""
    from vera.trap_registry import TRAP_EMITTERS

    for key, row in TRAP_EMITTERS.items():
        function = key.split(":", 1)[1]
        owners = [i for i in INTRINSICS.values() if i.lowering.emitter == function]
        for intrinsic in owners:
            module = inspect.getmodule(getattr(WasmContext, function))
            assert module is not None
            assert key == f"{module.__name__.removeprefix('vera.').replace('.', '/')}.py:{function}"
            assert row in registry.trap_rows(intrinsic.name)
    assert [r.kind for r in registry.trap_rows("abs")] == ["overflow"]
    assert registry.trap_rows("string_length") == []


# ---------------------------------------------------------------------
# What no record decides: the explicit branches, the ability
# intrinsics, the ownership rule
# ---------------------------------------------------------------------


_APPLY_FN = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn twice(@IntToInt, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@IntToInt.0, apply_fn(@IntToInt.0, @Int.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  twice(fn(@Int -> @Int) effects(pure) { @Int.0 + 3 }, 10)
}
"""

_STATE_CLAUSES = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 6) {
    get(@Unit) -> { resume(@Int.0 * 7) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
"""

_STATE_OPS = """\
private fn bump(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{
  put(get(()) + 41)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(@Int.0) },
    put(@Int) -> { resume(()) }
  } in {
    bump(());
    get(())
  }
}
"""

_THROW = """\
private fn fail(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(<Exn<Int>>)
{
  throw(@Int.0 + 1)
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[Exn<Int>] {
    throw(@Int) -> { @Int.0 }
  } in {
    fail(41)
  }
}
"""

_GENERIC = """\
private forall<T> fn pick(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(7, 9)
}
"""


@pytest.mark.parametrize(
    ("source", "value", "wat"),
    [
        pytest.param(_APPLY_FN, 16, "call_indirect", id="apply_fn"),
        pytest.param(_STATE_CLAUSES, 42, "i64.mul", id="state_clause_and_resume"),
        pytest.param(_STATE_OPS, 42, "call $vera.state_put_Int", id="effect_op_put_get"),
        pytest.param(_THROW, 42, "throw $exn_Int", id="effect_op_throw"),
        pytest.param(_GENERIC, 7, "call $pick$Int", id="generic_rewrite"),
    ],
)
def test_an_explicit_branch_keeps_its_lowering(source: str, value: int, wat: str) -> None:
    """The dispatch's branches that read no record lower as before."""
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert wat in compiled.wat
    ran = pipeline.run(compiled.result, "main")
    assert ran.value == value


def test_the_ability_intrinsics_are_not_functions() -> None:
    from vera.environment import TypeEnv
    from vera.introspect import builtins_payload

    env = TypeEnv()
    published = {i["name"] for i in builtins_payload()["items"]}
    for name, intrinsic in ABILITY_INTRINSICS.items():
        assert name not in BUILTINS and name not in env.functions
        assert name not in published
        ability = env.abilities[intrinsic.ability]
        assert len(ability.operations[name].param_types) == intrinsic.arity
        assert INTRINSICS[name].lowering == intrinsic.lowering


_LOCAL_SHOW = """\
private fn show(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  "mine"
}

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(5)
}
"""


def test_a_local_fn_show_owns_the_name() -> None:
    """E151 does not refuse it, and the module's own calls reach it."""
    checked = pipeline.check(_LOCAL_SHOW)
    assert checked.ok, [d.description for d in checked.errors]
    assert pipeline.run(_LOCAL_SHOW, "main").value == "mine"


_LIB_SHOW = """\
module lib;

private fn show(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  "lib"
}

public fn touch(@Int -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  show(@Int.0)
}
"""

_MAIN_SHOW = """\
import lib(touch);

public fn main(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  string_concat(show(5), touch(5))
}
"""


def test_a_modules_private_show_does_not_displace_the_intrinsic(tmp_path: Path) -> None:
    """#1299: the importer's bare `show(5)` is the ability operation, and the
    module's own call is its private function: "5" then "lib"."""
    verify_errors, result, codegen_errors = build_multi_module(
        tmp_path, {"lib.vera": _LIB_SHOW, "main.vera": _MAIN_SHOW})
    assert not codegen_errors and not verify_errors
    assert module_value(result, "main") == ("ok", "5lib")


# ---------------------------------------------------------------------
# The registry's own shape
# ---------------------------------------------------------------------


def test_the_prelude_records_are_the_prelude_bodies() -> None:
    """A `Prelude` record's arity, and a non-generic one's types, are its body's."""
    from vera import prelude

    from vera.ast import FnDecl, format_type_expr

    bodies: dict[str, FnDecl] = {}
    for block in (prelude._OPTION_COMBINATORS, prelude._RESULT_COMBINATORS,
                  prelude._JSON_COMBINATORS, prelude._HTML_COMBINATORS):
        for tld in prelude._parse_source(block).declarations:
            if isinstance(tld.decl, FnDecl):
                bodies[tld.decl.name] = tld.decl

    def written(te: Any) -> str:
        return format_type_expr(te).replace("@", "")

    prelude_specs = [spec for spec in _ALL if isinstance(spec.lowering, Prelude)]
    assert {s.name for s in prelude_specs} == prelude.overridable_builtin_names()
    for spec in prelude_specs:
        decl = bodies[spec.name]
        assert len(decl.params) == spec.arity, spec.name
        if spec.signature.forall is None:
            assert [written(p) for p in decl.params] == [
                _surface(p, {}, "F") for p in spec.signature.params], spec.name
            assert written(decl.return_type) == _surface(spec.signature.ret, {}, "F")


def _families() -> Iterator[str]:
    return (f.name for f in HOST_FAMILIES)


def _io_call(op: str) -> str:
    """A call of IO operation *op* with literal arguments, its result bound."""
    from vera.environment import TypeEnv

    info = TypeEnv().effects["IO"].operations[op]
    literal = {"String": '"x"', "Unit": "()", "Nat": "1", "Int": "1"}
    args = ", ".join(literal[_surface(t, {}, "")] for t in info.param_types)
    ret = _surface(info.return_type, {}, "")
    if ret in ("Unit", "Never"):
        return f"IO.{op}({args})"
    return f"let @{ret} = IO.{op}({args});\n  ()"


_IO_ROWS = [row for row in HOST_IMPORTS if row.family == "io"]


@pytest.mark.parametrize("row", _IO_ROWS, ids=[row.name for row in _IO_ROWS])
def test_an_import_the_host_allocates_through_exports_the_allocator(row: Any) -> None:
    """A module calling one IO operation exports `alloc`, which the host
    builds the result in, exactly when the operation's row needs it."""
    source = _fn_source("main", "@Unit", "Unit", "effects(<IO>)", _io_call(row.name))
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert (row.name in _declared(compiled.wat)) is True
    assert ('(export "alloc" (func $alloc))' in compiled.wat) is row.needs_alloc


def _served_effects() -> list[str]:
    return sorted({row.serves.split(".")[0] for row in HOST_IMPORTS if "." in row.serves})


@pytest.mark.parametrize("effect", _served_effects())
def test_a_host_effects_operations_each_have_a_row(effect: str) -> None:
    """An effect operation the host implements is one operation in its
    `EffectInfo` and one row serving it: an effect with one row has one for
    every operation, and every row names an operation the effect has."""
    from vera.environment import TypeEnv

    ops = set(TypeEnv().effects[effect].operations)
    served = {row.serves.split(".", 1)[1] for row in HOST_IMPORTS
              if row.serves.startswith(f"{effect}.")}
    assert served == ops


def test_the_host_families_are_the_imports_families() -> None:
    assert [f for f in _families() if any(r.family == f for r in HOST_IMPORTS)] == list(
        _families())
    assert all(row.instance in ("", "k", "v", "kv", "e", CELL) for row in HOST_IMPORTS)
