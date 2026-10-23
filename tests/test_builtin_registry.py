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
- for a `Host` record, the same call in a function code generation drops
  (E602) declares what no call declares: a module declares the imports its
  emitted code calls;
- E151 refuses a declaration of its name, except a `Prelude` record's, whose
  declaration replaces the prelude's body and is accepted;
- its emitter exists on `WasmContext` and takes the arguments its record's
  convention hands it, at the record's arity;
- for a `Host` record, the Python host's binding table binds exactly the
  imports the compiled call declares, each with its declaration's types, and
  the browser runtime's roster lists their rows.

The hosts read the registry too: the Python host binds a module's imports
through the binder of each row's family, and refuses one no row declares or
no binder defines; the browser runtime's roster is the registry's rendering,
and every corpus module's imports are among its rows; each WASI world's gate
refuses a module declaring an import whose row's worlds lack it, so the
world's import parser reads only rows it implements.

The cells that pin each reader to the registry change a record and watch
the reader follow: the checker's `FunctionInfo`, the dispatch, the
declarations, `vera builtins --json`, and the two tables the registry
absorbed (`since` and the domain).  The cells after them hold the
dispatch's explicit branches, the ownership rule (#1299) and the ability
intrinsics to their behaviour, which no record decides.
"""

from __future__ import annotations

import ast as pyast
import functools
import inspect
import re
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import pytest

from tests.codegen_helpers import skip_map_inserts  # noqa: F401  (the fixture)
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
    "vera/runtime/decimal.py",
    "vera/runtime/html.py",
    "vera/runtime/json.py",
    "vera/runtime/math.py",
    "vera/runtime/md.py",
    "vera/runtime/regex.py",
    "vera/runtime/async_http.py",
    "vera/runtime/db.py",
    "vera/runtime/http.py",
    "vera/runtime/inference.py",
    "vera/runtime/random.py",
    "vera/runtime/state.py",
    "vera/browser/runtime.mjs",
    "vera/codegen/api.py",
    "vera/codegen/wasi.py",
    "vera/codegen/core.py",
    "vera/codegen/functions.py",
    "vera/codegen/closures.py",
    "vera/wasm/context.py",
    "vera/monomorphize.py",
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
  let @Result<Array<Byte>, String> = IO.read_bytes(@String.1);
  let @Result<Unit, String> = IO.write_bytes(@String.1, []);
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
#: order, as the base (313c04db) compiled them, with the row added since
#: (`hash_key`, #1736: the JSON host builds a `Map<String, Json>`) where the
#: registry's order puts it.
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
    '(import "vera" "hash_key" (func $vera.hash_key (result i64)))',
    '(import "vera" "contract_fail" (func $vera.contract_fail (param i32 i32)))',
    '(import "vera" "trap" (func $vera.trap (param i32 i32 i32)))',
)

#: The declarations `_EVERY_EFFECT` makes, line for line and in order, as
#: the base compiled them, with the rows added since (`read_bytes` and
#: `write_bytes`, #1711) where the registry's order puts them.
_EVERY_EFFECT_IMPORTS = (
    '(import "vera" "args" (func $vera.args (result i32 i32)))',
    '(import "vera" "exit" (func $vera.exit (param i64)))',
    '(import "vera" "get_env" (func $vera.get_env (param i32 i32) (result i32)))',
    '(import "vera" "print" (func $vera.print (param i32 i32)))',
    '(import "vera" "read_bytes" (func $vera.read_bytes (param i32 i32) (result i32)))',
    '(import "vera" "read_char" (func $vera.read_char (result i32)))',
    '(import "vera" "read_file" (func $vera.read_file (param i32 i32) (result i32)))',
    '(import "vera" "read_line" (func $vera.read_line (result i32 i32)))',
    '(import "vera" "sleep" (func $vera.sleep (param i64)))',
    '(import "vera" "stderr" (func $vera.stderr (param i32 i32)))',
    '(import "vera" "time" (func $vera.time (result i64)))',
    '(import "vera" "write_bytes" (func $vera.write_bytes (param i32 i32 i32 i32) (result i32)))',
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
# A call code generation never emits declares nothing
# ---------------------------------------------------------------------


#: A statement code generation cannot lower, an array of closures (E602), so
#: the function holding it is dropped after the pre-scan has walked its body.
#: It calls no host import.
_DROPPER = "let @Array<Dropper> = [fn(@Int -> @Int) effects(pure) { @Int.0 }];"

#: A `main` that calls no host import, so no import a call declares is one
#: `main` declares too.
_ZERO = _fn_source("main", "@Unit", "Int", "effects(pure)", "0")

_PRINTS = """\
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("hi\\n")
}
"""


def _dropped_source(formals: str, ret: str, effect: str, body: str,
                    decls: str = "") -> str:
    """A program whose public `dead` holds *body* after the dropper, beside
    a `main` that calls no host import."""
    return (f"{decls}type Dropper = fn(Int -> Int) effects(pure);\n\n"
            + _fn_source("dead", formals, ret, effect, f"{_DROPPER}\n  {body}")
            + "\n" + _ZERO)


def _module_declarations(source: str, *, dropped: bool) -> dict[str, str]:
    """The declarations of *source*'s module, its `dead` dropped by code
    generation (E602) or compiled."""
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert ("dead" in compiled.exports) is not dropped
    assert ("E602" in {d.error_code for d in compiled.warnings}) is dropped
    return _declared(compiled.wat)


@functools.cache
def _no_call_declarations() -> dict[str, str]:
    """What the module declares with no call in `dead`: nothing."""
    return _module_declarations(
        _dropped_source("@Int", "Int", "effects(pure)", "@Int.0"), dropped=True)


@pytest.mark.parametrize("spec", _HOSTED, ids=_ids(_HOSTED))
def test_a_dropped_call_declares_nothing(spec: BuiltinSpec) -> None:
    """A call in a function code generation drops declares what no call
    declares, and the same function compiled declares the call's import: a
    module declares the imports its emitted code calls, and the pre-scan's
    walk of a body is no source of them (it declared the call's row, or for
    a `Map` or `Set` row raised the wrap table's flag, #735)."""
    aliases, formals, ret, call = probe_parts(spec)
    decls = "".join(f"type {n} = {d};\n\n" for n, d in aliases.items())
    effect = _effect_clause(spec)
    # `dead` also takes a value of its return type, which the module with
    # no call returns: the two mention the same types, so a prelude body a
    # type brings in (a `Json`'s, an `HtmlNode`'s) is compiled in both.
    both = f"{formals}, @{ret}"
    dropped = _dropped_source(both, ret, effect, call, decls)
    without = _dropped_source(both, ret, effect, f"@{ret}.0", decls)
    assert (_module_declarations(dropped, dropped=True)
            == _module_declarations(without, dropped=True))
    kept = decls + _fn_source("dead", formals, ret, effect, call) + "\n" + _ZERO
    assert any((row := host_import(name)) is not None and row.serves == spec.name
               for name in _module_declarations(kept, dropped=False))


#: The rows a host effect operation's call declares, the fused `async` forms
#: and `await` among them; a `State` cell's are declared by its handler or
#: its effect row, before the function is emitted.
_OPERATION_ROWS = [
    row for row in HOST_IMPORTS
    if row.serves == "await"
    or row.serves.split(".")[0] in ("IO", "Http", "Inference", "DB", "Random")]

_FUTURE = "@Future<Result<String, String>>"


def _operation_body(row: Any) -> tuple[str, str]:
    """The effect clause, and a body calling *row*'s operation with literal
    arguments."""
    from vera.environment import TypeEnv

    if row.serves == "await":
        return "effects(<Http, Async>)", (
            f'let {_FUTURE} = async(Http.get("x"));\n'
            f"  let @Result<String, String> = await({_FUTURE}.0);\n  ()")
    effect, op = row.serves.split(".")
    info = TypeEnv().effects[effect].operations[op]
    literal = {"String": '"x"', "Unit": "()", "Nat": "1", "Int": "1"}
    written = [_surface(t, {}, "") for t in info.param_types]
    args = ", ".join("[]" if w.startswith("Array<") else literal[w] for w in written)
    call = f"{effect}.{op}({args})"
    if row.family == "async":
        return "effects(<Http, Async>)", f"let {_FUTURE} = async({call});\n  ()"
    ret = _surface(info.return_type, {}, "")
    if ret in ("Unit", "Never"):
        return f"effects(<{effect}>)", call
    return f"effects(<{effect}>)", f"let @{ret} = {call};\n  ()"


@pytest.mark.parametrize("row", _OPERATION_ROWS, ids=[row.name for row in _OPERATION_ROWS])
def test_a_dropped_operation_declares_nothing(row: Any) -> None:
    """The same for each host effect operation's row."""
    effect, body = _operation_body(row)
    dropped = _dropped_source("@Int", "Unit", effect, body)
    assert _module_declarations(dropped, dropped=True) == _no_call_declarations()
    kept = _fn_source("dead", "@Int", "Unit", effect, body) + "\n" + _ZERO
    assert row.name in _module_declarations(kept, dropped=False)


# ---------------------------------------------------------------------
# A declaration of the built-in's name
# ---------------------------------------------------------------------


_PRELUDE_VALUES = {
    "Int": "0", "Bool": "false", "String": '""', "Option": "None",
    "Result": 'Err("")', "Array": '[""]',
}


@pytest.mark.parametrize("spec", _ALL, ids=_IDS)
def test_a_declaration_of_its_name(spec: BuiltinSpec) -> None:
    """E151, for a prelude body's name as for every other built-in's
    (#1469 reserved the prelude's function names)."""
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
    argument more is a call to no function of that arity, which the check
    refuses (E201, or E240 for an ability's operation), so code generation
    never meets it."""
    intrinsic = INTRINSICS[name]
    args = ", ".join(["1"] * (intrinsic.arity + 1))
    source = _fn_source("probe", "@Unit", "Int", "effects(pure)", f"{name}({args})")
    errors = pipeline.check(source).errors
    refusals = [d for d in errors if d.error_code in ("E201", "E240")]
    assert len(refusals) == 1, [(d.error_code, d.description) for d in errors]
    assert (f"{name!r} expects {intrinsic.arity} argument(s), got "
            f"{intrinsic.arity + 1}") in refusals[0].description


# ---------------------------------------------------------------------
# The hosts that bind a host-imported built-in's imports
# ---------------------------------------------------------------------


class _RecordingLinker:
    """Records each import a binder defines, with its types; binds nothing."""

    def __init__(self) -> None:
        self.defined: dict[str, tuple[list[str], list[str]]] = {}

    def define_func(self, module: str, name: str, ty: Any, *_args: object,
                    **_kwargs: object) -> None:
        assert module == "vera" and name not in self.defined, name
        self.defined[name] = ([str(p) for p in ty.params], [str(r) for r in ty.results])


def _line_types(line: str) -> tuple[list[str], list[str]]:
    """The parameter and result types a declaration line writes."""
    params = [t for group in re.findall(r"\(param ([^()]*)\)", line) for t in group.split()]
    results = [t for group in re.findall(r"\(result ([^()]*)\)", line) for t in group.split()]
    return params, results


def _host_env(own_lines: dict[str, str], state_types: list[Any]) -> Any:
    """A `HostEnv` whose own bindings stand in for `execute()`'s closures,
    each typed as the module declares it."""
    import wasmtime

    from vera.codegen.api import HostEnv

    def func_type(line: str) -> Any:
        params, results = _line_types(line)
        return wasmtime.FuncType([getattr(wasmtime.ValType, p)() for p in params],
                                 [getattr(wasmtime.ValType, r)() for r in results])

    own = {name: (func_type(line), lambda *_a: None) for name, line in own_lines.items()}
    return HostEnv(own=own, state_types=state_types, initial_state=None, state_store={},
                   env_vars={}, decimal_store={}, future_store={}, host_store_refs={})


_OWN_FAMILIES = frozenset({"io", "contract", "trap", "wrap"})


def _bound(declared: dict[str, str],
           state_types: list[Any] | None = None) -> dict[str, tuple[list[str], list[str]]]:
    """What `bind_host_imports` defines for a module that declares
    *declared*, `execute()`'s own bindings stood in for."""
    from vera.codegen.api import bind_host_imports

    own = {n: line for n, line in declared.items()
           if (row := host_import(n)) is not None and row.family in _OWN_FAMILIES}
    env = _host_env(own, state_types or [])
    linker: Any = _RecordingLinker()
    try:
        bind_host_imports(linker, [("vera", n) for n in declared], env)
    finally:
        if env.executor is not None:
            env.executor.shutdown(wait=False)
    return linker.defined


@pytest.mark.parametrize("spec", _HOSTED, ids=_ids(_HOSTED))
def test_python_host_binds_the_import(spec: BuiltinSpec) -> None:
    """The Python host binds exactly the imports a call to the record
    declares, each through its family's binder in `HOST_BINDERS`, with the
    types its declaration line writes."""
    compiled = pipeline.compile(probe_source(spec))
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    declared = _declared(compiled.wat)
    assert any(host_import(n).serves == spec.name for n in declared)
    bound = _bound(declared)
    assert set(bound) == set(declared)
    for name, line in declared.items():
        assert bound[name] == _line_types(line), name


def test_every_family_has_a_binder() -> None:
    from vera.codegen.api import HOST_BINDERS

    assert set(HOST_BINDERS) == {family.name for family in HOST_FAMILIES}


def _with_import(wat: str, line: str) -> str:
    """*wat* with one more import declaration, after its first."""
    at = wat.index('  (import "vera" ')
    return wat[:at] + line + "\n" + wat[at:]


_SIN = """\
public fn main(-> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{
  sin(1.0)
}
"""


def test_an_import_no_row_declares_is_refused_naming_it() -> None:
    import dataclasses

    from vera.codegen.api import HostBindingError, execute

    compiled = pipeline.compile(_SIN).result
    unknown = dataclasses.replace(compiled, wat=_with_import(
        compiled.wat, '  (import "vera" "no_such_import" (func $vera.no_such_import))'))
    with pytest.raises(HostBindingError, match=r"vera\.no_such_import, which no row"):
        execute(unknown)
    assert execute(compiled).value == pytest.approx(0.8414709848078965)


def test_an_import_no_binder_defines_is_refused_naming_its_row(
        monkeypatch: pytest.MonkeyPatch) -> None:
    from vera.codegen import api

    binders = dict(api.HOST_BINDERS)
    binders["math"] = lambda linker, names, env: None
    monkeypatch.setattr(api, "HOST_BINDERS", binders)
    with pytest.raises(api.HostBindingError, match=r"binds no vera\.sin, an import of the"
                       r" registry's math row sin, which serves sin"):
        api.execute(pipeline.compile(_SIN).result)


def _roster() -> list[tuple[str, str, str]]:
    """The browser runtime's roster: each row's name, family and instance."""
    text = (ROOT / "vera" / "browser" / "runtime.mjs").read_text(encoding="utf-8")
    block = text.split("// render_lists:begin host-imports\n")[1].split(
        "// render_lists:end host-imports\n")[0]
    return re.findall(r'^  \["([^"]+)", "([^"]+)", "([^"]*)"\],$', block, re.MULTILINE)


def _roster_row(name: str, rows: dict[str, tuple[str, str]]) -> str | None:
    """The roster row a declared import is an instance of, as the runtime's
    `hostImportRow` reads it."""
    base = name.split("$")[0]
    if base in rows:
        return base
    return next((row for row, (_family, instance) in rows.items()
                 if instance == CELL and name.startswith(row + "_")), None)


def test_the_roster_is_the_registrys() -> None:
    """The browser runtime's roster lists every row, in the registry's
    order, with its family and instance."""
    assert _roster() == [(row.name, row.family, row.instance) for row in HOST_IMPORTS]


@pytest.mark.parametrize("spec", _HOSTED, ids=_ids(_HOSTED))
def test_browser_runtime_lists_the_import(spec: BuiltinSpec) -> None:
    rows = {name: (family, instance) for name, family, instance in _roster()}
    served = [row for row in HOST_IMPORTS if row.serves == spec.name]
    assert served
    for row in served:
        assert rows[row.name][0] == spec.lowering.family, row.name


_CORPUS = sorted(
    [*(ROOT / "examples").glob("*.vera"), *(ROOT / "tests" / "conformance").glob("*.vera")])


@pytest.mark.parametrize("path", _CORPUS, ids=[p.name for p in _CORPUS])
def test_a_corpus_modules_imports_are_roster_rows(path: Path) -> None:
    """Every `vera` import a corpus program's module declares is a row the
    browser runtime's roster lists, and the Python host binds it."""
    compiled = pipeline.compile(path.read_text(encoding="utf-8"), file=str(path),
                                root=path.parent)
    if compiled._result is None or not compiled.result.ok:
        pytest.skip("the program does not compile (a negative fixture)")
    declared = _declared(compiled.result.wat)
    rows = {name: (family, instance) for name, family, instance in _roster()}
    for name in declared:
        assert _roster_row(name, rows) is not None, name
    assert set(_bound(declared, compiled.result.state_types)) == set(declared)


def test_the_browser_refuses_an_import_no_row_declares(tmp_path: Path) -> None:
    import shutil
    import subprocess

    import wasmtime

    node = shutil.which("node")
    if node is None:
        pytest.skip("Node.js is not on PATH")
    compiled = pipeline.compile(_SIN).result
    wasm = tmp_path / "unknown.wasm"
    wasm.write_bytes(wasmtime.wat2wasm(_with_import(
        compiled.wat, '  (import "vera" "no_such_import" (func $vera.no_such_import))')))
    proc = subprocess.run(
        [node, str(ROOT / "vera" / "browser" / "harness.mjs"), str(wasm)],
        capture_output=True, text=True, encoding="utf-8", timeout=60, check=False)
    # The harness reports a module it cannot initialise on stderr.
    assert proc.returncode != 0 and proc.stdout == "", proc.stdout
    assert "vera.no_such_import, which no row of the built-in registry" in proc.stderr


def test_the_browser_refuses_an_import_it_leaves_unbound(tmp_path: Path) -> None:
    """A declared import of a row the runtime binds nothing for is refused,
    naming its row: run on a copy of the runtime whose roster holds one more
    row, a stand-in no binding serves, by a module that imports it."""
    import shutil
    import subprocess

    import wasmtime

    node = shutil.which("node")
    if node is None:
        pytest.skip("Node.js is not on PATH")
    browser = ROOT / "vera" / "browser"
    runtime = (browser / "runtime.mjs").read_text(encoding="utf-8")
    roster_end = ("].map(([name, family, instance]) => [name, { name, family, instance }]));\n"
                  "// render_lists:end host-imports\n")
    assert runtime.count(roster_end) == 1
    (tmp_path / "runtime.mjs").write_text(
        runtime.replace(roster_end, '  ["stand_in", "math", ""],\n' + roster_end),
        encoding="utf-8")
    shutil.copy(browser / "harness.mjs", tmp_path / "harness.mjs")
    compiled = pipeline.compile(_SIN).result
    wasm = tmp_path / "unbound.wasm"
    wasm.write_bytes(wasmtime.wat2wasm(_with_import(
        compiled.wat, '  (import "vera" "stand_in" (func $vera.stand_in))')))
    proc = subprocess.run(
        [node, str(tmp_path / "harness.mjs"), str(wasm)],
        capture_output=True, text=True, encoding="utf-8", timeout=60, check=False)
    assert proc.returncode != 0 and proc.stdout == "", proc.stdout
    assert ("the browser runtime binds no vera.stand_in, an import of the registry's"
            " math row stand_in") in proc.stderr


# ---------------------------------------------------------------------
# WASI: each row's worlds decide what the component refuses
# ---------------------------------------------------------------------


class _Module:
    """What the WASI gates read of a compiled module."""

    def __init__(self, lines: list[str]) -> None:
        self.wat = "\n".join(lines) + "\n"
        self.state_types: list[Any] = []


def _planted(row: Any) -> tuple[str, str]:
    """An import of *row* and its declaration: the row's own name, or its
    `State` cell's at `Int`."""
    if row.instance == CELL:
        name = f"{row.name}_Int"
        return name, next(line for line in registry.cell_lines("Int", "i64")
                          if f'"{name}"' in line)
    return row.name, import_line(row.name)


@pytest.mark.parametrize("world", [registry.WASI_CLI, registry.WASI_SERVER])
@pytest.mark.parametrize("row", HOST_IMPORTS, ids=[row.name for row in HOST_IMPORTS])
def test_wasi_follows_the_rows_worlds(row: Any, world: str) -> None:
    """Each world's gate refuses a module declaring an import of a row whose
    worlds lack it, naming the import (a flag family's and a cell's among
    them), and admits one whose row's worlds hold it, which the world's
    import parser then reads: no row reaches the parser's out-of-sync
    error."""
    from vera.codegen import wasi

    name, line = _planted(row)
    module: Any = _Module([line])
    cli = world == registry.WASI_CLI
    gate = wasi._gate_families if cli else wasi._gate_families_server
    if world not in row.wasi:
        # A cli-only IO operation is refused with its own reason.
        reason = None if cli else wasi._SERVER_REJECTED_OPS.get(name)
        with pytest.raises(ValueError, match=re.escape(reason or name)):
            gate(module)
        return
    gate(module)
    if cli:
        parsed = wasi._IMPORT_RE.match(line)
        assert parsed is not None and parsed.group(1) == name, line
        assert parsed.group(2) == wasi._expected_sig(wasi._OPS[name])
    else:
        assert set(wasi._parse_server_imports(module.wat)) == {name}


#: Modules whose one `Map`, `Set`, `Decimal` or math call is one code
#: generation never emits, under an `assume` or in a function it drops
#: (E602).  At 477f184a the cli world refused each, and with one set of the
#: imports in use the first three reached its import parser's out-of-sync
#: error, on the wrap table's helpers their bare `Map` or `Set` name raised.
#: The drop is injected (`skip_map_inserts`): the Array-keyed map or set the
#: dropped shapes were written with is refused at check now (E135, #1680).
_NEVER_EMITTED = {
    "assumed_map_contains": """\
public fn f(@Map<String, Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume(map_contains(@Map<String, Int>.0, "a"));
  7
}
""",
    "dropped_map_insert": """\
public fn g(@Map<Int, Int>, @Int -> @Map<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  map_insert(@Map<Int, Int>.0, @Int.0, 2)
}
""",
    "dropped_set_add": """\
public fn g(@Set<Int> -> @Set<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 1, 2);
  set_add(@Set<Int>.0, 3)
}
""",
    "assumed_sin": """\
public fn f(@Float64 -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  assume(sin(@Float64.0) < 2.0);
  7
}
""",
    "dropped_decimal_add": """\
public fn g(@Int -> @Decimal)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<Int, Int> = map_insert(map_new(), 1, @Int.0);
  decimal_add(decimal_from_int(1), decimal_from_int(2))
}
""",
}

_HANDLES = """\
public fn handle(@Request -> @Response)
  requires(true)
  ensures(true)
  effects(<HttpServer>)
{
  Response(200, map_new(), "hi")
}
"""


@pytest.mark.usefixtures("skip_map_inserts")
def test_repro_a_call_never_emitted_reaches_no_parser_error() -> None:
    """Each module, beside a `main` and beside a `handle`, compiles to a
    component for its world, and the cli world's runs: the call declares
    nothing, so neither world's gate refuses it, and no import reaches a
    parser that has no op for it."""
    from vera.codegen.wasi import emit_wasi_component
    from vera.runtime.wasi_host import execute_wasi_p2

    for shape, source in _NEVER_EMITTED.items():
        cli = pipeline.compile(source + "\n" + _PRINTS)
        assert cli.ok, (shape, [d.description for d in cli.diagnostics])
        dropped = "E602" in {d.error_code for d in cli.warnings}
        assert dropped is shape.startswith("dropped_"), shape
        assert isinstance(emit_wasi_component(cli.result, "cli"), str), shape
        assert execute_wasi_p2(cli.result).stdout == "hi\n", shape
        server = pipeline.compile(source + "\n" + _HANDLES)
        assert server.ok, (shape, [d.description for d in server.diagnostics])
        assert isinstance(emit_wasi_component(server.result, "server"), str), shape


def test_the_wasi_tables_are_the_rows_worlds() -> None:
    """The cli world's adapter ops are its rows, with their types; the server
    world keeps the rows both worlds implement and names a reason for each
    cli-only row it refuses, and implements no row of its own (a `Map` is
    the module's own code, #1676)."""
    from vera.codegen import wasi

    worlds = {row.name: set(row.wasi) for row in HOST_IMPORTS}
    assert set(wasi._OPS) == {n for n, w in worlds.items() if registry.WASI_CLI in w}
    for name, op in wasi._OPS.items():
        params, results = _line_types(import_line(name))
        assert (op.params, op.results) == (" ".join(params), " ".join(results)), name
    both = {registry.WASI_CLI, registry.WASI_SERVER}
    assert wasi._SERVER_IO_OPS == {n for n, w in worlds.items() if w == both}
    assert set(wasi._SERVER_REJECTED_OPS) == {
        n for n, w in worlds.items() if w == {registry.WASI_CLI}}
    assert {n for n, w in worlds.items() if w == {registry.WASI_SERVER}} == set()
    assert wasi._CLI_REFUSED == registry.wasi_refused(registry.WASI_CLI)
    assert wasi._SERVER_REFUSED == registry.wasi_refused(registry.WASI_SERVER)


def test_the_wasi_refusal_names_the_modules_imports() -> None:
    """The refusal lists a family's imports as the module declares them,
    families in the registry's order, and names no flag family's (the wrap
    table's helpers a `Decimal` declares)."""
    from vera.codegen.wasi import emit_wasi_component

    compiled = pipeline.compile("""\
public fn main(-> @Float64)
  requires(true)
  ensures(true)
  effects(pure)
{
  sin(decimal_to_float(decimal_from_int(1)))
}
""").result
    with pytest.raises(ValueError) as refused:
        emit_wasi_component(compiled)
    assert ("following host families: decimal (decimal_from_int, decimal_to_float);"
            " math (sin)") in str(refused.value)


# ---------------------------------------------------------------------
# The other readers PR B moved onto the registry
# ---------------------------------------------------------------------


def test_compile_result_carries_no_family_set() -> None:
    import dataclasses

    from vera.codegen.api import CompileResult

    assert [f.name for f in dataclasses.fields(CompileResult)
            if f.name.endswith("_ops_used")] == []


def test_the_return_tables_are_the_records() -> None:
    """`vera/monomorphize.py`'s two return tables are read from the records:
    no literal table is written, and every name is its record's,
    `string_length`'s `Nat` included (the historical `Int` it was named by
    kept two clone namers agreeing, and clone names now come from the
    checker's instantiation, #1679)."""
    from vera import monomorphize

    source = (ROOT / "vera" / "monomorphize.py").read_text(encoding="utf-8")
    for node in pyast.walk(pyast.parse(source)):
        if isinstance(node, (pyast.Assign, pyast.AnnAssign)):
            targets = node.targets if isinstance(node, pyast.Assign) else [node.target]
            names = {pyast.unparse(target) for target in targets}
            if names & {"_BUILTIN_VERA_RETURN_TYPES", "_BUILTIN_PARAMETERIZED_RETURNS"}:
                assert not isinstance(node.value, pyast.Dict), names
    assert not hasattr(monomorphize, "_HISTORICAL_RETURN_NAMES")
    assert monomorphize._BUILTIN_VERA_RETURN_TYPES["string_length"] == "Nat"
    assert BUILTINS["string_length"].signature.ret.name == "Nat"


def test_the_rendered_blocks_are_the_registrys() -> None:
    """The browser runtime's roster and spec §9's signature tables are what
    `scripts/render_lists.py` renders from the registry."""
    import importlib.util

    spec = importlib.util.spec_from_file_location("render_lists", ROOT / "scripts" / "render_lists.py")
    assert spec is not None and spec.loader is not None
    render_lists = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(render_lists)
    blocks, errors = render_lists.plan(ROOT)
    assert errors == []
    ours = [b for b in blocks if b.name == "host-imports" or b.name.startswith("signatures-")]
    assert len(ours) == 1 + len(render_lists.SIGNATURE_BLOCKS)
    assert [b.name for b in ours if b.current != b.new] == []


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


def test_one_set_holds_the_imports_the_emitted_code_calls() -> None:
    """Code generation keeps one set of the host imports in use, where it
    kept one per family: the emitters write it, each with the imports it
    calls, and the pre-scan writes nothing to it and keeps no family set of
    built-ins (#735)."""
    source = (ROOT / "vera" / "codegen" / "compilability.py").read_text(encoding="utf-8")
    assert not re.findall(r"^\s*_[A-Z]+_BUILTINS\s*=", source, re.MULTILINE)
    assert not re.findall(r"_host_imports_used\.(?:add|update)\(", source)
    generator = pipeline.compile(probe_source(BUILTINS["md_parse"])).generator
    assert generator is not None
    per_family = [a for a in vars(generator)
                  if re.fullmatch(r"_[a-z]+_(ops_used|imports)", a)]
    assert per_family == []
    assert "md_parse" in generator._host_imports_used


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
        pytest.param(_GENERIC, 7, "call $:pick$Int", id="generic_rewrite"),
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

    from vera.ast import FnDecl, format_type

    bodies: dict[str, FnDecl] = {}
    for block in (prelude._OPTION_COMBINATORS, prelude._RESULT_COMBINATORS,
                  prelude._JSON_COMBINATORS, prelude._HTML_COMBINATORS):
        for tld in prelude._parse_source(block).declarations:
            if isinstance(tld.decl, FnDecl):
                bodies[tld.decl.name] = tld.decl

    def written(te: Any) -> str:
        return format_type(te)

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
    written = [_surface(t, {}, "") for t in info.param_types]
    args = ", ".join("[]" if w.startswith("Array<") else literal[w] for w in written)
    ret = _surface(info.return_type, {}, "")
    if ret in ("Unit", "Never"):
        return f"IO.{op}({args})"
    return f"let @{ret} = IO.{op}({args});\n  ()"


_IO_ROWS = [row for row in HOST_IMPORTS if row.family == "io"]


@pytest.mark.parametrize("row", _IO_ROWS, ids=[row.name for row in _IO_ROWS])
def test_an_import_the_host_allocates_through_exports_the_allocator(row: Any) -> None:
    """A module calling one IO operation exports `vera.alloc`, which the host
    builds the result in, exactly when the operation's row needs it."""
    source = _fn_source("main", "@Unit", "Unit", "effects(<IO>)", _io_call(row.name))
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert (row.name in _declared(compiled.wat)) is True
    assert ('(export "vera.alloc" (func $alloc))' in compiled.wat) is row.needs_alloc


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
    assert all(row.instance in ("", CELL) for row in HOST_IMPORTS)
