"""Tests for the ``apply_fn`` checker special form (#854).

Before #854, ``apply_fn`` — the documented primitive for applying a
function *value* (SKILL.md "Stored function values and `apply_fn`",
spec §11.10.5) — was unknown to the checker: every use fell into the
unresolved-bare-call path in ``vera/checker/calls.py``, which

1. emitted a spurious ``[E200] Unresolved function 'apply_fn'`` warning
   on green programs (``vera check examples/closures.vera`` showed it),
   and
2. typed the call as ``UnknownType()``, so wrong arity, wrong argument
   types, a non-function first argument, and an effectful applied row
   inside a pure caller all passed ``vera check`` with exit 0 and only
   surfaced (or silently mis-ran) at compile time.

These tests pin the special form: ``apply_fn(f, a0, ..., an)`` is typed
structurally against ``f``'s ``FunctionType`` — arity (E201), argument
types (E202), non-function first argument (E202), the applied effect
row joining the caller's used effects (E122) and being checked against
the caller's declared row (E125), and the call's result being ``f``'s
return type.

Effect-soundness probe result on main (2026-07-02, empirical):

* ``type F = fn(Int -> Int) effects(<IO>);`` parses AND checks — fn
  types carry effect rows, and an ``effects(<IO>)`` fn-typed *parameter*
  is constructible/passable today.
* Applying such a parameter with ``apply_fn`` inside an
  ``effects(pure)`` function passed ``vera check`` (exit 0, only the
  E200 warning) — a real, reachable soundness hole, pinned RED by
  ``TestApplyFnEffects.test_effectful_row_in_pure_caller``.
* The *construction* route was already blocked: an AnonFn whose body
  performs ``IO.print`` inside a pure function trips E122 on the
  enclosing declaration (the checker attributes effect ops in closure
  bodies to the enclosing function), so only the pass-as-parameter
  route was open.

User-defined ``fn apply_fn`` probe result on main (empirical): the
redefinition checked green (apply_fn is not a registry built-in, so
E151 did not fire), but codegen unconditionally hijacks the name — any
call with >= 2 arguments is translated as ``call_indirect``, so
``apply_fn(1, 2)`` against a user ``fn apply_fn(@Int, @Int -> @Int)``
failed closure-type inference and the calling function was silently
skipped from the compiled module (``vera run`` reported "No exported
functions to call").  That is exactly the #815 one-canonical-form
desync E151 exists for, so the fix adds ``apply_fn`` to the E151
reject set: redefinition is now a check-time error, pinned by
``TestApplyFnRedefinition``.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

from vera.codegen import compile as vera_compile, execute
from vera.parser import parse_file, parse_to_ast
from vera.transform import transform

from tests.checker_helpers import (
    EXAMPLES_DIR,
    _check_clean,
    _check_err,
    _check_ok,
    _errors,
)

# ---------------------------------------------------------------------
# Shared program scaffolding
# ---------------------------------------------------------------------

_ADDER = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn make_adder(@Int -> @IntToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}
"""

_MINIMAL_OK = _ADDER + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make_adder(10);
  apply_fn(@IntToInt.0, 5)
}
"""


def _compile_and_run(source: str, fn: str) -> int:
    """Compile a Vera source string to WASM and execute *fn*.

    Mirrors the ``tests/test_wasm_coverage.py`` helper (Windows-safe:
    ``delete=False`` + manual unlink)."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        path = f.name
    try:
        tree = parse_file(path)
        prog = transform(tree)
        result = vera_compile(prog, source=source, file=path)
        assert result.wasm_bytes is not None, \
            f"Compile failed: {result.errors}"
        exec_result = execute(result, fn_name=fn, args=[])
        assert exec_result.value is not None
        return int(exec_result.value)
    finally:
        Path(path).unlink()


# =====================================================================
# 1. Zero-warning pin — valid apply_fn programs are diagnostic-free
# =====================================================================

class TestApplyFnClean:
    """Valid apply_fn uses produce NO diagnostics (no E200 warning)."""

    def test_minimal_apply_fn_no_diagnostics(self) -> None:
        """A minimal valid apply_fn program checks with zero
        diagnostics and zero warnings (API level)."""
        _check_clean(_MINIMAL_OK)

    def test_cli_check_json_zero_warnings(self, tmp_path) -> None:
        """`vera check --json` on a valid apply_fn program: ok, no
        diagnostics, no warnings."""
        vera_file = tmp_path / "apply_fn_ok.vera"
        vera_file.write_text(_MINIMAL_OK, encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, "-m", "vera.cli", "check", "--json",
             str(vera_file)],
            capture_output=True, text=True, encoding="utf-8",
        )
        assert proc.returncode == 0, proc.stderr
        payload = json.loads(proc.stdout)
        assert payload["ok"] is True
        assert payload["diagnostics"] == []
        assert payload["warnings"] == []

    def test_closures_example_no_e200(self) -> None:
        """examples/closures.vera checks with zero diagnostics —
        before #854 its apply_fn call drew a spurious E200 warning."""
        source = (EXAMPLES_DIR / "closures.vera").read_text(
            encoding="utf-8")
        prog = parse_to_ast(source, file="closures.vera")
        from vera.checker import typecheck
        diags = typecheck(prog, source=source, file="closures.vera")
        e200s = [d for d in diags if d.error_code == "E200"]
        assert e200s == [], \
            f"closures.vera should be E200-free: " \
            f"{[d.description for d in e200s]}"
        assert diags == [], \
            f"closures.vera should be diagnostic-free: " \
            f"{[d.description for d in diags]}"

    def test_generic_typevar_params_clean(self) -> None:
        """apply_fn on a TypeVar-parameterised fn-type alias (the
        prelude combinator shape) checks cleanly."""
        _check_clean("""
type Mapper<A, B> = fn(A -> B) effects(pure);

private forall<A, B> fn my_map(@Mapper<A, B>, @A -> @B)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@Mapper<A, B>.0, @A.0)
}
""")

    def test_return_type_flows_to_context(self) -> None:
        """apply_fn's result is the applied fn's return type, not
        UnknownType — a body returning Int against a declared @String
        return is now an E121 error (it was silently green)."""
        errs = _check_err(_ADDER + """
public fn bad(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make_adder(1);
  apply_fn(@IntToInt.0, 5)
}
""", "body has type")
        assert any(e.error_code == "E121" for e in errs)


# =====================================================================
# 2/7. Arity — too few, too many, zero, multi-parameter shapes
# =====================================================================

class TestApplyFnArity:
    """Wrong arity is a check-time ERROR, not a warning."""

    def test_too_few_args(self) -> None:
        errs = _check_err(_ADDER + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make_adder(10);
  apply_fn(@IntToInt.0)
}
""", "expects 1 argument(s), got 0")
        assert any(e.error_code == "E201" for e in errs)

    def test_too_many_args(self) -> None:
        errs = _check_err(_ADDER + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make_adder(10);
  apply_fn(@IntToInt.0, 1, 2)
}
""", "expects 1 argument(s), got 2")
        assert any(e.error_code == "E201" for e in errs)

    def test_zero_args(self) -> None:
        """apply_fn with no arguments at all lacks its function value."""
        errs = _check_err("""
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn()
}
""", "apply_fn")
        assert any(e.error_code == "E201" for e in errs)

    def test_two_param_fn_two_args_clean(self) -> None:
        """Variadic shape: a two-parameter fn type applied to two
        arguments types correctly (result Int feeds the return)."""
        _check_clean("""
type BinOp = fn(Int, Int -> Int) effects(pure);

public fn use_binop(@BinOp, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@BinOp.0, @Int.0, 2)
}
""")

    def test_two_param_fn_one_arg_error(self) -> None:
        errs = _check_err("""
type BinOp = fn(Int, Int -> Int) effects(pure);

public fn use_binop(@BinOp, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@BinOp.0, @Int.0)
}
""", "expects 2 argument(s), got 1")
        assert any(e.error_code == "E201" for e in errs)


# =====================================================================
# 3/4. Argument types — wrong arg type, non-function first argument
# =====================================================================

class TestApplyFnArgTypes:

    def test_wrong_arg_type(self) -> None:
        """Passing a String where the applied fn expects Int errors."""
        errs = _check_err(_ADDER + """
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make_adder(10);
  apply_fn(@IntToInt.0, "hello")
}
""", "has type String, expected Int")
        assert any(e.error_code == "E202" for e in errs)

    def test_non_function_first_arg(self) -> None:
        """apply_fn's first argument must be function-typed."""
        errs = _check_err("""
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(42, 1)
}
""", "expected a function value")
        assert any(e.error_code == "E202" for e in errs)


# =====================================================================
# 5. Effect soundness — the applied row joins the caller's effects
# =====================================================================

class TestApplyFnEffects:
    """The applied fn's effect row participates in effect checking.

    Empirical result on main (see module docstring): an effects(<IO>)
    fn-typed parameter applied inside an effects(pure) function passed
    `vera check` — this class pins the fix (E125 at the call site, and
    the row joining `_effect_ops_used` so the pure declaration trips
    E122, exactly as a named-function call would)."""

    _EFF_SRC = """
type IntToIntIO = fn(Int -> Int) effects(<IO>);

public fn pure_caller(@IntToIntIO, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(@IntToIntIO.0, @Int.0)
}
"""

    def test_effectful_row_in_pure_caller(self) -> None:
        """Applying an effects(<IO>) fn value in a pure function is a
        check-time error."""
        errs = _errors(self._EFF_SRC)
        codes = {e.error_code for e in errs}
        assert "E125" in codes, \
            f"Expected E125 call-site effect error, got: " \
            f"{[(e.error_code, e.description) for e in errs]}"
        assert "E122" in codes, \
            f"Expected E122 (applied row joins used effects), got: " \
            f"{[(e.error_code, e.description) for e in errs]}"

    def test_effectful_row_in_matching_caller_ok(self) -> None:
        """The same application is clean when the caller declares the
        effect."""
        _check_clean("""
type IntToIntIO = fn(Int -> Int) effects(<IO>);

public fn io_caller(@IntToIntIO, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  apply_fn(@IntToIntIO.0, @Int.0)
}
""")


# =====================================================================
# 6. Prelude regression — combinators still check and compile
# =====================================================================

class TestPreludeRegression:
    """option_map / option_and_then / result_map keep working."""

    _PRELUDE_SRC = """\
type IntToInt = fn(Int -> Int) effects(pure);

private fn make_adder(@Int -> @IntToInt)
  requires(true)
  ensures(true)
  effects(pure)
{
  fn(@Int -> @Int) effects(pure) { @Int.0 + @Int.1 }
}

public fn combinators(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @IntToInt = make_adder(100);
  let @Option<Int> = option_map(Some(5), @IntToInt.0);
  let @Option<Int> = option_and_then(
    @Option<Int>.0,
    fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0 + 1) });
  let @Result<Int, String> = result_map(Ok(7), @IntToInt.0);
  match @Option<Int>.0 {
    None -> 0,
    Some(@Int) -> @Int.0
  }
}
"""

    def test_prelude_combinators_check(self) -> None:
        _check_ok(self._PRELUDE_SRC)

    def test_prelude_combinators_compile_and_run(self) -> None:
        assert _compile_and_run(self._PRELUDE_SRC, "combinators") == 106


# =====================================================================
# 8. User-defined apply_fn — one canonical form (E151)
# =====================================================================

class TestApplyFnRedefinition:
    """Redefining apply_fn is a check-time E151 error (see module
    docstring for the main-behaviour probe and the decision)."""

    def test_user_redefinition_rejected(self) -> None:
        errs = _check_err("""
private fn apply_fn(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + @Int.1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(1, 2)
}
""", "redefines a built-in")
        assert any(e.error_code == "E151" for e in errs)

    def test_where_helper_redefinition_rejected(self) -> None:
        """A where-helper named apply_fn is rejected too (#815 covers
        nested helpers)."""
        errs = _errors("""
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(1, 2)
}
where {
  fn apply_fn(@Int, @Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    @Int.0 + @Int.1
  }
}
""")
        assert any(e.error_code == "E151" for e in errs)
