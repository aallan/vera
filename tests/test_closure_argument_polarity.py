"""The polarity rule: a type variable inside a function-typed argument is
fixed by that argument's declared type, by the position's polarity (spec
§4.2; #1525).

A closure handed to a generic is a value of a function type, and a type
variable can sit at either side of it.  At a positive position (the
closure's return, a parameter of one of its parameters) the generic receives
the closure's values, so a closure declared to return `@Int` there makes the
variable `Int`: an `Int` result is never read as a `@Nat`.  At a negative
position (a parameter) the generic hands the closure values, so a closure
declared to take a `@Nat` there makes the variable `Nat`: an `Int` value
argument at the variable is then a narrowing, recorded and guarded where it
enters.  A variable a closure fixes both ways has no instance, and the call
is refused at that closure argument with `E202`.

Before the rule the first argument fixed the variable and the closure was
admitted at the other type, so `apply2(@Nat.0, fn(@Int -> @Int) { @Int.0 -
100 })` was a `@Nat` holding -95, and `apply2(@Int.0, fn(@Nat -> @Nat) {
@Nat.0 })` handed -7 to the closure's `@Nat` parameter, with check and
verify clean.

The matrix is every combination of the carrier (`array_fold`, a user
generic, a constructor read back by a generic), the value argument's type,
the closure's return and parameter type at the variable, and the position
the call's value is used at (a `let @Nat`, a `@Nat` argument, a `-> @Nat`
result).  Each cell is its own test, unparametrised, so the mutation lane
never samples one out; each asserts the call's checked type, the
`nat_bind` obligations the verifier records, the guards the module holds,
and the run, which never returns a negative `@Nat`.
"""

from __future__ import annotations

import re
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=["vera/checker/resolution.py"])

_HELPERS = {
    "fold": "",
    "generic": (
        "type Endo<T> = fn(T -> T) effects(pure);\n\n"
        "private forall<T> fn apply2(@T, @Endo<T> -> @T)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  apply_fn(@Endo<T>.0, @T.0)\n}\n\n"
    ),
    "constructor": (
        "type Endo<T> = fn(T -> T) effects(pure);\n\n"
        "private data Fold<T> {\n  MkFold(T, Endo<T>)\n}\n\n"
        "private forall<T> fn run(@Fold<T> -> @T)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n"
        "{\n  match @Fold<T>.0 {\n"
        "    MkFold(@T, @Endo<T>) -> apply_fn(@Endo<T>.0, @T.0)\n  }\n}\n\n"
    ),
}

_NEED = (
    "private fn need(@Nat -> @Nat)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{\n  @Nat.0\n}\n\n"
)


@dataclass(frozen=True)
class Cell:
    """One program of the matrix and the outcome the rule gives it."""

    carrier: str
    value: str
    """The value argument's type: ``Nat`` (``@Nat.0``) or ``Int`` (``@Int.0``)."""
    returns: str
    """The closure's declared type at the variable's positive position."""
    takes: str
    """The closure's declared type at the variable's negative position."""
    use: str
    """``let``, ``argument`` or ``result``: where the call's value goes."""

    @property
    def name(self) -> str:
        return (f"{self.carrier}_value_{self.value.lower()}_returns_"
                f"{self.returns.lower()}_takes_{self.takes.lower()}_"
                f"{self.use}")

    # -- the rule ---------------------------------------------------------

    @property
    def refused(self) -> bool:
        """A closure that returns `Int` and takes `Nat` at one variable."""
        return self.returns == "Int" and self.takes == "Nat"

    @property
    def instance(self) -> str:
        """The type the call instantiates its variable at."""
        if self.returns == "Int":
            return "Int"
        if self.takes == "Nat":
            return "Nat"
        return self.value

    @property
    def narrows_value(self) -> bool:
        """The `Int` value argument enters the variable at `Nat`."""
        return self.instance == "Nat" and self.value == "Int"

    @property
    def narrows_use(self) -> bool:
        """The call's `Int` value is bound into the `@Nat` use."""
        return self.instance == "Int"

    # -- the program ------------------------------------------------------

    def closure(self) -> str:
        """The closure argument, its body reading the variable's parameter."""
        if self.carrier == "fold":
            params = f"@{self.takes}, @Int"
            acc = "@Int.1" if self.takes == "Int" else "@Nat.0"
        else:
            params = f"@{self.takes}"
            acc = f"@{self.takes}.0"
        if self.returns == "Int":
            body = f"{acc} - 100"
        elif self.takes == "Int":
            body = f"abs({acc})"
        else:
            body = acc
        return f"fn({params} -> @{self.returns}) effects(pure) {{ {body} }}"

    def call(self) -> str:
        value = f"@{self.value}.0"
        if self.carrier == "fold":
            return f"array_fold(@Array<Int>.0, {value}, {self.closure()})"
        if self.carrier == "generic":
            return f"apply2({value}, {self.closure()})"
        return f"run(MkFold({value}, {self.closure()}))"

    def source(self) -> str:
        lets = "let @Array<Int> = [3, 4];\n  " if self.carrier == "fold" else ""
        if self.use == "let":
            body = f"{lets}let @Nat = {self.call()};\n  @Nat.0"
        elif self.use == "argument":
            body = f"{lets}need({self.call()})"
        else:
            body = f"{lets}{self.call()}"
        return (
            _HELPERS[self.carrier] + _NEED
            + "public fn cell(@Nat, @Int -> @Nat)\n"
            + "  requires(@Nat.0 <= 10)\n  ensures(true)\n  effects(pure)\n"
            + "{\n  " + body + "\n}\n"
        )

    def call_line(self) -> int:
        """The line holding the carrier's call."""
        lines = self.source().splitlines()
        return next(n for n, line in enumerate(lines, 1)
                    if self.call() in line)


_CELLS = tuple(
    Cell(carrier, value, returns, takes, use)
    for carrier in ("fold", "generic", "constructor")
    for value in ("Nat", "Int")
    for returns in ("Int", "Nat")
    for takes in ("Nat", "Int")
    for use in ("let", "argument", "result")
)

#: The run's arguments: `@Nat.0` = 5, `@Int.0` = -7.
_ARGS = [5, -7]

_NAT_TRAP = "Negative value bound into a @Nat slot"

_CARRIER_CALL = {"fold": "array_fold", "generic": "apply2",
                 "constructor": "run"}


def _call_type(checked: pipeline.Checked, cell: Cell) -> str | None:
    """The checked type of the carrier's call in `cell`, the variable's
    instance, read off the typed program."""
    from vera import ast
    from vera.types import pretty_type

    name = _CARRIER_CALL[cell.carrier]
    typed = checked.typed
    found: list[str] = []

    def walk(node: object) -> None:
        if isinstance(node, ast.FnCall) and node.name == name:
            ty = typed.semantic.get(node.node_id) if node.node_id else None
            found.append(pretty_type(ty) if ty is not None else "?")
        for field in getattr(node, "__dataclass_fields__", {}):
            child = getattr(node, field)
            if isinstance(child, ast.Node):
                walk(child)
            elif isinstance(child, tuple):
                for item in child:
                    if isinstance(item, ast.Node):
                        walk(item)

    for tld in checked.program.declarations:
        if getattr(tld.decl, "name", None) == "cell":
            walk(tld.decl)
    assert len(found) == 1, found
    return found[0].lstrip("@")


def _observe(cell: Cell, tmp_path: Path) -> None:
    path = tmp_path / "cell.vera"
    path.write_text(cell.source(), encoding="utf-8")
    if cell.refused:
        checked = pipeline.check(path)
        found = [d for d in checked.errors if d.error_code == "E202"]
        assert found, [d.format() for d in checked.diagnostics]
        text = found[0].description
        assert "`Int`" in text and "`Nat`" in text, text
        assert "return" in text and "parameter" in text, text
        assert found[0].location.line == cell.call_line(), found[0].format()
        return
    verified = pipeline.verify(path, reconcile=True)
    errors = {d.error_code for d in verified.diagnostics
              if d.severity == "error"}
    # An `Int` value entering the variable at `Nat` is a narrowing; the
    # parameter's negative values refute it (E503), as they refute
    # `pick(@Nat.0, @Int.0)`, and the module guards it all the same.
    assert errors == ({"E503"} if cell.narrows_value else set()), [
        d.format() for d in verified.diagnostics]
    assert _call_type(verified.checked, cell) == cell.instance
    expected = int(cell.narrows_value) + int(cell.narrows_use)
    records = [o for o in verified.result.obligations
               if o.kind == "nat_bind" and o.status != "verified"]
    assert len(records) == expected, (records, cell)
    compiled = pipeline.compile(path).result
    guards = [c for c in compiled.emitted_checks
              if c.emitter == "wasm/operators.py:_emit_nat_bind_guard"]
    assert len(guards) == expected, (guards, cell)
    # The record and the module hold the same sites (the join's own
    # reading of a site: a result narrowing is recorded at the body and
    # guarded at its tail).
    report = verified.reconciled.report() if verified.reconciled else {}
    assert not report.get("mismatches"), report
    ran = pipeline.run(compiled, "cell", _ARGS, capture_stderr=False)
    if cell.narrows_value or (cell.narrows_use and cell.returns == "Int"):
        assert _traps(ran), ran.value
    else:
        assert ran.ok, ran.trap
        assert isinstance(ran.value, int) and ran.value >= 0, ran.value


def _traps(ran: pipeline.Ran) -> bool:
    """*ran* stopped at a `@Nat` guard."""
    return ran.trap is not None and _NAT_TRAP in str(ran.trap)


def _cell_test(cell: Cell) -> Callable[[Path], None]:
    def test(tmp_path: Path) -> None:
        _observe(cell, tmp_path)
    test.__name__ = f"test_{cell.name}"
    test.__doc__ = f"{cell.call()} at a {cell.use} `@Nat`."
    return test


def _declared_name_guard(cell: Cell) -> bool:
    """A fold at `Nat` bound into a `@Nat` `let` or argument: code
    generation's declared-name rule reads the fold as `Int` and guards the
    binding, which the verifier, reading the checked `Nat`, does not record
    (#1695's (a) member; A2a's step 4 removes the rule)."""
    return (cell.carrier == "fold" and cell.instance == "Nat"
            and cell.use in ("let", "argument"))


for _cell in _CELLS:
    _test = _cell_test(_cell)
    if _declared_name_guard(_cell):
        _test = pytest.mark.xfail(strict=True, reason=(
            "#1695 (a): code generation guards a Nat-typed fold by its "
            "declared-name rule, with no record"))(_test)
    globals()[f"test_{_cell.name}"] = _test
del _cell, _test


def test_the_matrix_spans_every_combination() -> None:
    """72 cells: 3 carriers, 2 value types, 2 return types, 2 parameter
    types, 3 uses; 18 refused, and every instance the rule gives present."""
    assert len(_CELLS) == len({c.name for c in _CELLS}) == 72
    assert sum(c.refused for c in _CELLS) == 18
    assert {c.instance for c in _CELLS if not c.refused} == {"Int", "Nat"}


# ---------------------------------------------------------------------
# The two finds (W55, 23 October), as reported
# ---------------------------------------------------------------------

_ENDO = (
    "type Endo<T> = fn(T -> T) effects(pure);\n\n"
    "private forall<T> fn apply2(@T, @Endo<T> -> @T)\n"
    "  requires(true)\n  ensures(true)\n  effects(pure)\n"
    "{\n  apply_fn(@Endo<T>.0, @T.0)\n}\n\n"
)

_INT_RETURN_AT_NAT = _ENDO + (
    "public fn f(@Nat -> @Nat)\n  requires(@Nat.0 <= 10)\n  ensures(true)\n"
    "  effects(pure)\n{\n"
    "  let @Nat = apply2(@Nat.0, fn(@Int -> @Int) effects(pure) "
    "{ @Int.0 - 100 });\n  @Nat.0\n}\n\n"
    "public fn g(@Nat -> @Nat)\n  requires(@Nat.0 <= 10)\n  ensures(true)\n"
    "  effects(pure)\n{\n"
    "  apply2(@Nat.0, fn(@Int -> @Int) effects(pure) { @Int.0 - 100 })\n}\n"
)

_NAT_PARAM_AT_INT = _ENDO + (
    "public fn h(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{\n"
    "  apply2(@Int.0, fn(@Nat -> @Nat) effects(pure) { @Nat.0 })\n}\n\n"
    "public fn k(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(pure)\n{\n  let @Array<Int> = [1, 2];\n"
    "  array_fold(@Array<Int>.0, @Int.0, fn(@Nat, @Int -> @Nat) "
    "effects(pure) { @Nat.0 })\n}\n"
)


def _line_of(source: str, text: str) -> int:
    return next(n for n, line in enumerate(source.splitlines(), 1)
                if text in line)


def _int_return_traps(fn: str, tmp_path: Path) -> None:
    path = tmp_path / "f.vera"
    path.write_text(_INT_RETURN_AT_NAT, encoding="utf-8")
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    assert _traps(pipeline.run(path, fn, [5]))


def test_repro_a_closure_int_return_never_reaches_a_nat_let(
        tmp_path: Path) -> None:
    """finds/a2_closure_int_return_at_nat_formal.vera's `f`: -95 at a
    `let @Nat` at f1bc772d; the variable is `Int`, and the `let` traps."""
    _int_return_traps("f", tmp_path)


def test_repro_a_closure_int_return_never_reaches_a_nat_result(
        tmp_path: Path) -> None:
    """The same find's `g`: -95 at a `-> @Nat` return at f1bc772d."""
    _int_return_traps("g", tmp_path)


def _nat_parameter_traps(fn: str, call: str, tmp_path: Path) -> None:
    path = tmp_path / "h.vera"
    path.write_text(_NAT_PARAM_AT_INT, encoding="utf-8")
    verified = pipeline.verify(path)
    # The `@Int` argument now enters `T` at `Nat`: a narrowing, refuted
    # for the parameter's negative values as `pick(@Nat.0, @Int.0)` is.
    refused = {(d.error_code, d.location.line) for d in verified.errors}
    assert ("E503", _line_of(_NAT_PARAM_AT_INT, call)) in refused, refused
    assert {code for code, _ in refused} == {"E503"}, refused
    assert _traps(pipeline.run(path, fn, [-7]))
    ok = pipeline.run(path, fn, [7])
    assert ok.ok and ok.value == 7, (ok.value, ok.trap)


def test_repro_a_closure_nat_parameter_never_takes_an_int(
        tmp_path: Path) -> None:
    """finds/a2_closure_nat_param_at_int_variable.vera's `h`: -7 in a
    closure's `@Nat` parameter at f1bc772d; the variable is `Nat`, and the
    `Int` value traps where it enters."""
    _nat_parameter_traps("h", "apply2(@Int.0,", tmp_path)


def test_repro_a_fold_closure_nat_parameter_never_takes_an_int(
        tmp_path: Path) -> None:
    """The same find's `k`: `array_fold`'s accumulator, -7 at f1bc772d."""
    _nat_parameter_traps("k", "array_fold(@Array<Int>.0, @Int.0,", tmp_path)


# ---------------------------------------------------------------------
# The refusal's fix, applied as written
# ---------------------------------------------------------------------

_REPLACE = re.compile(r"replace '([^']+)' with '([^']+)'")


def _fix_applies(carrier: str, tmp_path: Path) -> None:
    """The refusal's fix is a replacement in the reported program, and the
    program it makes checks with no `E202`."""
    cell = Cell(carrier, "Nat", "Int", "Nat", "let")
    source = cell.source()
    before = tmp_path / "before.vera"
    before.write_text(source, encoding="utf-8")
    found = [d for d in pipeline.check(before).errors
             if d.error_code == "E202"]
    assert found, source
    match = _REPLACE.search(found[0].fix)
    assert match is not None, found[0].fix
    old, new = match.groups()
    assert source.count(old) == 1, (old, source)
    after = tmp_path / "after.vera"
    after.write_text(source.replace(old, new), encoding="utf-8")
    checked = pipeline.check(after)
    assert checked.ok and not [d for d in checked.diagnostics
                               if d.error_code == "E202"], [
        d.format() for d in checked.diagnostics]


def test_the_e202_fix_applied_as_written_checks_clean_fold(
        tmp_path: Path) -> None:
    _fix_applies("fold", tmp_path)


def test_the_e202_fix_applied_as_written_checks_clean_generic(
        tmp_path: Path) -> None:
    _fix_applies("generic", tmp_path)


def test_the_e202_fix_applied_as_written_checks_clean_constructor(
        tmp_path: Path) -> None:
    _fix_applies("constructor", tmp_path)


# ---------------------------------------------------------------------
# The nearest accepted neighbours of the refusal
# ---------------------------------------------------------------------

def test_a_closure_at_one_type_per_variable_is_accepted(
        tmp_path: Path) -> None:
    """A closure whose positions agree, or whose `Nat` return and `Int`
    parameter fix nothing, is accepted with no diagnostic and runs: the
    refusal is the two pins on one variable, never a closure over `Int`
    and `Nat` as such."""
    for n, closure in enumerate((
            "fn(@Int -> @Int) effects(pure) { @Int.0 }",
            "fn(@Nat -> @Nat) effects(pure) { @Nat.0 }",
            "fn(@Int -> @Nat) effects(pure) { abs(@Int.0) }")):
        path = tmp_path / f"n{n}.vera"
        path.write_text(_ENDO + (
            "public fn f(@Nat -> @Int)\n  requires(true)\n  ensures(true)\n"
            f"  effects(pure)\n{{\n  apply2(@Nat.0, {closure})\n}}\n"),
            encoding="utf-8")
        verified = pipeline.verify(path)
        assert verified.ok and not verified.checked.diagnostics, [
            d.format() for d in verified.diagnostics]
        ran = pipeline.run(path, "f", [5])
        assert ran.ok and ran.value == 5, (closure, ran.value, ran.trap)
