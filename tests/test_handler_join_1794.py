"""#1794: an `Exn` handler's value is the join of its body's and its clauses'.

A `throw` clause runs in place of the rest of the handled body, so its value
is a value of the handler, as an `if`'s branch is a value of the `if`.  The
checker typed the handler by its body alone: a clause of another type passed
`vera check` and was read at the body's type (`Some(5)` as a `Result`'s
`Err(5)`), and a body that always throws made the handler `Never`, a type
that fits any context.  Code generation, which takes the handler block's
result from the handler's checked type (#1525), then lost the clause's value.

Each cell names what f1bc772d did with its program.
"""

from __future__ import annotations

import re
from pathlib import Path

from tests import pipeline

_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"

_REPRO_1794 = """\
private fn ok_one(@Unit -> @Result<Int, Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Ok(1)
}

private fn some_of(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn pick(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Result<Int, Int> = handle[Exn<Int>] {
    throw(@Int) -> { some_of(@Int.0) }
  } in {
    if @Bool.0 then { throw(5) } else { ok_one(()) }
  };
  match @Result<Int, Int>.0 {
    Ok(@Int) -> @Int.0,
    Err(@Int) -> 100 + @Int.0
  }
}
"""

_ALWAYS_THROWS = (
    "public fn caught(@Unit -> @Int)\n  requires(true)\n"
    "  ensures(@Int.result == 9)\n  effects(pure)\n{\n"
    "  handle[Exn<Option<Int>>] {\n"
    "    throw(@Option<Int>) -> { option_unwrap_or(@Option<Int>.0, 0) }\n"
    "  } in {\n    throw(Some(9))\n  }\n}\n"
)

_NEVER_AT_STRING = (
    "public fn f(@Int -> @String)\n" + _C + "{\n"
    "  handle[Exn<Int>] {\n    throw(@Int) -> { @Int.0 + 1 }\n"
    "  } in {\n    throw(@Int.0)\n  }\n}\n"
)

_RETHROW = (
    "public fn f(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
    "  effects(<Exn<Int>>)\n{\n"
    "  handle[Exn<Int>] {\n    throw(@Int) -> { throw(@Int.0 + 1) }\n"
    "  } in {\n    if @Int.0 > 0 then { throw(@Int.0) } else { @Int.0 - 1 }\n"
    "  }\n}\n"
)

_WIDER_CLAUSE = (
    "public fn f(@Nat, @Int -> @Nat)\n" + _C + "{\n"
    "  let @Nat = handle[Exn<Int>] {\n    throw(@Int) -> { @Int.0 - 10 }\n"
    "  } in {\n    if @Int.0 > 0 then { throw(@Int.0) } else { @Nat.0 }\n"
    "  };\n  @Nat.0\n}\n"
)

_NARROWER_CLAUSE = (
    "public fn f(@Nat, @Int -> @Int)\n" + _C + "{\n"
    "  handle[Exn<Nat>] {\n    throw(@Nat) -> { @Nat.0 }\n"
    "  } in {\n    if @Int.0 > 0 then { throw(@Nat.0) } else { @Int.0 }\n"
    "  }\n}\n"
)

_STATE_HANDLER = (
    "public fn f(@Int -> @Int)\n" + _C + "{\n"
    "  handle[State<Int>](@Int = @Int.0) {\n"
    "    get(@Unit) -> { resume(@Int.0) },\n"
    "    put(@Int) -> { resume(()) }\n"
    "  } in {\n    put(get(()) + 1);\n    get(())\n  }\n}\n"
)

_REPLACE = re.compile(r"replace '(.+?)' with '(.+?)'")


def _write(tmp_path: Path, source: str) -> Path:
    return pipeline.write_tree(tmp_path, {"main.vera": source})


def _codes(diagnostics: object) -> list[str | None]:
    return [d.error_code for d in diagnostics]  # type: ignore[attr-defined]


def test_repro_1794_a_clause_of_another_type_is_refused_at_the_clause(
        tmp_path: Path) -> None:
    """f1bc772d: check and verify pass, and `pick(true)` prints 105, the
    clause's `Some(5)` read as `Err(5)`."""
    checked = pipeline.check(_write(tmp_path, _REPRO_1794))
    found = [d for d in checked.errors if d.error_code == "E341"]
    assert found, [d.format() for d in checked.diagnostics]
    assert (found[0].location.line, found[0].location.column) == (23, 22)
    assert "Option<Int>" in found[0].description
    assert "Result<Int, Int>" in found[0].description


def test_the_e341_fix_applied_as_written_checks_clean(tmp_path: Path) -> None:
    """The fix is a replacement in the reported program, and the program it
    makes checks with no diagnostic."""
    checked = pipeline.check(_write(tmp_path / "before", _REPRO_1794))
    found = [d for d in checked.errors if d.error_code == "E341"]
    assert found, [d.format() for d in checked.diagnostics]
    match = _REPLACE.search(found[0].fix)
    assert match is not None, found[0].fix
    old, new = match.groups()
    fixed = _REPRO_1794.replace(old, new)
    assert fixed != _REPRO_1794
    after = pipeline.check(_write(tmp_path / "after", fixed))
    assert after.ok and "E341" not in _codes(after.diagnostics), [
        d.format() for d in after.diagnostics]


def test_a_body_that_always_throws_takes_the_clauses_type(
        tmp_path: Path) -> None:
    """`tests/conformance/ch07_exn_composite.vera`'s `caught_composite`.
    f1bc772d typed the handler `Never` and code generation took the block's
    result from the clause; read from the checked type, the block lost it
    until the handler was typed by its clause."""
    path = _write(tmp_path, _ALWAYS_THROWS)
    assert pipeline.verify(path).ok
    ran = pipeline.run(path, "caught", [])
    assert ran.ok and ran.value == 9, (ran.stderr, ran.value)


def test_a_handler_that_always_throws_is_not_every_type(
        tmp_path: Path) -> None:
    """f1bc772d: `vera check` accepts the `Never` handler as a `@String`
    body, and the module `vera run` builds does not load."""
    checked = pipeline.check(_write(tmp_path, _NEVER_AT_STRING))
    assert _codes(checked.errors) == ["E121"], [
        d.format() for d in checked.diagnostics]
    assert "Int" in checked.errors[0].description


def test_a_rethrowing_clause_keeps_the_bodys_type(tmp_path: Path) -> None:
    """A clause that throws is `Never`, so the handler is its body's
    `Int`, at f1bc772d and now."""
    path = _write(tmp_path, _RETHROW)
    assert pipeline.verify(path).ok
    ran = pipeline.run(path, "f", [-3])
    assert ran.ok and ran.value == -4, (ran.stderr, ran.value)


def test_a_wider_clause_makes_the_handler_its_type(tmp_path: Path) -> None:
    """A `Nat` body and an `Int` clause join at `Int`, so the `let @Nat`
    is a narrowing the verifier records and the module checks.  f1bc772d
    typed the handler `Nat`, recorded nothing, and guarded it only by code
    generation's own rule."""
    path = _write(tmp_path, _WIDER_CLAUSE)
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    kinds = {o.kind.value if hasattr(o.kind, "value") else o.kind
             for o in verified.obligations}
    assert "nat_bind" in kinds, sorted(kinds)
    ran = pipeline.run(path, "f", [3, 5])
    assert ran.trap is not None, ran.value
    assert "Negative value bound into a @Nat slot" in str(ran.trap)


def test_a_narrower_clause_joins_at_the_bodys_type(tmp_path: Path) -> None:
    """A `Nat` clause beside an `Int` body: the handler is `Int`, at
    f1bc772d and now."""
    path = _write(tmp_path, _NARROWER_CLAUSE)
    assert pipeline.verify(path).ok
    ran = pipeline.run(path, "f", [3, 5])
    assert ran.ok and ran.value == 3, (ran.stderr, ran.value)


def test_a_state_handler_is_typed_by_its_body(tmp_path: Path) -> None:
    """The negative space: a `State` clause resumes, its body's type is
    `resume`'s `Unit`, and the handler keeps its body's `Int`."""
    path = _write(tmp_path, _STATE_HANDLER)
    verified = pipeline.verify(path)
    assert verified.ok and "E341" not in _codes(verified.diagnostics)
    ran = pipeline.run(path, "f", [4])
    assert ran.ok and ran.value == 5, (ran.stderr, ran.value)
