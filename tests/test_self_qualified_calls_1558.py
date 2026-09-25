"""#1558 — a module's qualified call to its own function.

Inside a file that declares `module ma;`, `ma::two(3)` names the file's own
top-level `two`.  It checked with an E230 *warning* ("Module 'ma' not
found") on `main` and ran, because code generation compiled the call; #1513
made E230 an error and the program stopped checking.  The checker had never
resolved the path: a module-qualified call looked the path up among the
modules the file imports, and a file does not import itself.

The rule (spec §8.5.3): the path a file declares with `module P;` names the
file itself, so `P::f(...)` calls its own top-level `f` — public or private,
since the call is inside the module (§8.4.1) — and a `where` helper named
`f` does not shadow it, as no local name shadows a module-qualified call.
The path is the file's own only when the program reaches the file by it: an
imported module's declared path must be the path it is imported by, and the
entry's must not be the path of a module it resolves.  Every other path
still has to be a module the file imports (E230), as #1513 made it.

The instrument:

- **The position matrix** (`TestThePositionMatrix`): the call in every
  position a call takes — a body, a `let`, an `if` condition, a `match` arm,
  `requires`, `ensures`, a nested call, a generic call's argument, a pipe, an
  interpolation, a closure, a `where` helper, a handler, an `assert` — and to
  every kind of callee: a private function, a generic, a recursive call, a
  callee with a precondition, one whose result and precondition read the
  order of two `@Int` arguments, and a callee a `where` helper of the same
  name shadows.
  Each is placed in a module the entry imports, in one it reaches only
  transitively, and in the file checked as the entry, under a one-segment
  and a dotted path.  Every cell checks clean and prints the value its
  bare-call control prints (12), except the shadowed callee, whose control
  reaches the helper (600) where the qualified call reaches `two` (12).
- **The verifier** (`TestTheVerifierReadsTheOwnPath`): a qualified call is
  verified as its bare control is, in every position: the same errors, the
  same warnings and the same tier counts.  The call's precondition is an
  obligation (E501 where the control's is), read with the arguments in the
  order they are written, a contract that calls a private
  function by its qualified name is read in that module's scope, and a
  recursive call spelled with the path counts for `decreases`.
- **The clones** (`TestBothSidesNameTheSameClones`): a generic called by its
  qualified name from a module body is discovered by the verifier as the
  clone code generation emits — the #732 differential.
- **The path alone** (`TestOnlyTheOwnPath`): a path that is not the file's
  own and not an import is still E230; an unknown function under the own
  path is E233; a file without a `module` declaration, or one whose
  declaration is not the path it is imported by, has no own path.
- **The call graph** (`TestTheCallGraphReadsTheOwnPath`,
  `TestAFalsePostconditionIsNeverProved`,
  `TestThePathNamesTheTopLevelFunction`): #1524's graph draws a call by the
  own path as an edge to the top-level function it names.  Direct, mutual
  (bare and qualified mixed), parent-helper, closure and handler-clause
  cycles through the path need a measure (E137), and with one verify and
  run as their bare spelling does; a contract calling back through the path
  is E138; `ensures(false)` reached through the path is never Tier 1 and
  never returns under `vera run`; and a helper of the same name never takes
  the edge, in the graph or in a generic clone's by-name group.
"""

from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
from typing import Any, Callable, NamedTuple

import pytest

# ---------------------------------------------------------------------------
# Program builders
# ---------------------------------------------------------------------------


def _fn(sig: str, body: str, *, vis: str = "public", req: str = "true",
        ens: str = "true", dec: str | None = None, where: str = "") -> str:
    decreases = f"  decreases({dec})\n" if dec else ""
    tail = f"\nwhere {{\n{where}\n}}" if where else ""
    return (f"{vis} fn {sig}\n  requires({req})\n  ensures({ens})\n"
            f"{decreases}  effects(pure)\n{{\n  {body}\n}}{tail}\n")


def _helper(sig: str, body: str) -> str:
    return (f"  fn {sig}\n    requires(true)\n    ensures(true)\n"
            f"    effects(pure)\n  {{\n    {body}\n  }}")


def _callees(rec: str) -> str:
    """The functions `four` calls; *rec* prefixes `fact`'s recursive call."""
    return "\n".join((
        _fn("two(@Int -> @Int)", "@Int.0 * 2", ens="@Int.result == @Int.0 * 2"),
        _fn("ptwo(@Int -> @Int)", "@Int.0 * 2", vis="private",
            ens="@Int.result == @Int.0 * 2"),
        "public forall<T> fn gid(@T -> @T)\n  requires(true)\n  ensures(true)\n"
        "  effects(pure)\n{\n  @T.0\n}\n",
        _fn("fact(@Nat -> @Nat)",
            f"if @Nat.0 == 0 then {{\n    1\n  }} else {{\n"
            f"    @Nat.0 * {rec}fact(@Nat.0 - 1)\n  }}",
            ens="@Nat.result >= 1", dec="@Nat.0"),
        _fn("pos(@Int -> @Int)", "@Int.0", req="@Int.0 > 0"),
        _fn("three(@Int -> @Nat)", "3", ens="@Nat.result == 3"),
        _fn("pthree(@Int -> @Nat)", "3", vis="private",
            ens="@Nat.result == 3"),
        _fn("nid(@Nat -> @Int)", "nat_to_int(@Nat.0)"),
        # Two `@Int` parameters, whose order the result and the precondition
        # both read: `@Int.1` is the first argument, `@Int.0` the second.
        _fn("sub(@Int, @Int -> @Int)", "@Int.1 - @Int.0",
            req="@Int.1 > @Int.0", ens="@Int.result == @Int.1 - @Int.0"),
    ))


class Position(NamedTuple):
    body: str
    req: str = "true"
    ens: str = "true"
    where: str = ""
    recursive: bool = False


def _positions(q: str) -> dict[str, Position]:
    """`four`'s body per position, calling through the prefix *q* (`ma::` or
    `` for the bare control).  `four(3)` is 12 in every control but one."""
    return {
        "body": Position(f"{q}two(@Int.0) * 2"),
        "let": Position(f"let @Int = {q}two(@Int.0);\n  @Int.0 * 2"),
        "if_cond": Position(
            f"if {q}two(@Int.0) > 0 then {{\n    12\n  }} else {{\n    0\n  }}"),
        "match_arm": Position(
            f"match Some(@Int.0) {{\n    Some(@Int) -> {q}two(@Int.0) * 2,\n"
            f"    None -> 0\n  }}"),
        "requires": Position("@Int.0 * 4", req=f"{q}two(@Int.0) == @Int.0 * 2"),
        "ensures": Position("@Int.0 * 4",
                            ens=f"@Int.result == {q}two(@Int.0) * 2"),
        "nested": Position(f"{q}two({q}two(@Int.0))"),
        "pipe": Position(f"(@Int.0 |> {q}two()) * 2"),
        "interp": Position(
            f'string_length("\\({q}two(@Int.0))xxxxxxxxxxx")'),
        "closure": Position(
            f"array_fold(array_map([@Int.0], fn(@Int -> @Int) effects(pure) "
            f"{{ {q}two(@Int.0) }}), 0, fn(@Int, @Int -> @Int) effects(pure) "
            f"{{ @Int.1 + @Int.0 }}) * 2"),
        "where_helper": Position(
            "helper(@Int.0)",
            where=_helper("helper(@Int -> @Int)", f"{q}two(@Int.0) * 2")),
        "handler": Position(
            "handle[State<Int>](@Int = 0) {\n    get(@Unit) -> { resume(@Int.0) },"
            "\n    put(@Int) -> { resume(()) }\n  } in {\n"
            f"    put({q}two(3));\n    get(()) * 2\n  }}"),
        "assert": Position(f"assert({q}two(@Int.0) == @Int.0 * 2);\n  @Int.0 * 4"),
        "private": Position(f"{q}ptwo(@Int.0) * 2"),
        "generic": Position(f"{q}gid(@Int.0) * 4"),
        # The argument of a generic's call: its instantiation is named from
        # the argument's type, which a call by the path has to supply.
        "generic_argument": Position(f"{q}gid({q}two(@Int.0)) * 2"),
        "recursion": Position("nat_to_int(fact(3)) * 2", recursive=True),
        "precondition": Position(f"{q}pos(@Int.0) * 4"),
        # A `@Nat` result: the subtraction is `@Nat`'s, with its underflow
        # obligation, only when the callee's return type is read.
        "nat_result": Position(
            f"nat_to_int({q}three(@Int.0) - {q}three(@Int.0)) + 12"),
        # A `@Nat` parameter given an `@Int`: the narrowing is obligated at
        # the call only when the callee's parameters are read (E503 here,
        # since nothing keeps `@Int.0` non-negative).
        "nat_param": Position(f"{q}nid(@Int.0) * 4"),
        # Two same-typed arguments, which no type check tells apart:
        # `sub(15, 3)` is 12 only in the order written, and `four`'s
        # `requires` proves `sub`'s only in that order (swapped, E501).
        "argument_order": Position(f"{q}sub(@Int.0 * 5, @Int.0)",
                                   req="@Int.0 > 0"),
        # A `where` helper named `two`: the bare control reaches the helper
        # (600), and the qualified call the module's `two` (12).
        "helper_shadow": Position(
            f"{q}two(@Int.0) * 2",
            where=_helper("two(@Int -> @Int)", "@Int.0 * 100")),
    }


# form -> (module path, file name)
_FORMS = {
    "one_segment": ("ma", "ma.vera"),
    "dotted": ("lib.ma", "lib/ma.vera"),
}


def _module_source(path: str, pos: Position, q: str) -> str:
    return (f"module {path};\n\n" + _callees(q if pos.recursive else "") + "\n"
            + _fn("four(@Int -> @Int)", pos.body, req=pos.req, ens=pos.ens,
                  where=pos.where))


def _entry(imports: str, body: str) -> str:
    return f"{imports}\n\n" + _fn("main(@Unit -> @Int)", body)


def _write_cell(root: Path, form: str, position: str, placement: str, *,
                qualified: bool) -> tuple[Path, dict[str, Any]]:
    """Write one cell; return the file to run and the `cmd_run` keywords."""
    path, rel = _FORMS[form]
    q = f"{path}::" if qualified else ""
    pos = _positions(q)[position]
    target = root / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(_module_source(path, pos, q), encoding="utf-8")
    if placement == "as_entry":
        return target, {"fn_name": "four", "raw_fn_args": ["3"]}
    if placement == "direct":
        entry = _entry(f"import {path}(four);", "four(3)")
    else:
        (root / "mid.vera").write_text(
            f"module mid;\n\nimport {path}(four);\n\n"
            + _fn("six(@Int -> @Int)", "four(@Int.0)"), encoding="utf-8")
        entry = _entry("import mid(six);", "six(3)")
    (root / "main.vera").write_text(entry, encoding="utf-8")
    return root / "main.vera", {}


# ---------------------------------------------------------------------------
# Running the CLI in process
# ---------------------------------------------------------------------------


def _cli(command: str, path: Path, **kwargs: Any) -> dict[str, Any]:
    """Run `vera <command> --json <path>` in process and parse its output."""
    from vera import cli

    fns: dict[str, Callable[..., int]] = {
        "check": cli.cmd_check, "run": cli.cmd_run, "verify": cli.cmd_verify}
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = fns[command](str(path), as_json=True, **kwargs)
    try:
        payload: dict[str, Any] = json.loads(out.getvalue())
    except json.JSONDecodeError:  # pragma: no cover - a failure report
        raise AssertionError(
            f"vera {command} --json printed no JSON: "
            f"{out.getvalue()!r} {err.getvalue()!r}") from None
    payload["_rc"] = rc
    return payload


def _said(payload: dict[str, Any]) -> str:
    """A failure message that leads with what the CLI reported."""
    diags = payload.get("diagnostics", []) + payload.get("warnings", [])
    return "; ".join(
        f"{d['severity']} {d.get('error_code') or '-'}: "
        f"{d['description'][:160]}" for d in diags) or repr(payload)[:400]


def _codes(payload: dict[str, Any], key: str) -> list[tuple[str, str]]:
    return [(d["severity"], d.get("error_code") or "")
            for d in payload.get(key, [])]


def _errors(payload: dict[str, Any]) -> list[str]:
    return [d.get("error_code") or "" for d in payload.get("diagnostics", [])
            if d["severity"] == "error"]


# ---------------------------------------------------------------------------
# The issue's program
# ---------------------------------------------------------------------------

_ISSUE_MA = """\
module ma;

public fn two(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 * 2
}

public fn four(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  ma::two(@Int.0) * 2
}
"""

_ISSUE_MAIN = """\
import ma(four);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  four(3)
}
"""


class TestTheIssueProgram:
    def test_it_checks_clean_and_prints_12(self, tmp_path: Path) -> None:
        (tmp_path / "ma.vera").write_text(_ISSUE_MA, encoding="utf-8")
        (tmp_path / "main.vera").write_text(_ISSUE_MAIN, encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert check["ok"] is True, _said(check)
        assert check["diagnostics"] == [] and check["warnings"] == [], _said(check)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 12, _said(run)


# ---------------------------------------------------------------------------
# The position matrix
# ---------------------------------------------------------------------------

_POSITION_NAMES = list(_positions(""))
_PLACEMENTS = ["direct", "transitive", "as_entry"]


class TestThePositionMatrix:
    """The qualified call checks clean and prints its bare control's value
    in every position, placement and form.

    `four(3)` is 12 by computation, not a default: `ma::two` resolving to
    anything but the module's `two` gives another value (the shadowing
    helper's 600, a stranger's), and one resolving to nothing is refused.
    """

    @pytest.mark.parametrize("placement", _PLACEMENTS)
    @pytest.mark.parametrize("position", _POSITION_NAMES)
    @pytest.mark.parametrize("form", list(_FORMS))
    def test_the_qualified_call_checks_and_runs(
        self, form: str, position: str, placement: str, tmp_path: Path,
    ) -> None:
        target, run_kw = _write_cell(tmp_path, form, position, placement,
                                     qualified=True)
        check = _cli("check", target)
        assert check["ok"] is True, _said(check)
        assert _codes(check, "diagnostics") == [], _said(check)
        assert _codes(check, "warnings") == [], _said(check)
        run = _cli("run", target, **run_kw)
        assert run["ok"] is True, _said(run)
        assert run["value"] == 12, _said(run)

    @pytest.mark.parametrize("placement", _PLACEMENTS)
    def test_the_bare_control_of_the_shadowed_callee_reaches_the_helper(
        self, placement: str, tmp_path: Path,
    ) -> None:
        """The control is what makes `helper_shadow` a differential: the
        same body with the bare name prints 600, so the qualified call's 12
        is the module's `two` and not the helper."""
        target, run_kw = _write_cell(tmp_path, "one_segment", "helper_shadow",
                                     placement, qualified=False)
        run = _cli("run", target, **run_kw)
        assert run["ok"] is True and run["value"] == 600, _said(run)


# ---------------------------------------------------------------------------
# The verifier
# ---------------------------------------------------------------------------


def _verify_outcome(payload: dict[str, Any]) -> tuple[object, ...]:
    """What a verification says: its errors, its warning codes, its counts
    and each obligation's kind and status — two streams can agree on the
    counts with one obligation traded for another."""
    summary = payload.get("verification") or {}
    return (
        sorted(_errors(payload)),
        sorted(d.get("error_code") or "" for d in payload.get("warnings", [])),
        summary.get("tier1_verified"), summary.get("tier3_runtime"),
        sorted((o.get("kind"), o.get("status"))
               for o in payload.get("obligations", [])),
    )


class TestTheVerifierReadsTheOwnPath:
    """`vera verify` treats the qualified call as it treats the bare one."""

    @pytest.mark.parametrize(
        "position", [p for p in _POSITION_NAMES if p != "helper_shadow"])
    def test_every_position_verifies_as_its_control(
        self, position: str, tmp_path: Path,
    ) -> None:
        (tmp_path / "q").mkdir()
        (tmp_path / "c").mkdir()
        q_target, _ = _write_cell(tmp_path / "q", "one_segment", position,
                                  "as_entry", qualified=True)
        c_target, _ = _write_cell(tmp_path / "c", "one_segment", position,
                                  "as_entry", qualified=False)
        q = _cli("verify", q_target)
        c = _cli("verify", c_target)
        assert _verify_outcome(q) == _verify_outcome(c), (q, c)

    def test_the_arguments_are_read_in_the_order_written(
        self, tmp_path: Path,
    ) -> None:
        """`four`'s `requires(@Int.0 > 0)` proves `sub`'s precondition for
        `ma::sub(@Int.0 * 5, @Int.0)` only in the order written, so the
        qualified call verifies clean.  Read swapped (`@Int.0 > @Int.0 * 5`)
        it is E501, which is how the `argument_order` cell above tells the
        two readings apart rather than finding both sides refused."""
        target, _ = _write_cell(tmp_path, "one_segment", "argument_order",
                                "as_entry", qualified=True)
        verify = _cli("verify", target)
        assert verify["ok"] is True and _errors(verify) == [], _said(verify)

    def test_a_generic_clone_reads_its_own_module_path(
        self, tmp_path: Path,
    ) -> None:
        """A generic of `ma` whose body calls `ma`'s PRIVATE `ppos(0)` by
        path, against `requires(@Int.0 > 0)`.  Its clone is verified at the
        importer, in `ma`'s scope — where the path is `ma`'s own — so the
        broken precondition is E501, as with the bare call."""
        outcomes = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n" + _callees("") + "\n"
                + _fn("ppos(@Int -> @Int)", "@Int.0", vis="private",
                      req="@Int.0 > 0") + "\n"
                + "public forall<T> fn gcall(@T -> @Int)\n  requires(true)\n"
                "  ensures(true)\n  effects(pure)\n{\n"
                f"  {q}ppos(0)\n}}\n\n"
                + _fn("four(@Int -> @Int)", "gcall(true)"),
                encoding="utf-8")
            (root / "main.vera").write_text(
                _entry("import ma(four);", "four(3)"), encoding="utf-8")
            outcomes.append(_verify_outcome(_cli("verify", root / "main.vera")))
        qualified, bare = outcomes
        assert qualified == bare
        assert qualified[0] == ["E501"], qualified

    def test_a_generic_clone_reads_its_callees_result_type_by_path(
        self, tmp_path: Path,
    ) -> None:
        """A generic of `ma` subtracts two results of `ma`'s PRIVATE
        `pthree`, called by path.  The clone is verified at the importer,
        where the checker's side table has nothing for the module's
        expressions, so the subtraction is `@Nat`'s — with its underflow
        obligation — only if the verifier reads `pthree`'s return type
        through the own path, as it does for the bare call."""
        outcomes = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n" + _callees("") + "\n"
                + "public forall<T> fn gsub(@T -> @Int)\n  requires(true)\n"
                "  ensures(true)\n  effects(pure)\n{\n"
                f"  nat_to_int({q}pthree(1) - {q}pthree(1))\n}}\n\n"
                + _fn("four(@Int -> @Int)", "gsub(true) + 12"),
                encoding="utf-8")
            (root / "main.vera").write_text(
                _entry("import ma(four);", "four(3)"), encoding="utf-8")
            outcomes.append(_verify_outcome(_cli("verify", root / "main.vera")))
        qualified, bare = outcomes
        assert qualified == bare
        assert ("nat_sub", "verified") in qualified[4], qualified

    def test_the_callees_precondition_is_an_obligation(
        self, tmp_path: Path,
    ) -> None:
        """`four(0)` breaks `pos`'s `requires(@Int.0 > 0)`: E501 at the
        qualified call, as at the bare one.  The verifier used to find no
        callee for the path and raise no obligation at all."""
        target, _ = _write_cell(tmp_path, "one_segment", "precondition",
                                "as_entry", qualified=True)
        verify = _cli("verify", target)
        assert _errors(verify) == ["E501"], _said(verify)

    def test_a_contract_calling_a_private_function_by_path(
        self, tmp_path: Path,
    ) -> None:
        """`four`'s `requires` calls its module's PRIVATE `ptwo` by path.  At
        the importer's call site the contract is read in the module's scope,
        where the private function is the one the path names — as the bare
        spelling reads it."""
        outcomes = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n" + _callees("") + "\n"
                + _fn("four(@Int -> @Int)", "@Int.0 * 4",
                      req=f"{q}ptwo(@Int.0) == @Int.0 * 2"),
                encoding="utf-8")
            (root / "main.vera").write_text(
                _entry("import ma(four);", "four(3)"), encoding="utf-8")
            outcomes.append(_verify_outcome(_cli("verify", root / "main.vera")))
        qualified, bare = outcomes
        assert qualified == bare
        assert qualified[0] == [] and qualified[3] == 0, qualified

    def test_a_recursive_call_by_path_counts_for_decreases(
        self, tmp_path: Path,
    ) -> None:
        """`fact`'s only recursive call is `ma::fact(@Nat.0 - 1)`: the
        measure is proved at it (Tier 1), where a call the termination walk
        did not recognise left `decreases` to a runtime check (E525)."""
        target, _ = _write_cell(tmp_path, "one_segment", "recursion",
                                "as_entry", qualified=True)
        verify = _cli("verify", target)
        assert verify["ok"] is True and _errors(verify) == [], _said(verify)
        codes = [d.get("error_code") for d in verify["warnings"]]
        assert "E525" not in codes, _said(verify)

    def test_a_callee_reached_only_through_a_clone_is_verified(
        self, tmp_path: Path,
    ) -> None:
        """`four` calls `ma`'s private generic `pg`, whose body calls
        `pub_g`, a generic the entry imports; `pub_g` calls `ma`'s private
        `pg2`, whose `ensures(false)` is a lie.  The entry reaches `pub_g`
        only through `pg`'s clone, where the verifier reads calls by name,
        so it reaches `pg2`'s clone only because the call by the path is
        renamed onto `pg2`'s key as the bare call is: E500 in both
        spellings, where a call left as written would verify clean.  The
        program is not run: code generation drops `main` in both spellings
        (#1575)."""
        outcomes = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n"
                "private forall<T> fn pg2(@T -> @T)\n  requires(true)\n"
                "  ensures(false)\n  effects(pure)\n{\n  @T.0\n}\n\n"
                "public forall<T> fn pub_g(@T -> @T)\n  requires(true)\n"
                "  ensures(true)\n  effects(pure)\n{\n"
                f"  {q}pg2(@T.0)\n}}\n\n"
                "private forall<T> fn pg(@T -> @T)\n  requires(true)\n"
                "  ensures(true)\n  effects(pure)\n{\n  pub_g(@T.0)\n}\n\n"
                + _fn("four(@Int -> @Int)", f"{q}pg(@Int.0) * 4"),
                encoding="utf-8")
            (root / "main.vera").write_text(
                _entry("import ma(four, pub_g);", "four(3)"),
                encoding="utf-8")
            outcomes.append(_verify_outcome(_cli("verify", root / "main.vera")))
        qualified, bare = outcomes
        assert qualified == bare
        assert qualified[0] == ["E500"], qualified


# ---------------------------------------------------------------------------
# The #732 differential
# ---------------------------------------------------------------------------


def _emitted_and_discovered(
    root: Path,
) -> tuple[set[object], set[object]]:
    """``(codegen emitted, verifier discovered)`` instantiations for the
    program at *root* — the two sides of the #732 differential, read from
    the records each side consumes."""
    from vera.checker import typecheck_with_artifacts
    from vera.codegen.core import CodeGenerator
    from vera.parser import parse_to_ast
    from vera.resolver import ModuleResolver
    from vera.verifier import ContractVerifier

    main_path = root / "main.vera"
    source = main_path.read_text(encoding="utf-8")
    program = parse_to_ast(source)
    resolved = ModuleResolver(_root=root).resolve_imports(program, main_path)
    diags, arts = typecheck_with_artifacts(
        program, source, file=str(main_path), resolved_modules=resolved,
        collect_module_artifacts=True,
    )
    assert not [d for d in diags if d.severity == "error"], diags
    gen = CodeGenerator(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
        module_artifacts=arts.module_artifacts,
    )
    gen.compile_program(program)
    emitted = set(getattr(gen, "_emitted_instances", set()))
    verifier = ContractVerifier(
        source=source, file=str(main_path), resolved_modules=resolved,
        expr_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    verifier.register_program(program)
    discovered = {(name, ct) for name, cts in verifier._instances.items()
                  for ct in cts}
    return emitted, discovered


_PRIVATE_GENERIC = """\
private forall<T> fn pgid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
"""

_GENERIC_CALLER = """\
public forall<T> fn gcall(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  {q}gid(3)
}
"""


class TestBothSidesNameTheSameClones:
    """A generic called by its module's own path from that module's body is
    the clone code generation emits, on the verifier's side too."""

    @pytest.mark.parametrize("placement", ["direct", "transitive"])
    @pytest.mark.parametrize("callee", ["gid", "pgid", "via_generic"])
    def test_emitted_equals_discovered_and_the_control(
        self, callee: str, placement: str, tmp_path: Path,
    ) -> None:
        results = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            if callee == "via_generic":
                body = "gcall(true) * 4"
                extra = _GENERIC_CALLER.replace("{q}", q)
            else:
                body = f"{q}{callee}(@Int.0) * 4"
                extra = ""
            (root / "ma.vera").write_text(
                "module ma;\n\n" + _callees("") + "\n" + _PRIVATE_GENERIC
                + "\n" + extra + "\n" + _fn("four(@Int -> @Int)", body),
                encoding="utf-8")
            if placement == "direct":
                entry = _entry("import ma(four);", "four(3)")
            else:
                (root / "mid.vera").write_text(
                    "module mid;\n\nimport ma(four);\n\n"
                    + _fn("six(@Int -> @Int)", "four(@Int.0)"),
                    encoding="utf-8")
                entry = _entry("import mid(six);", "six(3)")
            (root / "main.vera").write_text(entry, encoding="utf-8")
            results.append(_emitted_and_discovered(root))
        (q_emitted, q_discovered), (c_emitted, c_discovered) = results
        assert q_emitted, q_emitted
        assert q_emitted == q_discovered, (q_emitted, q_discovered)
        assert (q_emitted, q_discovered) == (c_emitted, c_discovered)


# ---------------------------------------------------------------------------
# Only the file's own path
# ---------------------------------------------------------------------------


_MB = "module mb;\n\n" + _fn("mbonly(@Int -> @Int)", "@Int.0")


class TestOnlyTheOwnPath:
    """A path names the file itself only when it is the path the file
    declares and is reached by; any other path must be an import."""

    def _four(self, tmp_path: Path, header: str, call: str,
              where: str = "") -> dict[str, Any]:
        (tmp_path / "ma.vera").write_text(
            header + _callees("") + "\n"
            + _fn("four(@Int -> @Int)", call, where=where), encoding="utf-8")
        (tmp_path / "mb.vera").write_text(_MB, encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            _entry("import ma(four);\nimport mb(mbonly);", "four(3)"),
            encoding="utf-8")
        return _cli("check", tmp_path / "main.vera")

    def test_a_path_that_names_no_module_is_still_e230(
        self, tmp_path: Path,
    ) -> None:
        check = self._four(tmp_path, "module ma;\n\n", "zz::two(@Int.0) * 2")
        assert _errors(check) == ["E230"], _said(check)

    def test_a_module_the_file_does_not_import_is_still_e230(
        self, tmp_path: Path,
    ) -> None:
        """`mb` is in the program — the entry imports it — but not in `ma`,
        so `mb::two` names nothing `ma` can see.  On `main` it ran as `ma`'s
        own `two`: code generation dropped the path."""
        check = self._four(tmp_path, "module ma;\n\n", "mb::two(@Int.0) * 2")
        assert _errors(check) == ["E230"], _said(check)

    def test_an_unknown_function_under_the_own_path_is_e233(
        self, tmp_path: Path,
    ) -> None:
        check = self._four(tmp_path, "module ma;\n\n", "ma::nope(@Int.0)")
        assert _errors(check) == ["E233"], _said(check)
        (diag,) = [d for d in check["diagnostics"] if d["severity"] == "error"]
        assert "'nope'" in diag["description"], diag

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("callee", ["abs", "two"],
                             ids=["built_in", "imported"])
    def test_a_name_in_scope_the_file_does_not_declare_is_e233(
        self, callee: str, placement: str, tmp_path: Path,
    ) -> None:
        """`abs` is a built-in and `two` is imported from `mb`: each is in
        scope in `ma`, and its bare call checks, but neither is a function
        `ma` declares, so the path does not name it."""
        def write(call: str) -> Path:
            (tmp_path / "ma.vera").write_text(
                "module ma;\n\nimport mb(two);\n\n"
                + _fn("four(@Int -> @Int)", f"{call}(@Int.0) * 4"),
                encoding="utf-8")
            (tmp_path / "mb.vera").write_text(
                "module mb;\n\n" + _fn("two(@Int -> @Int)", "@Int.0 * 2"),
                encoding="utf-8")
            if placement == "entry":
                return tmp_path / "ma.vera"
            (tmp_path / "main.vera").write_text(
                _entry("import ma(four);", "four(3)"), encoding="utf-8")
            return tmp_path / "main.vera"
        bare = _cli("check", write(callee))
        assert bare["ok"] is True, _said(bare)
        check = _cli("check", write(f"ma::{callee}"))
        assert _errors(check) == ["E233"], _said(check)
        (diag,) = [d for d in check["diagnostics"] if d["severity"] == "error"]
        assert f"'{callee}'" in diag["description"], diag

    def test_a_where_helper_is_not_a_function_of_the_module(
        self, tmp_path: Path,
    ) -> None:
        check = self._four(
            tmp_path, "module ma;\n\n", "ma::helper(@Int.0)",
            where=_helper("helper(@Int -> @Int)", "@Int.0"))
        assert _errors(check) == ["E233"], _said(check)
        (diag,) = [d for d in check["diagnostics"] if d["severity"] == "error"]
        assert "'where' helper of 'four'" in diag["fix"], diag

    def test_another_modules_helper_is_not_named_as_this_files(
        self, tmp_path: Path,
    ) -> None:
        """`mb` has a `where` helper named `helper`; `ma` calls
        `ma::helper(...)`.  The fix is for `ma`'s own top level, and does
        not send the reader to `mb`'s helper."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\nimport mb(mbonly);\n\n" + _callees("") + "\n"
            + _fn("four(@Int -> @Int)", "ma::helper(@Int.0)"),
            encoding="utf-8")
        (tmp_path / "mb.vera").write_text(
            "module mb;\n\n" + _fn("mbonly(@Int -> @Int)", "helper(@Int.0)",
                                   where=_helper("helper(@Int -> @Int)",
                                                 "@Int.0")),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            _entry("import ma(four);", "four(3)"), encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert _errors(check) == ["E233"], _said(check)
        (diag,) = [d for d in check["diagnostics"] if d["severity"] == "error"]
        assert "where" not in diag["fix"], diag
        assert "Define 'fn helper(...)' at the top level" in diag["fix"], diag

    def test_a_helper_of_another_signature_does_not_capture_the_path(
        self, tmp_path: Path,
    ) -> None:
        """`four`'s `where` helper `two` takes a `@Bool`.  `ma::two(@Int.0)`
        is checked against the module's `two(@Int -> @Int)`, never the
        helper — the bare spelling would be a type error."""
        check = self._four(
            tmp_path, "module ma;\n\n", "ma::two(@Int.0) * 2",
            where=_helper("two(@Bool -> @Int)", "7"))
        assert check["ok"] is True, _said(check)
        assert _codes(check, "diagnostics") == [], _said(check)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 12, _said(run)
        bare = self._four(
            tmp_path, "module ma;\n\n", "two(@Int.0) * 2",
            where=_helper("two(@Bool -> @Int)", "7"))
        assert _errors(bare), _said(bare)

    def test_a_refused_declaration_draws_no_second_error(
        self, tmp_path: Path,
    ) -> None:
        """`ma` declares its own `abs`, which redefines a built-in (E151), and
        calls it as `ma::abs`.  The declaration's E151 is the error the
        program owes; the call adds no E233 restating it."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n" + _fn("abs(@Int -> @Int)", "@Int.0") + "\n"
            + _fn("four(@Int -> @Int)", "ma::abs(@Int.0)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "ma.vera")
        assert _errors(check) == ["E151"], _said(check)

    def test_a_path_a_resolved_module_holds_is_not_the_entrys(
        self, tmp_path: Path,
    ) -> None:
        """The entry declares `module base;` and reaches a module at path
        `base` through `mid`.  The path names that module — which the entry
        does not import, so it cannot call it (E230) — not the entry."""
        (tmp_path / "base.vera").write_text(
            "module base;\n\n" + _fn("two(@Int -> @Int)", "@Int.0 * 1000"),
            encoding="utf-8")
        (tmp_path / "mid.vera").write_text(
            "module mid;\n\nimport base(two);\n\n"
            + _fn("six(@Int -> @Int)", "two(@Int.0)"), encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "module base;\n\nimport mid(six);\n\n"
            + _fn("two(@Int -> @Int)", "@Int.0 * 2", vis="private") + "\n"
            + _fn("main(@Unit -> @Int)", "base::two(3)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert _errors(check) == ["E230"], _said(check)

    def test_a_file_without_a_module_declaration_has_no_own_path(
        self, tmp_path: Path,
    ) -> None:
        """Imported as `ma`, a file with no `module` line has no path of its
        own to qualify by.  The fix names the declaration, and following it
        makes the program check clean and print 12."""
        check = self._four(tmp_path, "", "ma::two(@Int.0) * 2")
        assert _errors(check) == ["E230"], _said(check)
        (diag,) = [d for d in check["diagnostics"] if d["severity"] == "error"]
        assert "module ma;" in diag["fix"], diag
        fixed = self._four(tmp_path, "module ma;\n\n", "ma::two(@Int.0) * 2")
        assert fixed["ok"] is True and _codes(fixed, "warnings") == [], _said(fixed)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 12, _said(run)

    @pytest.mark.parametrize("path", ["mz", "ma"])
    def test_a_declaration_the_file_is_not_imported_by_has_no_own_path(
        self, path: str, tmp_path: Path,
    ) -> None:
        """`ma.vera` declares `module mz;` and is imported as `ma`.  Neither
        spelling is its own path: `mz` is not how the program reaches it and
        `ma` is not what it declares.  The fix names the mismatch."""
        check = self._four(tmp_path, "module mz;\n\n",
                           f"{path}::two(@Int.0) * 2")
        assert _errors(check) == ["E230"], _said(check)
        (diag,) = [d for d in check["diagnostics"] if d["severity"] == "error"]
        assert "module ma;" in diag["fix"], diag

    def test_an_import_of_the_same_path_keeps_the_path(
        self, tmp_path: Path,
    ) -> None:
        """An entry that declares `module ma;` and imports a module at path
        `ma` calls the IMPORT by `ma::`, as it always did: the path names the
        module the file imports, and the entry has no own path to compete."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n" + _callees(""), encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "module ma;\n\nimport ma(two);\n\n"
            + _fn("two(@Int -> @Int)", "@Int.0 * 1000", vis="private") + "\n"
            + _fn("main(@Unit -> @Int)", "ma::two(3)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert check["ok"] is True, _said(check)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 6, _said(run)


# ---------------------------------------------------------------------------
# The call graph
# ---------------------------------------------------------------------------
#
# #1524's graph decides which functions are recursive (E137), which contracts
# call back into their own function (E138), and which calls a `decreases`
# measure is compared at.  A module-qualified call into ANOTHER module is no
# edge — the module graph is acyclic (E011) — but a call by the module's OWN
# path is the bare call it resolves to, so it is an edge: without it a
# function recursing through `ma::f(...)` needs no measure, and a false
# postcondition could be proved by the recursion it assumes.

#: shape -> ((function, callee, calls through: plain | closure | clause,
#: helper (name, callee) or None), the functions on the cycle).  A callee in
#: a `ma::` position is written with the path in the qualified variant; a
#: `where` helper is never qualified, since no path names one.
_TERM_SHAPES: dict[str, tuple[tuple[tuple[str, str, str, tuple[str, str]
                                         | None], ...], frozenset[str]]] = {
    "direct": ((("f", "ma::f", "plain", None),), frozenset({"f"})),
    "mutual_mixed": ((("f", "ma::g", "plain", None),
                      ("g", "f", "plain", None)), frozenset({"f", "g"})),
    "parent_helper": ((("f", "w", "plain", ("w", "ma::f")),),
                      frozenset({"f", "w"})),
    "closure": ((("f", "ma::f", "closure", None),), frozenset({"f"})),
    "clause": ((("f", "ma::f", "clause", None),), frozenset({"f"})),
}


def _term_fn(name: str, callee: str, how: str, *, measure: bool,
             indent: str = "", top: bool = True) -> str:
    if how == "closure":
        step = (f"apply_fn(fn(@Nat -> @Nat) effects(pure) {{ {callee}(@Nat.0) }}"
                f", @Nat.0 - 1) + 2")
    elif how == "clause":
        step = (f"handle[Exn<Nat>] {{ throw(@Nat) -> {{ {callee}(@Nat.0) + 2 }} "
                f"}} in {{ throw(@Nat.0 - 1) }}")
    else:
        step = f"{callee}(@Nat.0 - 1) + 2"
    effects = "effects(pure)"
    return (
        f"{indent}{'public ' if top else ''}fn {name}(@Nat -> @Nat)\n"
        f"{indent}  requires(true)\n{indent}  ensures(true)\n"
        + (f"{indent}  decreases(@Nat.0)\n" if measure else "")
        + f"{indent}  {effects}\n{indent}{{\n"
        f"{indent}  if @Nat.0 == 0 then {{ 0 }} else {{ {step} }}\n"
        f"{indent}}}\n")


def _term_module(shape: str, *, qualified: bool, measure: bool) -> str:
    fns, _cycle = _TERM_SHAPES[shape]
    parts = ["module ma;\n"]
    for name, callee, how, helper in fns:
        callee = callee if qualified else callee.removeprefix("ma::")
        text = _term_fn(name, callee, how, measure=measure)
        if helper is not None:
            h_name, h_callee = helper
            h_callee = h_callee if qualified else h_callee.removeprefix("ma::")
            text += ("where {\n" + _term_fn(h_name, h_callee, "plain",
                                            measure=measure, indent="  ",
                                            top=False) + "}\n")
        parts.append(text)
    parts.append(_fn("entry(@Nat -> @Nat)", "f(@Nat.0)"))
    return "\n".join(parts)


def _term_files(root: Path, shape: str, *, qualified: bool, measure: bool,
                placement: str) -> Path:
    root.mkdir(parents=True, exist_ok=True)
    (root / "ma.vera").write_text(
        _term_module(shape, qualified=qualified, measure=measure),
        encoding="utf-8")
    if placement == "entry":
        return root / "ma.vera"
    (root / "main.vera").write_text(
        _entry("import ma(entry);", "nat_to_int(entry(3))"), encoding="utf-8")
    return root / "main.vera"


def _e137_names(payload: dict[str, Any]) -> set[str]:
    return {d["description"].split("'")[1]
            for d in payload.get("diagnostics", [])
            if d.get("error_code") == "E137"}


def _statuses(payload: dict[str, Any], kind: str) -> list[str]:
    return [o.get("status") for o in payload.get("obligations", [])
            if o.get("kind") == kind]


class TestTheCallGraphReadsTheOwnPath:
    """A call by the module's own path is an edge of the call graph."""

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("shape", list(_TERM_SHAPES))
    def test_a_cycle_through_the_path_needs_a_measure(
        self, shape: str, placement: str, tmp_path: Path,
    ) -> None:
        """No measure: E137 on exactly the functions on the cycle, as for
        the bare spelling of the same cycle."""
        results = []
        for qualified in (True, False):
            target = _term_files(tmp_path / str(qualified), shape,
                                 qualified=qualified, measure=False,
                                 placement=placement)
            results.append(_cli("check", target))
        qualified_check, bare_check = results
        cycle = _TERM_SHAPES[shape][1]
        assert _e137_names(bare_check) == cycle, _said(bare_check)
        assert _e137_names(qualified_check) == cycle, _said(qualified_check)
        assert _errors(qualified_check) == _errors(bare_check)

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("shape", list(_TERM_SHAPES))
    def test_a_cycle_through_the_path_with_a_measure_is_accepted(
        self, shape: str, placement: str, tmp_path: Path,
    ) -> None:
        """With a measure on every function of the cycle it checks, verifies
        as its bare control does — the measure compared at the qualified
        call — and runs to the value its body computes."""
        results = []
        for qualified in (True, False):
            target = _term_files(tmp_path / str(qualified), shape,
                                 qualified=qualified, measure=True,
                                 placement=placement)
            check = _cli("check", target)
            assert check["ok"] is True, _said(check)
            results.append(target)
        q_target, c_target = results
        q_verify, c_verify = _cli("verify", q_target), _cli("verify", c_target)
        assert _verify_outcome(q_verify) == _verify_outcome(c_verify), (
            _said(q_verify), _said(c_verify))
        if placement == "entry" and shape in ("direct", "mutual_mixed"):
            assert _statuses(q_verify, "decreases"), _said(q_verify)
            assert set(_statuses(q_verify, "decreases")) == {"verified"}, (
                q_verify.get("obligations"))
        kw: dict[str, Any] = (
            {"fn_name": "entry", "raw_fn_args": ["3"]}
            if placement == "entry" else {})
        q_run, c_run = _cli("run", q_target, **kw), _cli("run", c_target, **kw)
        assert q_run["ok"] is True and c_run["ok"] is True, (
            _said(q_run), _said(c_run))
        assert q_run["value"] == c_run["value"] == 6, (q_run, c_run)

    @pytest.mark.parametrize("measure", [False, True])
    def test_a_contract_calling_back_through_the_path_is_e138(
        self, measure: bool, tmp_path: Path,
    ) -> None:
        results = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n"
                + _fn("f(@Nat -> @Nat)", "@Nat.0",
                      req=f"{q}f(@Nat.0) >= 0",
                      dec="@Nat.0" if measure else None),
                encoding="utf-8")
            results.append(_cli("check", root / "ma.vera"))
        qualified, bare = results
        assert "E138" in _errors(bare), _said(bare)
        assert _errors(qualified) == _errors(bare), _said(qualified)


# A postcondition no return can meet, on a recursion through the path.
_FALSE_POST = """\
module ma;

public fn spin(@Nat -> @Int)
  requires(true)
  ensures(false)
{measure}  effects(pure)
{{
  {body}
}}
"""


class TestAFalsePostconditionIsNeverProved:
    """`ensures(false)` holds of no value a call returns, so a Tier-1 claim
    for it would be a proof by the recursion it assumes.  Through the path as
    through the bare call, it is refused or left to a run-time check, and
    `vera run` never returns a value under it."""

    @pytest.mark.parametrize(("case", "measure", "body"), [
        ("no_measure", "", "{q}spin(@Nat.0)"),
        ("stalled_measure", "  decreases(@Nat.0)\n", "{q}spin(@Nat.0)"),
        ("decreasing_measure", "  decreases(@Nat.0)\n",
         "if @Nat.0 == 0 then {{ 0 }} else {{ {q}spin(@Nat.0 - 1) }}"),
    ])
    def test_it_is_never_tier_1(
        self, case: str, measure: str, body: str, tmp_path: Path,
    ) -> None:
        outcomes = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            source = _FALSE_POST.format(
                measure=measure, body=body.format(q=q).replace(
                    "{{", "{").replace("}}", "}"))
            (root / "ma.vera").write_text(source, encoding="utf-8")
            verify = _cli("verify", root / "ma.vera")
            ensures = _statuses(verify, "ensures")
            assert "verified" not in ensures, (q, verify.get("obligations"))
            run = _cli("run", root / "ma.vera", fn_name="spin",
                       raw_fn_args=["2"])
            assert run["ok"] is False, (q, run)
            outcomes.append((_errors(verify), sorted(ensures),
                             sorted(_errors(run))))
        qualified, bare = outcomes
        assert qualified == bare, (qualified, bare)
        if case == "no_measure":
            assert qualified[0] == ["E137"], qualified


class TestThePathNamesTheTopLevelFunction:
    """In the call graph as in the checker, a call by the path reaches the
    TOP-LEVEL function, never a `where` helper of the same name."""

    def test_a_helper_of_the_same_name_does_not_take_the_edge(
        self, tmp_path: Path,
    ) -> None:
        """`g` has a helper named `f` and calls `ma::f(...)`, the top-level
        `f`, which calls `g` back: `f` and `g` are on a cycle, and neither
        declares a measure.  Drawn to the helper, the edge would leave no
        cycle and no E137."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n"
            + _term_fn("f", "g", "plain", measure=False) + "\n"
            + _term_fn("g", "ma::f", "plain", measure=False)
            + "where {\n  fn f(@Nat -> @Nat)\n    requires(true)\n"
            "    ensures(true)\n    effects(pure)\n  {\n    @Nat.0 + 2\n"
            "  }\n}\n",
            encoding="utf-8")
        check = _cli("check", tmp_path / "ma.vera")
        assert _e137_names(check) == {"f", "g"}, _said(check)

    @pytest.mark.parametrize("measure", [False, True])
    def test_a_generic_recursing_through_the_path(
        self, measure: bool, tmp_path: Path,
    ) -> None:
        """A generic recursing through `ma::gf(...)` is on a cycle: E137
        without a measure, and with one its clones prove it as the bare
        spelling's do."""
        results = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n"
                "public forall<T> fn gf(@Nat, @T -> @Nat)\n"
                "  requires(true)\n  ensures(true)\n"
                + ("  decreases(@Nat.0)\n" if measure else "")
                + "  effects(pure)\n{\n"
                f"  if @Nat.0 == 0 then {{ 0 }} else {{ {q}gf(@Nat.0 - 1, "
                "@T.0) + 2 }\n}\n\n"
                + _fn("entry(@Nat -> @Nat)", "gf(@Nat.0, true)"),
                encoding="utf-8")
            check = _cli("check", root / "ma.vera")
            results.append((check, root / "ma.vera"))
        (q_check, q_path), (c_check, c_path) = results
        if not measure:
            assert _e137_names(q_check) == {"gf"}, _said(q_check)
            assert _e137_names(c_check) == {"gf"}, _said(c_check)
            return
        assert q_check["ok"] is True, _said(q_check)
        q_verify, c_verify = _cli("verify", q_path), _cli("verify", c_path)
        assert _verify_outcome(q_verify) == _verify_outcome(c_verify), (
            q_verify.get("obligations"), c_verify.get("obligations"))

    def test_a_clone_whose_path_call_a_helper_shares_claims_no_proof(
        self, tmp_path: Path,
    ) -> None:
        """A generic's clone is matched by name against its `where` group,
        and here the group holds a helper `f` while `ma::f(...)` calls the
        TOP-LEVEL `f`, which calls the generic back with the same argument.
        The helper's measure (`0`) would decrease at that call; the cycle's
        does not, and `vera run` traps on it.  So the clone's `decreases`
        is never reported verified."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n"
            "public forall<T> fn gf(@Nat, @T -> @Nat)\n"
            "  requires(true)\n  ensures(true)\n  decreases(@Nat.0)\n"
            "  effects(pure)\n{\n"
            "  if @Nat.0 == 0 then { 0 } else { ma::f(@Nat.0) + 2 }\n}\n"
            "where {\n  fn f(@Nat -> @Nat)\n    requires(true)\n"
            "    ensures(true)\n    decreases(0)\n    effects(pure)\n  {\n"
            "    @Nat.0 + 1\n  }\n}\n\n"
            + _fn("f(@Nat -> @Nat)",
                  "if @Nat.0 == 0 then { 0 } else { gf(@Nat.0, true) + 2 }",
                  dec="@Nat.0")
            + "\n" + _fn("entry(@Nat -> @Nat)", "f(@Nat.0)"),
            encoding="utf-8")
        verify = _cli("verify", tmp_path / "ma.vera")
        gf_measure = [o for o in verify["obligations"]
                      if o["kind"] == "decreases"
                      and o["location"]["line"] == 6]
        assert gf_measure, verify["obligations"]
        assert all(o["status"] != "verified" for o in gf_measure), gf_measure
        run = _cli("run", tmp_path / "ma.vera", fn_name="entry",
                   raw_fn_args=["2"])
        assert run["ok"] is False, _said(run)

    def test_an_imported_modules_graph_draws_the_path(
        self, tmp_path: Path,
    ) -> None:
        """The same guard, reached through a module: the entry imports `ma`'s
        generic `gf`, whose clone is verified at the importer against `ma`'s
        call graph.  `gf` calls `ma::probe(...)`, which calls `gf` back with
        the same argument, so the cycle's measure stalls and `vera run`
        traps.  The graph of `ma` has to draw that edge for the clone's
        `decreases` to stay unproved, as it does for the bare spelling."""
        outcomes = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(
                "module ma;\n\n"
                "public forall<T> fn gf(@Nat, @T -> @Int)\n"
                "  requires(true)\n  ensures(true)\n  decreases(@Nat.0)\n"
                "  effects(pure)\n{\n"
                "  if @Nat.0 == 0 then { 0 } else { gf(@Nat.0 - 1, @T.0) + "
                f"{q}probe(@Nat.0) }}\n}}\n\n"
                + _fn("probe(@Nat -> @Int)", "gf(@Nat.0, true)",
                      dec="@Nat.0"),
                encoding="utf-8")
            (root / "main.vera").write_text(
                _entry("import ma(probe, gf);", "probe(3) + gf(2, false)"),
                encoding="utf-8")
            verify = _cli("verify", root / "main.vera")
            measures = _statuses(verify, "decreases")
            assert measures, verify["obligations"]
            assert "verified" not in measures, (q, verify["obligations"])
            run = _cli("run", root / "main.vera")
            assert run["ok"] is False, (q, _said(run))
            outcomes.append(_verify_outcome(verify))
        qualified, bare = outcomes
        assert qualified == bare, (qualified, bare)


# ---------------------------------------------------------------------------
# The language server's warm session
# ---------------------------------------------------------------------------
#
# `vera lsp` verifies every edit on one warm `VerificationSession`, and its
# proof-delta methods read that session's verdicts.  The session replays a
# function's cached obligations while its cache key is unchanged
# (`vera.obligations.cache`), and the key follows the calls a proof reads
# THROUGH: the function's own calls, the calls in each callee's contract, and
# the calls in the refinement predicates of the types it reaches.  A call by
# the file's own path reads its callee's contract exactly as the bare call
# does, so each of those readers has to follow it too, or an edit to the
# callee's contract replays a proof that no longer holds.  The oracle is a
# fresh session on the edited text, as in #1441's cells, beside two premises:
# the original verifies clean, and the edit moves what a fresh session reports.

_WARM_H = """\
public fn h(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 * {k})
  effects(pure)
{{
  @Int.0 * {k}
}}
"""

#: shape -> (the program after `module ma;` and `h`, with `{q}` for the call's
#: prefix; the (function, obligation kind) the edit to `h` breaks).  Each
#: shape reaches `h` through ONE of the key's readers, so a fix that misses a
#: reader fails that reader's cell alone.
_WARM_SHAPES: dict[str, tuple[str, tuple[str, str]]] = {
    # The caller's own body calls `h`: the function's direct calls.
    "caller_body": ("""\
public fn four(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 * 4)
  effects(pure)
{{
  {q}h(@Int.0) * 2
}}
""", ("four", "ensures")),
    # The caller's own `ensures` calls it: still the direct calls, in a
    # contract.
    "caller_contract": ("""\
public fn four(@Int -> @Int)
  requires(true)
  ensures(@Int.result == {q}h(@Int.0) * 2)
  effects(pure)
{{
  @Int.0 * 4
}}
""", ("four", "ensures")),
    # A `where` helper of the caller calls it: verifying `four` verifies its
    # helpers, so their calls are `four`'s.
    "where_helper": ("""\
public fn four(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  helper(@Int.0)
}}
where {{
  fn helper(@Int -> @Int)
    requires(true)
    ensures(@Int.result == @Int.0 * 4)
    effects(pure)
  {{
    {q}h(@Int.0) * 2
  }}
}}
""", ("helper", "ensures")),
    # A CALLEE's `ensures` calls it, and the caller calls that callee by its
    # bare name: the closure's walk of each callee's contracts.
    "callee_contract": ("""\
public fn two(@Int -> @Int)
  requires(true)
  ensures(@Int.result == {q}h(@Int.0))
  effects(pure)
{{
  {q}h(@Int.0)
}}

public fn four(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 * 4)
  effects(pure)
{{
  two(@Int.0) * 2
}}
""", ("four", "ensures")),
    # A refinement the caller's own signature names calls it: the types the
    # declaration reaches.
    "caller_refinement": ("""\
type Twice = {{ @Int | @Int.0 == {q}h(7) }};

public fn four(@Int -> @Twice)
  requires(true)
  ensures(true)
  effects(pure)
{{
  14
}}
""", ("four", "refine_bind")),
    # A refinement a CALLEE's return type names calls it: the closure's walk
    # of each callee's signature.
    "callee_signature": ("""\
type Small = {{ @Int | @Int.0 < {q}h(1) }};

public fn mk(@Unit -> @Small)
  requires(true)
  ensures(true)
  effects(pure)
{{
  1
}}

public fn use_it(@Unit -> @Int)
  requires(true)
  ensures(@Int.result < 2)
  effects(pure)
{{
  mk(())
}}
""", ("use_it", "ensures")),
}


def _warm_source(shape: str, q: str, k: int) -> str:
    body, _broken = _WARM_SHAPES[shape]
    return ("module ma;\n\n" + _WARM_H.format(k=k) + "\n"
            + body.format(q=q))


def _session_view(result: Any) -> tuple[list[str], list[tuple[object, ...]]]:
    """Everything a consumer acts on: the error codes, and every obligation's
    function, owner, kind and status."""
    codes = sorted({d.error_code for d in result.diagnostics
                    if d.severity == "error"})
    return codes, sorted((o.fn_name, o.owner, o.kind, o.status)
                         for o in result.obligations)


def _warm_and_fresh(
    path: Path, original: str, edited: str,
) -> tuple[Any, Any, Any, Any]:
    """(original, warm after the edit, fresh on the edit, the warm session)."""
    from vera.obligations.session import VerificationSession

    warm = VerificationSession()
    before = warm.verify_source(original, file=str(path))
    after = warm.verify_source(edited, file=str(path))
    fresh = VerificationSession().verify_source(edited, file=str(path))
    return before, after, fresh, warm


def _status_of(result: Any, fn: str, kind: str) -> list[str]:
    return sorted(o.status for o in result.obligations
                  if o.fn_name == fn and o.kind == kind)


class TestTheWarmSessionReadsTheOwnPath:
    """An edit to a function a proof reads through the own path invalidates
    that proof on the warm session, as the same edit does through the bare
    call."""

    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    @pytest.mark.parametrize("shape", list(_WARM_SHAPES))
    def test_a_contract_edit_reaches_the_caller(
        self, shape: str, q: str, tmp_path: Path,
    ) -> None:
        """`h`'s contract and body go from `* 2` to `* 3`.  The warm session
        reports what a fresh one does, and that is the caller's obligation
        refuted, where the original proved it."""
        fn, kind = _WARM_SHAPES[shape][1]
        before, after, fresh, _ = _warm_and_fresh(
            tmp_path / "ma.vera", _warm_source(shape, q, 2),
            _warm_source(shape, q, 3))
        assert _session_view(before)[0] == [], _session_view(before)
        assert _status_of(before, fn, kind) == ["verified"], (
            _session_view(before))
        assert _status_of(fresh, fn, kind) == ["violated"], (
            _session_view(fresh))
        assert _session_view(after) == _session_view(fresh), (
            f"{shape}: the warm session replayed what a fresh one refutes — "
            f"warm {_session_view(after)} vs fresh {_session_view(fresh)}")

    def test_a_body_only_edit_still_replays_the_caller(
        self, tmp_path: Path,
    ) -> None:
        """The optimisation survives the path: an edit to `h`'s BODY alone
        moves nothing a caller reads, so `four` is replayed, not re-proved."""
        original = _warm_source("caller_body", "ma::", 2)
        edited = original.replace("{\n  @Int.0 * 2\n}",
                                  "{\n  @Int.0 + @Int.0\n}", 1)
        assert edited != original
        before, after, fresh, warm = _warm_and_fresh(
            tmp_path / "ma.vera", original, edited)
        assert _session_view(before)[0] == [], _session_view(before)
        assert _session_view(after) == _session_view(fresh)
        assert _status_of(after, "four", "ensures") == ["verified"]
        assert warm.last_run_stats.replayed_fns == 1, warm.last_run_stats

    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    def test_a_cycle_closed_through_the_path_reaches_the_measure(
        self, q: str, tmp_path: Path,
    ) -> None:
        """`f` recurses by a decreasing bare call and calls `g` by the path;
        `g`'s body changes from `1` to `f(@Nat.0)`, which closes a cycle
        through `f` whose measure does not decrease.  `f`'s `decreases` goes
        from proved to a run-time check, warm as fresh: the session's cycle
        key draws the path's edge, as the verifier's graph does."""
        def source(g_body: str) -> str:
            return (
                "module ma;\n\n"
                + _fn("f(@Nat -> @Int)",
                      "if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) + "
                      f"{q}g(@Nat.0) }}", dec="@Nat.0")
                + "\n" + _fn("g(@Nat -> @Int)", g_body, dec="@Nat.0"))
        before, after, fresh, _ = _warm_and_fresh(
            tmp_path / "ma.vera", source("1"), source("f(@Nat.0)"))
        assert _status_of(before, "f", "decreases") == ["verified"], (
            _session_view(before))
        assert _status_of(fresh, "f", "decreases") == ["tier3"], (
            _session_view(fresh))
        assert _session_view(after) == _session_view(fresh), (
            f"warm {_session_view(after)} vs fresh {_session_view(fresh)}")


# ---------------------------------------------------------------------------
# Code generation: a tail call by the path
# ---------------------------------------------------------------------------

_COUNT = """\
module ma;

private fn count(@Nat, @Int -> @Int)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{{
  if @Nat.0 == 0 then {{
    @Int.0
  }} else {{
    {q}count(@Nat.0 - 1, @Int.0 + 1)
  }}
}}

public fn run_it(@Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  count(@Nat.0, 0)
}}
"""

#: Far past the depth one frame per iteration reaches: a `count` that pushes
#: a frame per call exhausts the call stack below 50,000.
_DEEP = 1_000_000


def _wat(path: Path) -> str:
    """`vera compile --wat <path>`, in process."""
    from vera import cli

    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = cli.cmd_compile(str(path), wat=True)
    assert rc == 0, err.getvalue()
    return out.getvalue()


def _wat_fn(wat: str, name: str) -> str:
    """The text of the WAT function `$name`, up to the next function."""
    start = wat.index(f"(func ${name} ")
    end = wat.find("(func $", start + 1)
    return wat[start:end if end != -1 else len(wat)]


class TestATailCallByThePath:
    """A tail call by the own path compiles as the bare tail call does, to
    WASM's `return_call` (#517), so a loop written through the path runs in
    constant stack, in the entry and in a module.  A call into ANOTHER module
    cannot close a cycle (E011), so it is the own path's call that a loop
    needs."""

    @pytest.mark.parametrize("placement", ["entry", "module"])
    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    def test_a_deep_loop_runs_to_its_end(
        self, q: str, placement: str, tmp_path: Path,
    ) -> None:
        (tmp_path / "ma.vera").write_text(_COUNT.format(q=q), encoding="utf-8")
        if placement == "entry":
            run = _cli("run", tmp_path / "ma.vera", fn_name="run_it",
                       raw_fn_args=[str(_DEEP)])
        else:
            (tmp_path / "main.vera").write_text(
                _entry("import ma(run_it);", f"run_it({_DEEP})"),
                encoding="utf-8")
            run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == _DEEP, _said(run)

    @pytest.mark.parametrize("placement", ["entry", "module"])
    def test_the_call_compiles_to_return_call(
        self, placement: str, tmp_path: Path,
    ) -> None:
        """The WAT of `count` holds `return_call $count` for the qualified
        spelling as for the bare one, and no plain `call $count`."""
        bodies = []
        for q in ("ma::", ""):
            root = tmp_path / (q.rstrip(":") or "bare")
            root.mkdir()
            (root / "ma.vera").write_text(_COUNT.format(q=q), encoding="utf-8")
            target = root / "ma.vera"
            if placement == "module":
                (root / "main.vera").write_text(
                    _entry("import ma(run_it);", "run_it(3)"),
                    encoding="utf-8")
                target = root / "main.vera"
            bodies.append(_wat_fn(_wat(target), "count"))
        qualified, bare = bodies
        assert "return_call $count" in bare, bare
        assert "return_call $count" in qualified, qualified
        assert "call $count" not in qualified.replace(
            "return_call $count", ""), qualified

    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    def test_a_narrowing_tail_call_keeps_its_guard(
        self, q: str, tmp_path: Path,
    ) -> None:
        """`to_nat` returns `minus`'s `@Int` through a `@Nat` slot, so the
        call is followed by the `>= 0` guard, which a `return_call` would
        skip.  Through the path as bare: `to_nat(3)` traps on the guard
        rather than returning -7, and `to_nat(20)` is 10."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n"
            + _fn("minus(@Int -> @Int)", "@Int.0 - 10", vis="private") + "\n"
            + _fn("to_nat(@Int -> @Nat)", f"{q}minus(@Int.0)"),
            encoding="utf-8")
        trapped = _cli("run", tmp_path / "ma.vera", fn_name="to_nat",
                       raw_fn_args=["3"])
        assert trapped["ok"] is False, _said(trapped)
        assert [d.get("trap_kind") for d in trapped["diagnostics"]] == [
            "nat_guard"], trapped
        ran = _cli("run", tmp_path / "ma.vera", fn_name="to_nat",
                   raw_fn_args=["20"])
        assert ran["ok"] is True and ran["value"] == 10, _said(ran)


# ---------------------------------------------------------------------------
# An entry declaration of the same name
# ---------------------------------------------------------------------------

_ENTRY_TWO = {
    "function": _fn("two(@Int -> @Int)", "@Int.0 * 1000", vis="private"),
    "generic": ("private forall<T> fn two(@T -> @T)\n  requires(true)\n"
                "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n"),
}


class TestAnEntryDeclarationOfTheSameName:
    """The entry file declares a function named like one of `ma`'s own, so
    code generation emits `ma`'s under its `mod$` symbol and renames `ma`'s
    bare calls to it (#1508).  A call by `ma`'s own path inside `ma` reaches
    `ma`'s function as its bare call does, whatever the entry declares under
    the name: a function, or a generic, whose clone took the qualified call
    while `vera verify` proved `four` from `ma`'s `two`."""

    @pytest.mark.parametrize("placement", ["direct", "transitive"])
    @pytest.mark.parametrize("vis", ["public", "private"])
    @pytest.mark.parametrize("entry_two", list(_ENTRY_TWO))
    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    def test_the_modules_own_function_runs(
        self, q: str, entry_two: str, vis: str, placement: str,
        tmp_path: Path,
    ) -> None:
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n"
            + _fn("two(@Int -> @Int)", "@Int.0 * 2", vis=vis,
                  ens="@Int.result == @Int.0 * 2") + "\n"
            + _fn("four(@Int -> @Int)", f"{q}two(@Int.0) * 2",
                  ens="@Int.result == @Int.0 * 4"),
            encoding="utf-8")
        if placement == "direct":
            imports = "import ma(four);"
        else:
            (tmp_path / "mid.vera").write_text(
                "module mid;\n\nimport ma(four);\n\n"
                + _fn("six(@Int -> @Int)", "four(@Int.0)"), encoding="utf-8")
            imports = "import mid(six);"
        call = "four(3)" if placement == "direct" else "six(3)"
        (tmp_path / "main.vera").write_text(
            f"{imports}\n\n" + _ENTRY_TWO[entry_two] + "\n"
            + _fn("main(@Unit -> @Int)", f"{call} + two(0)"),
            encoding="utf-8")
        check = _cli("check", tmp_path / "main.vera")
        assert check["ok"] is True, _said(check)
        verify = _cli("verify", tmp_path / "main.vera")
        assert _errors(verify) == [], _said(verify)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 12, _said(run)

    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    def test_the_modules_own_generic_runs(
        self, q: str, tmp_path: Path,
    ) -> None:
        """`ma`'s own GENERIC `gid`, beside an entry function `gid`: the call
        by the path reaches `ma`'s clone, which the verifier discovers as
        code generation emits it (the #732 differential)."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n"
            "public forall<T> fn gid(@T -> @T)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n\n"
            + _fn("four(@Int -> @Int)", f"{q}gid(@Int.0) * 4"),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "import ma(four);\n\n"
            + _fn("gid(@Int -> @Int)", "@Int.0 * 1000", vis="private") + "\n"
            + _fn("main(@Unit -> @Int)", "four(3) + gid(0)"),
            encoding="utf-8")
        emitted, discovered = _emitted_and_discovered(tmp_path)
        assert emitted, emitted
        assert emitted <= discovered, (emitted, discovered)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 12, _said(run)

    @pytest.mark.parametrize("q", ["ma::", ""], ids=["qualified", "bare"])
    def test_an_entry_generic_of_the_name_gains_no_clone(
        self, q: str, tmp_path: Path,
    ) -> None:
        """`ma`'s generic `gcall` calls `ma`'s own generic `gid` at `Int`,
        and the entry declares a generic `gid` it calls only at `Bool`.
        The verifier renames the call by the path onto `ma`'s key, as it
        renames the bare call, so it discovers exactly the clones code
        generation emits (the #732 differential).  Read as written, the
        call would also instantiate the entry's `gid` at `Int`, a clone
        nothing calls."""
        (tmp_path / "ma.vera").write_text(
            "module ma;\n\n"
            "public forall<T> fn gid(@T -> @T)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n\n"
            "public forall<T> fn gcall(@T -> @Int)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n"
            f"  {q}gid(3)\n}}\n\n"
            + _fn("four(@Int -> @Int)", "gcall(true) * 4"),
            encoding="utf-8")
        (tmp_path / "main.vera").write_text(
            "import ma(four);\n\n"
            "private forall<T> fn gid(@T -> @T)\n  requires(true)\n"
            "  ensures(true)\n  effects(pure)\n{\n  @T.0\n}\n\n"
            + _fn("main(@Unit -> @Int)",
                  "if gid(true) then {\n    four(3)\n  } else {\n    0\n  }"),
            encoding="utf-8")
        emitted, discovered = _emitted_and_discovered(tmp_path)
        assert ("mod$ma$gid", ("Int",)) in emitted, emitted
        assert emitted == discovered, (emitted, discovered)
        run = _cli("run", tmp_path / "main.vera")
        assert run["ok"] is True and run["value"] == 12, _said(run)
