"""A guard on a tail call's result runs (#1849).

THE MECHANISM.  A call in tail position was lowered to `return_call` unless
`_compile_fn` knew a guard followed it, and it knew by a list: a leaf
narrowing into a bare `@Nat` return was cut from the tail-call set, and a
runtime postcondition turned every `return_call` back into a `call`.  A
return leaf coerced into a composite type with a `Nat` component is guarded
after the call by the composite coercion (`vera/wasm/coercion.py`) and was
on no list, so the guard was emitted after a `return_call` and never ran:
`wrap(@Int.0)` returned `Some(-1)` through an `@Option<Nat>` while
`vera verify` counted the check as present.

THE RULE (`ObligationTable.tail_calls`, read by `_compile_fn`).  A call in
tail position leaves by `return_call` only where nothing checked needs its
result after it: no row with a check of its own stands at the call (any
kind, any path), and the function runs no check after its body (a
non-trivial `ensures`, a guarded refined return: the table's epilogue).
Beside it, a tripwire in `_compile_fn`: a check marker after a surviving
`return_call` on the path its value leaves by stops the compile (E699).

THE INSTRUMENT.  Guard kind at the return leaf (a bare `Nat`, a refinement
at the head, a `Nat` component of `Option`, `Array`, `Tuple`, `Result`, a
`Map` value and a user data type, two levels down, a runtime-checked
postcondition) × tail form (the body's last expression, an `if` arm, a
`match` arm, a block's tail, a self-recursive loop, a mutually recursive
pair, a `where` helper, a generic callee's clone, a call by the module's own
path, a closure body, an `apply_fn` result) × a violating and a satisfying
input.  Each cell is a differential: the tail form and its twin, the same
leaf with the call's value bound by a `let` first, run to the same outcome
(the same trap kind at the violating input, the same value at the
satisfying one), and `vera verify` reports the same obligation statuses for
the two.  Beside it, each run on every pull request unless parametrised:
the `repro` pins of the issue's program and of one cell per container
kind it reached; deep tail recursion at a million steps; the tripwire,
tested by a double of a guard kind added later (a check planted after a
call, with no row the rule could read); the one-decision test (the set
the translator is handed is `ObligationTable.tail_calls`, untouched); and
the universal form, no check after a `return_call` on its value's exit
path, over the corpus and the program generator's seeds 0 to 999.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline
from vera.trap_registry import CHECK_MARKER_RE

pytestmark = pytest.mark.matrix(decides=[
    "vera/obligations/table.py", "vera/codegen/functions.py",
    "vera/tail_position.py", "vera/wasm/calls.py", "vera/wasm/coercion.py"])

FILE = "tail_guard.vera"
ROOT = Path(__file__).resolve().parent.parent

_C = "  requires(true)\n  ensures(true)\n  effects(pure)\n"


def _fn(vis: str, sig: str, body: str, *, contracts: str = _C,
        where: str = "") -> str:
    indented = "\n".join("  " + ln if ln else ln for ln in body.splitlines())
    tail = f"\nwhere {{\n{where}}}" if where else ""
    prefix = f"{vis} " if vis else ""
    return f"{prefix}fn {sig}\n{contracts}{{\n{indented}\n}}{tail}\n"


# =====================================================================
# The guard kinds
# =====================================================================


@dataclass(frozen=True)
class Kind:
    """A guard at a return leaf: the function's return type *ret*, the
    type *src* the leaf's call returns, how *mk* builds a *src* from
    `@Int.0`, and how *observe* reads an `@Int` back out of a *ret* value
    (``CALL`` stands for the value)."""

    id: str
    ret: str
    src: str
    mk: str
    observe: str
    decls: str = ""
    #: The `ensures` of every function returning *ret*.
    ensures: str = "true"


_OPT_OBS = "match CALL {\n  Some(@Nat) -> nat_to_int(@Nat.0),\n  None -> 7\n}"

KINDS: tuple[Kind, ...] = (
    Kind("bare_nat", "Nat", "Int", "@Int.0", "nat_to_int(CALL)"),
    Kind("refined_head", "PosInt", "Int", "@Int.0", "CALL",
         decls="type PosInt = { @Int | @Int.0 > 0 };\n\n"),
    Kind("option", "Option<Nat>", "Option<Int>", "Some(@Int.0)", _OPT_OBS),
    Kind("array", "Array<Nat>", "Array<Int>", "[@Int.0]",
         "nat_to_int(CALL[0])"),
    Kind("tuple", "Tuple<Nat, Int>", "Tuple<Int, Int>", "Tuple(@Int.0, 1)",
         "match CALL {\n  Tuple(@Nat, @Int) -> nat_to_int(@Nat.0)\n}"),
    Kind("result", "Result<Nat, Bool>", "Result<Int, Bool>", "Ok(@Int.0)",
         "match CALL {\n  Ok(@Nat) -> nat_to_int(@Nat.0),\n  Err(@Bool) -> 7\n}"),
    Kind("map_value", "Map<String, Nat>", "Map<String, Int>",
         'map_insert(map_new(), "k", @Int.0)',
         'match map_get(CALL, "k") {\n  Some(@Nat) -> nat_to_int(@Nat.0),\n'
         "  None -> 7\n}"),
    Kind("user_data", "Box<Nat>", "Box<Int>", "Box(@Int.0)",
         "match CALL {\n  Box(@Nat) -> nat_to_int(@Nat.0)\n}",
         decls="private data Box<T> {\n  Box(T)\n}\n\n"),
    Kind("two_levels", "Option<Option<Nat>>", "Option<Option<Int>>",
         "Some(Some(@Int.0))",
         "match CALL {\n  Some(Some(@Nat)) -> nat_to_int(@Nat.0),\n"
         "  Some(None) -> 8,\n  None -> 7\n}"),
    Kind("postcondition", "Int", "Int", "@Int.0", "CALL",
         ensures="@Int.result >= 0"),
)


# =====================================================================
# The tail forms
# =====================================================================


def _leaf(kind: Kind, call: str, twin: bool) -> str:
    """The return leaf: *call* itself, or its twin, the call's value bound
    by a `let` and read back."""
    if not twin:
        return call
    return f"let @{kind.src} = {call};\n@{kind.src}.0"


def _contracts(kind: Kind, decreases: str = "") -> str:
    dec = f"  decreases({decreases})\n" if decreases else ""
    return (f"  requires(true)\n  ensures({kind.ensures})\n{dec}"
            "  effects(pure)\n")


def _block(text: str) -> str:
    return "{\n" + "\n".join("  " + ln for ln in text.splitlines()) + "\n}"


def _wrap(kind: Kind, name: str = "wrap", vis: str = "private") -> str:
    return _fn(vis, f"{name}(@Int -> @{kind.src})", kind.mk)


def _f(kind: Kind, body: str, where: str = "") -> str:
    return _fn("public", f"f(@Int -> @{kind.ret})", body,
               contracts=_contracts(kind), where=where)


def _form_last(kind: Kind, twin: bool) -> str:
    return _wrap(kind) + "\n" + _f(kind, _leaf(kind, "wrap(@Int.0)", twin))


def _form_if(kind: Kind, twin: bool) -> str:
    body = (f"if @Int.0 > 100 then {_block(_leaf(kind, 'wrap(0)', twin))}"
            f" else {_block(_leaf(kind, 'wrap(@Int.0)', twin))}")
    return _wrap(kind) + "\n" + _f(kind, body)


def _form_match(kind: Kind, twin: bool) -> str:
    some = _block(_leaf(kind, "wrap(@Int.0)", twin))
    none = _block(_leaf(kind, "wrap(0)", twin))
    body = (f"match Some(@Int.0) {{\n  Some(@Int) -> {some},\n"
            f"  None -> {none}\n}}")
    return _wrap(kind) + "\n" + _f(kind, body)


def _form_block_tail(kind: Kind, twin: bool) -> str:
    body = "let @Int = @Int.0 + 0;\n" + _leaf(kind, "wrap(@Int.0)", twin)
    return _wrap(kind) + "\n" + _f(kind, body)


def _counted(kind: Kind, name: str, other: str, twin: bool) -> str:
    body = (f"if @Nat.0 == 0 then {_block(_leaf(kind, 'wrap(@Int.0)', twin))}"
            f" else {{\n  {other}(@Int.0, @Nat.0 - 1)\n}}")
    return _fn("private", f"{name}(@Int, @Nat -> @{kind.ret})", body,
               contracts=_contracts(kind, "@Nat.0"))


def _form_self(kind: Kind, twin: bool) -> str:
    return (_wrap(kind) + "\n" + _counted(kind, "loop", "loop", twin) + "\n"
            + _f(kind, "loop(@Int.0, 3)"))


def _form_mutual(kind: Kind, twin: bool) -> str:
    return (_wrap(kind) + "\n" + _counted(kind, "ev", "od", twin) + "\n"
            + _counted(kind, "od", "ev", twin) + "\n"
            + _f(kind, "ev(@Int.0, 3)"))


def _form_where(kind: Kind, twin: bool) -> str:
    helper = _fn("", f"w(@Int -> @{kind.src})", kind.mk)
    helper = "\n".join("  " + ln if ln else ln for ln in helper.splitlines())
    return _f(kind, _leaf(kind, "w(@Int.0)", twin), where=helper + "\n")


_IDG = _fn("private forall<T>", "idg(@T -> @T)", "@T.0")


def _form_generic(kind: Kind, twin: bool) -> str:
    mk = kind.mk if kind.id != "map_value" else (
        f"let @{kind.src} = {kind.mk};\n@{kind.src}.0")
    gen = _fn("private", f"mk(@Int -> @{kind.src})", mk)
    return (_IDG + "\n" + gen + "\n"
            + _f(kind, _leaf(kind, "idg(mk(@Int.0))", twin)))


def _form_module_path(kind: Kind, twin: bool) -> str:
    return ("module mm;\n\n" + _wrap(kind) + "\n"
            + _f(kind, _leaf(kind, "mm::wrap(@Int.0)", twin)))


def _form_closure_body(kind: Kind, twin: bool) -> str:
    inner = _leaf(kind, "wrap(@Int.0)", twin)
    clo = (f"fn(@Int -> @{kind.ret}) effects(pure) "
           + _block(inner))
    return _wrap(kind) + "\n" + _f(kind, f"apply_fn({clo}, @Int.0)")


def _form_apply_fn(kind: Kind, twin: bool) -> str:
    clo = f"fn(@Int -> @{kind.src}) effects(pure) {{\n  wrap(@Int.0)\n}}"
    return _wrap(kind) + "\n" + _f(
        kind, _leaf(kind, f"apply_fn({clo}, @Int.0)", twin))


FORMS = {
    "last": _form_last,
    "if_arm": _form_if,
    "match_arm": _form_match,
    "block_tail": _form_block_tail,
    "self_recursive": _form_self,
    "mutual_pair": _form_mutual,
    "where_helper": _form_where,
    "generic_clone": _form_generic,
    "module_path": _form_module_path,
    "closure_body": _form_closure_body,
    "apply_fn_result": _form_apply_fn,
}


def program(kind: Kind, form: str, twin: bool) -> str:
    """The cell's program: the form, then `show`, which reads an `@Int`
    out of `f`'s value."""
    body = FORMS[form](kind, twin)
    head, sep, rest = body.partition("module mm;\n\n")
    module = head + sep if sep else ""
    body = rest if sep else body
    show = _fn("public", "show(@Int -> @Int)",
               kind.observe.replace("CALL", "f(@Int.0)"))
    return module + kind.decls + body + "\n" + show


# =====================================================================
# The differential
# =====================================================================


def _outcome(source: str, arg: int) -> tuple[str, object]:
    ran = pipeline.run(source, "show", [arg], file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, [
        (d.error_code, d.description[:100]) for d in ran.compiled.errors
    ] if ran.compiled is not None else "no compile"
    if ran.trap is not None:
        return ("trap", ran.trap.kind)
    return ("value", ran.value)


def _statuses(source: str) -> tuple[list[str], list[tuple[str, str]]]:
    verified = pipeline.verify(source, file=FILE)
    assert verified.checked.ok, [
        (d.error_code, d.description[:100]) for d in verified.checked.errors]
    codes = sorted(d.error_code for d in verified.errors)
    return codes, sorted((o.kind, o.status) for o in verified.obligations)


#: The cells the checker refuses, by kind and form: none measured.
CELLS = [(k, f) for k in KINDS for f in FORMS]


@pytest.mark.parametrize(
    ("kind", "form"), CELLS, ids=[f"{k.id}-{f}" for k, f in CELLS])
def test_tail_form_agrees_with_its_let_twin(kind: Kind, form: str) -> None:
    tail, twin = program(kind, form, False), program(kind, form, True)
    assert _statuses(tail) == _statuses(twin)
    violating, satisfying = _outcome(tail, -1), _outcome(tail, 5)
    assert violating == _outcome(twin, -1)
    assert satisfying == _outcome(twin, 5)
    assert violating[0] == "trap", violating
    assert satisfying == ("value", 5), satisfying


# =====================================================================
# The issue's program, pinned
# =====================================================================

_ISSUE = """\
private fn wrap(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn f(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@Int.0)
}

public fn g(@Int -> @Option<Nat>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = wrap(@Int.0);
  @Option<Int>.0
}

public fn show_f(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match f(@Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 7
  }
}

public fn show_g(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match g(@Int.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 7
  }
}
"""


# =====================================================================
# One cell per container kind the issue's mechanism reached, pinned
# =====================================================================


def _repro_kind(kind_id: str) -> None:
    """The kind's tail form traps at the violating input, as its `let`
    twin does, and returns the value at the satisfying one."""
    (kind,) = [k for k in KINDS if k.id == kind_id]
    source = program(kind, "last", False)
    ran = pipeline.run(source, "show", [-1], file=FILE)
    assert ran.trap is not None, f"{kind_id}: returned {ran.value}"
    assert ran.trap.kind == "nat_guard"
    assert pipeline.run(source, "show", [5], file=FILE).value == 5


def test_repro_option_component() -> None:
    _repro_kind("option")


def test_repro_array_component() -> None:
    _repro_kind("array")


def test_repro_result_component() -> None:
    _repro_kind("result")


def test_repro_map_value_component() -> None:
    _repro_kind("map_value")


def test_repro_user_data_component() -> None:
    _repro_kind("user_data")


def test_repro_two_levels_down() -> None:
    _repro_kind("two_levels")


def test_repro_issue_program_tail_form_traps() -> None:
    """`f`'s call is its last expression: the coercion's guard runs."""
    ran = pipeline.run(_ISSUE, "show_f", [-1], file=FILE)
    assert ran.trap is not None, f"returned {ran.value}"
    assert ran.trap.kind == "nat_guard"


def test_repro_issue_program_let_form_traps() -> None:
    ran = pipeline.run(_ISSUE, "show_g", [-1], file=FILE)
    assert ran.trap is not None and ran.trap.kind == "nat_guard"


def test_repro_issue_program_returns_at_a_satisfying_input() -> None:
    assert pipeline.run(_ISSUE, "show_f", [3], file=FILE).value == 3


def test_repro_issue_program_lowers_the_tail_call_to_a_call() -> None:
    wat = pipeline.compile(_ISSUE, file=FILE).wat
    f = _func(wat, "f")
    assert "return_call" not in f
    assert "call $:wrap" in f


# =====================================================================
# Tail recursion keeps its `return_call`
# =====================================================================

_DEEP = """\
public fn drain(@Nat -> @Nat)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    0
  } else {
    drain(@Nat.0 - 1)
  }
}

private fn wrap(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn count(@Int, @Nat -> @Option<Nat>)
  requires(true)
  ensures(true)
  decreases(@Nat.0)
  effects(pure)
{
  if @Nat.0 == 0 then {
    wrap(@Int.0)
  } else {
    count(@Int.0, @Nat.0 - 1)
  }
}

public fn show_count(@Int, @Nat -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match count(@Int.0, @Nat.0) {
    Some(@Nat) -> nat_to_int(@Nat.0),
    None -> 7
  }
}
"""


def test_repro_deep_tail_recursion_runs_a_million_steps() -> None:
    assert pipeline.run(_DEEP, "drain", [1_000_000], file=FILE).value == 0


def test_repro_a_guarded_leaf_beside_a_self_tail_call_keeps_it() -> None:
    """The guarded leaf lowers to a `call`; the self tail call beside it
    keeps its `return_call`, so the loop runs a million steps and the
    guard still traps at its end."""
    wat = pipeline.compile(_DEEP, file=FILE).wat
    count = _func(wat, "count")
    assert "return_call $:count" in count
    assert "return_call $:wrap" not in count
    assert pipeline.run(
        _DEEP, "show_count", [4, 1_000_000], file=FILE).value == 4
    ran = pipeline.run(_DEEP, "show_count", [-4, 1_000_000], file=FILE)
    assert ran.trap is not None and ran.trap.kind == "nat_guard"


# =====================================================================
# The tripwire: a guard kind the rule does not see fails loudly
# =====================================================================

#: A program with no row at its tail call: the rule keeps the
#: `return_call`, and only a guard the table does not list could follow it.
_UNGUARDED = """\
private fn wrap(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  Some(@Int.0)
}

public fn f(@Int -> @Option<Int>)
  requires(true)
  ensures(true)
  effects(pure)
{
  wrap(@Int.0)
}
"""

#: An emitter key the trap registry knows, for the planted check's record.
_PLANTED_EMITTER = "wasm/calls_strings.py:_float_to_string_core"


def _plant(monkeypatch: pytest.MonkeyPatch, *, after: bool) -> None:
    """A test double of a guard kind added later: a recorded check emitted
    beside each call of `wrap`, after it (where it would read the call's
    result) or before it, with no row in the table, so the tail-call rule
    cannot know of it."""
    from vera.wasm.context import WasmContext
    original = WasmContext._translate_call

    def translate(self, call, env, **kwargs):  # type: ignore[no-untyped-def]
        out = original(self, call, env, **kwargs)
        if out is None or call.name != "wrap":
            return out
        check = "nop" + self._record_shared_check(emitter=_PLANTED_EMITTER)
        return [*out, check] if after else [check, *out]

    monkeypatch.setattr(WasmContext, "_translate_call", translate)


def test_repro_tripwire_refuses_a_planted_guard_after_a_return_call(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A check after the surviving `return_call $:wrap` stops the compile
    with one [E699] naming `f`, the call, and the fix to report it."""
    _plant(monkeypatch, after=True)
    compiled = pipeline.compile(_UNGUARDED, file=FILE)
    refusals = [d for d in compiled.diagnostics if d.error_code == "E699"]
    assert len(refusals) == 1, [d.description for d in compiled.diagnostics]
    (refusal,) = refusals
    assert "'f'" in refusal.description
    assert "return_call $:wrap" in refusal.description
    assert refusal.fix and "report" in refusal.fix
    assert refusal.spec_ref


def test_repro_tripwire_passes_a_planted_guard_before_the_call(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The nearest accepted neighbour: the same check before the call is on
    no `return_call`'s exit path, so `f` compiles and keeps its tail call."""
    _plant(monkeypatch, after=False)
    compiled = pipeline.compile(_UNGUARDED, file=FILE)
    assert compiled.ok, [d.description for d in compiled.diagnostics]
    assert "return_call $:wrap" in _func(compiled.wat, "f")


def test_repro_the_rule_keeps_the_unguarded_tail_call() -> None:
    """Without the double, `f`'s call has no row and keeps `return_call`."""
    compiled = pipeline.compile(_UNGUARDED, file=FILE)
    assert compiled.ok
    assert "return_call $:wrap" in _func(compiled.wat, "f")


# =====================================================================
# One decision: the code generator's tail-call set is the table's
# =====================================================================


def test_the_tail_call_set_is_the_tables_alone(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Over the corpus, each function's set of tail-call sites handed to
    the translator is exactly `ObligationTable.tail_calls` of it, and is
    still that set when the function is lowered: nothing in `_compile_fn`
    subtracts from it or adds to it."""
    from vera.obligations.table import ObligationTable
    from vera.wasm.context import WasmContext
    decided: list[set[int]] = []
    handed: list[tuple[object, set[int], set[int]]] = []
    tail_calls = ObligationTable.tail_calls
    set_context = WasmContext.set_tail_call_context

    def table_rule(self, decl):  # type: ignore[no-untyped-def]
        result = tail_calls(self, decl)
        decided.append(set(result))
        return result

    def context(self, sites, self_ret_wt):  # type: ignore[no-untyped-def]
        assert decided, "a tail-call set handed over before the table decided"
        handed.append((self, set(sites), decided.pop()))
        return set_context(self, sites, self_ret_wt)

    monkeypatch.setattr(ObligationTable, "tail_calls", table_rule)
    monkeypatch.setattr(WasmContext, "set_tail_call_context", context)
    nonempty = 0
    for path in _corpus():
        pipeline.compile(path, file=str(path))
        for ctx, sites, table in handed:
            assert sites == table, path.name
            assert ctx._tail_call_sites == table, path.name
            nonempty += bool(table)
        handed.clear()
        assert decided == [], path.name
    assert nonempty > 50


# =====================================================================
# The universal form: no check follows a `return_call`
# =====================================================================


def _func(wat: str, name: str) -> str:
    start = wat.index(f"(func $:{name} ")
    end = wat.find("\n  (func ", start + 1)
    return wat[start:end if end != -1 else len(wat)]


def checks_after_tail_calls(wat: str) -> list[str]:
    """Each `return_call` in *wat* with a recorded check on the path its
    value would leave by (see `vera.codegen.functions.checks_after`)."""
    from vera.codegen.functions import checks_after
    lines = wat.splitlines()
    return [lines[i].strip() for i in range(len(lines))
            if lines[i].lstrip().startswith("return_call ")
            and checks_after(lines, i)]


def _corpus() -> list[Path]:
    return (sorted((ROOT / "examples").glob("*.vera"))
            + sorted((ROOT / "tests" / "conformance").glob("*.vera")))


def test_no_check_follows_a_return_call_in_the_corpus() -> None:
    """Every example and conformance program that compiles (the sweep is
    one test, so every pull request runs it whole)."""
    found, tail_calls = [], 0
    for path in _corpus():
        compiled = pipeline.compile(path, file=str(path))
        if not compiled.ok:
            continue
        tail_calls += compiled.wat.count("return_call ")
        found.extend((path.name, hit)
                     for hit in checks_after_tail_calls(compiled.wat))
    assert found == []
    assert tail_calls > 100, "the corpus lost its tail calls"


def test_the_universal_form_sees_a_check_after_a_return_call() -> None:
    """The scan's own proof: a function with a check spliced after its
    `return_call` is reported."""
    from vera.trap_registry import check_marker
    wat = ("  (func $:f (result i64)\n    return_call $:g\n"
           "    local.set 1\n    if\n      nop"
           + check_marker(1) + "\n      unreachable\n    end\n  )")
    assert checks_after_tail_calls(wat) == ["return_call $:g"]


def test_the_universal_form_reads_past_the_branch_it_leaves() -> None:
    """A `return_call` in a `then` arm is followed by the `else` arm (not
    on its path, so its checks do not count) and by what follows the `if`
    (on its path, so they do)."""
    from vera.trap_registry import check_marker
    m = check_marker(1)
    other_arm = ("  (func $:f (result i64)\n    if (result i64)\n"
                 "      return_call $:g\n    else\n"
                 f"      nop{m}\n    end\n  )")
    after_if = ("  (func $:f (result i64)\n    if (result i64)\n"
                "      return_call $:g\n    else\n      i64.const 0\n"
                f"    end\n    nop{m}\n  )")
    assert checks_after_tail_calls(other_arm) == []
    assert checks_after_tail_calls(after_if) == ["return_call $:g"]


def test_the_universal_form_ignores_an_epilogue_with_no_check() -> None:
    """The unreached remainder of a call's epilogue (the `$gc_sp` restore,
    whose shadow push holds a bare `unreachable`) is no recorded check."""
    wat = ("  (func $:f (result i32)\n    return_call $:g\n    local.set 4\n"
           "    global.get $gc_sp\n    if\n      unreachable\n    end\n  )")
    assert checks_after_tail_calls(wat) == []
    assert CHECK_MARKER_RE.search(wat) is None


_SEED_CHUNK = 50


@pytest.mark.parametrize(
    "first", range(0, 1000, _SEED_CHUNK), ids=lambda s: f"seeds{s}")
def test_generator_programs_carry_no_check_after_a_return_call(
    first: int, tmp_path: Path,
) -> None:
    """The universal form over the program generator's seeds 0 to 999,
    fifty to a cell; a program with a module has it written beside it."""
    from tests import program_generator as gen
    found, compiled_any = [], False
    for seed in range(first, first + _SEED_CHUNK):
        prog = gen.generate(seed)
        if prog.module is not None:
            (tmp_path / gen.MODULE_FILE).write_text(
                gen.render_module(prog), encoding="utf-8")
        entry = tmp_path / f"gen{seed}.vera"
        entry.write_text(prog.render(), encoding="utf-8")
        compiled = pipeline.compile(entry, file=str(entry))
        if compiled.ok:
            compiled_any = True
            found.extend((seed, hit)
                         for hit in checks_after_tail_calls(compiled.wat))
    assert compiled_any
    assert found == []
