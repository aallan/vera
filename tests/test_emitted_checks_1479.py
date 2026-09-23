"""The per-module record of emitted runtime checks (#1479).

``CompileResult.emitted_checks`` says which runtime checks a compiled module
contains: one :class:`vera.trap_registry.EmittedCheck` per check, naming the
emitter from :data:`vera.trap_registry.TRAP_EMITTERS`, the trap kind the
check reports, the verifier obligation kinds it is the runtime half of, the
WASM function it sits in, and the source span of the node it guards.  It is
the codegen side of the obligation differential (#1480), so what matters is
that it is COMPLETE (every check the module holds is listed) and EXACT
(nothing the module lacks is listed).

The cells here hold those two properties:

* every per-site emitter the registry names has a fixture that compiles a
  program through the real pipeline and finds that emitter's check in the
  record, at the span the emitter's row says it locates;
* a check emitted into a closure body, a ``where`` helper, or a postcondition
  lands in the record under the function it actually sits in;
* a check whose function is dropped after compiling, or whose translation is
  thrown away and redone, is not listed;
* a generic body contributes one entry per monomorphised clone, and an
  imported body's entries name the imported file.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

import pytest

from tests.codegen_helpers import wat_fn_body
from tests.module_fixture_helpers import build_multi_module
from vera.checker import typecheck_with_artifacts
from vera.codegen import compile as codegen_compile
from vera.codegen import CodeGenerator
from vera.codegen.api import CompileResult, execute
from vera.parser import parse_to_ast
from vera.skip import CodegenInvariantError
from vera.trap_registry import (
    CHECK_MARKER_RE,
    TRAP_EMITTERS,
    TRAP_KINDS,
    EmittedCheck,
    signal_call_pattern,
)


def _compile(source: str, file: str = "prog.vera") -> CompileResult:
    """Parse, check (collecting artifacts) and compile, as `vera compile`
    does — the overflow classifier and the widening guards read the
    checker's side tables, so a bare transform-and-compile would measure a
    different backend."""
    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source, file=file)
    errors = [d.description for d in diags if d.severity == "error"]
    assert not errors, f"fixture does not type-check: {errors}"
    result = codegen_compile(
        program, source=source, file=file,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    assert result.ok, [d.description for d in result.diagnostics]
    return result


def _by_emitter(result: CompileResult, emitter: str) -> list[EmittedCheck]:
    return [c for c in result.emitted_checks if c.emitter == emitter]


_HEAD = "  requires(true) ensures(true) effects(pure)\n"

#: One program per per-site emitter, and the line its check must be
#: located on.  Keyed by the TRAP_EMITTERS key, so a registry row without a
#: fixture — or a fixture for a row that no longer exists — is a failure of
#: `test_every_per_site_emitter_has_a_fixture`, not a silent gap.
FIXTURES: dict[str, tuple[str, int]] = {
    "wasm/operators.py:_emit_overflow_guard": (
        "public fn f(@Int, @Int -> @Int)\n" + _HEAD
        + "{\n  @Int.1 + @Int.0\n}\n", 4),
    "wasm/operators.py:_emit_nat_sub_guard": (
        "public fn f(@Nat, @Nat -> @Nat)\n" + _HEAD
        + "{\n  @Nat.1 - @Nat.0\n}\n", 4),
    "wasm/operators.py:_translate_binary": (
        "public fn f(@Int, @Int -> @Int)\n" + _HEAD
        + "{\n  @Int.1 / @Int.0\n}\n", 4),
    "wasm/operators.py:_note_quotient_overflow": (
        "public fn f(@Int, @Int -> @Int)\n" + _HEAD
        + "{\n  @Int.1 / @Int.0\n}\n", 4),
    "wasm/operators.py:_emit_nat_bind_guard": (
        "public fn f(@Int -> @Nat)\n" + _HEAD
        + "{\n  let @Nat = @Int.0;\n  @Nat.0\n}\n", 4),
    "wasm/operators.py:_emit_int_widen_guard": (
        "public fn f(@Nat -> @Int)\n" + _HEAD + "{\n  @Nat.0\n}\n", 4),
    "wasm/operators.py:_translate_assert": (
        "public fn f(@Int -> @Int)\n" + _HEAD
        + "{\n  assert(@Int.0 > 0);\n  @Int.0\n}\n", 4),
    "wasm/data.py:_translate_index_expr": (
        "public fn f(@Int -> @Int)\n" + _HEAD
        + "{\n  let @Array<Int> = [1, 2, 3];\n  @Array<Int>.0[@Int.0]\n}\n",
        5),
    "wasm/calls_strings.py:_translate_char_code": (
        "public fn f(@Int -> @Nat)\n" + _HEAD
        + '{\n  string_char_code("abc", @Int.0)\n}\n', 4),
    "wasm/calls_math.py:_translate_float_to_int": (
        "public fn f(@Float64 -> @Int)\n" + _HEAD
        + "{\n  float_to_int(@Float64.0)\n}\n", 4),
    "wasm/calls_math.py:_translate_floor": (
        "public fn f(@Float64 -> @Int)\n" + _HEAD
        + "{\n  floor(@Float64.0)\n}\n", 4),
    "wasm/calls_math.py:_translate_ceil": (
        "public fn f(@Float64 -> @Int)\n" + _HEAD
        + "{\n  ceil(@Float64.0)\n}\n", 4),
    "wasm/calls_math.py:_translate_round": (
        "public fn f(@Float64 -> @Int)\n" + _HEAD
        + "{\n  round(@Float64.0)\n}\n", 4),
    "codegen/contracts.py:_compile_preconditions": (
        "public fn f(@Int -> @Int)\n"
        "  requires(@Int.0 > 0) ensures(true) effects(pure)\n"
        "{\n  @Int.0\n}\n", 2),
    "codegen/contracts.py:_compile_postconditions": (
        "public fn f(@Int -> @Int)\n"
        "  requires(true) ensures(@Int.result == @Int.0) effects(pure)\n"
        "{\n  @Int.0\n}\n", 2),
    "codegen/contracts.py:_emit_refinement_check": (
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "public fn f(@Pos -> @Int)\n" + _HEAD + "{\n  @Pos.0\n}\n", 2),
    "codegen/contracts.py:_compile_decreases_entry": (
        "public fn f(@Nat -> @Nat)\n"
        "  requires(true) ensures(true) decreases(@Nat.0) effects(pure)\n"
        "{\n  if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }\n}\n", 2),
    "codegen/contracts.py:_dec_self_tail_prefix": (
        "public fn f(@Nat, @Nat -> @Nat)\n"
        "  requires(true) ensures(true) decreases(@Nat.1) effects(pure)\n"
        "{\n  if @Nat.1 == 0 then { @Nat.0 } else "
        "{ f(@Nat.1 - 1, @Nat.0 + 1) }\n}\n", 2),
    "codegen/contracts.py:_dec_bound_check_pairs": (
        "public fn f(@Nat -> @Nat)\n"
        "  requires(true) ensures(true) decreases(@Nat.0) effects(pure)\n"
        "{\n  if @Nat.0 == 0 then { 0 } else { f(@Nat.0 - 1) }\n}\n", 2),
}


def test_every_per_site_emitter_has_a_fixture() -> None:
    """The fixture table and the registry name the same emitters."""
    per_site = {key for key, row in TRAP_EMITTERS.items() if row.per_site}
    assert set(FIXTURES) == per_site, (
        f"registry rows with no fixture: {sorted(per_site - set(FIXTURES))}; "
        f"fixtures for no registry row: {sorted(set(FIXTURES) - per_site)}"
    )


@pytest.mark.parametrize("emitter", sorted(FIXTURES))
def test_a_fixture_records_its_emitter(emitter: str) -> None:
    """Compiling the emitter's fixture lists its check, at its line, with
    the kind and obligations its registry row states."""
    source, line = FIXTURES[emitter]
    result = _compile(source)
    found = _by_emitter(result, emitter)
    assert found, (
        f"{emitter} emitted nothing the record lists; record: "
        f"{[(c.emitter, c.line) for c in result.emitted_checks]}"
    )
    row = TRAP_EMITTERS[emitter]
    for check in found:
        assert check.kind == row.kind
        assert check.obligations == row.obligations
        assert check.function == "f"
        assert check.line == line, (check.line, check.column)
        assert check.column > 0
        assert check.file == "prog.vera"
        assert check.prelude is False


def test_every_kind_a_row_names_exists() -> None:
    """A registry row's kind is a kind a host can report."""
    for key, row in TRAP_EMITTERS.items():
        assert row.kind in TRAP_KINDS, key


def test_the_record_serialises_to_json() -> None:
    source, _ = FIXTURES["wasm/operators.py:_translate_assert"]
    result = _compile(source)
    payload = json.loads(json.dumps(
        [c.to_dict() for c in result.emitted_checks]))
    assert payload and payload[0]["kind"] == "assertion_failed"
    assert payload[0]["obligations"] == ["assert"]


# ---------------------------------------------------------------------------
# Where a check sits: the per-scope seams
# ---------------------------------------------------------------------------

def test_a_check_in_a_closure_body_is_recorded_under_the_closure() -> None:
    """The closure's own context merges its record at the lift seam, under
    the lifted function's name."""
    result = _compile(
        "public fn f(@Int -> @Int)\n" + _HEAD
        + "{\n  let @Array<Int> = array_map([1, 2], fn(@Int -> @Int)"
        " effects(pure) { @Int.0 / 1 });\n  @Array<Int>.0[0]\n}\n")
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    assert [c.function for c in div] == ["anon_0"], div
    assert div[0].line == 4


def test_a_check_in_a_where_helper_is_recorded_under_the_helper() -> None:
    result = _compile(
        "public fn f(@Int -> @Int)\n" + _HEAD
        + "{\n  half(@Int.0)\n}\nwhere {\n"
        "  fn half(@Int -> @Int)\n" + _HEAD
        + "  {\n    @Int.0 / 2\n  }\n}\n")
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    # A `where` helper is emitted under its owner-qualified symbol.
    assert [c.function for c in div] == ["f$where$half"], div
    assert div[0].line == 10


def test_a_check_in_a_postcondition_is_recorded() -> None:
    """A check lowered while compiling an `ensures(...)` sits in the
    function body like any other; the merge runs after the postcondition
    phase, so it is not lost."""
    result = _compile(
        "public fn f(@Int -> @Int)\n"
        "  requires(true) ensures(@Int.result / 1 == @Int.0) effects(pure)\n"
        "{\n  @Int.0\n}\n")
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    assert [(c.function, c.line) for c in div] == [("f", 2)], div


def test_a_self_tail_check_is_recorded_once_per_splice() -> None:
    """The self-tail `decreases` prefix is built once and spliced at every
    self-recursive `return_call`; two tail sites are two checks."""
    result = _compile(
        "public fn f(@Nat, @Nat -> @Nat)\n"
        "  requires(true) ensures(true) decreases(@Nat.1) effects(pure)\n"
        "{\n  if @Nat.1 == 0 then { @Nat.0 } else {\n"
        "    if @Nat.0 == 7 then { f(@Nat.1 - 1, 0) } "
        "else { f(@Nat.1 - 1, 7) }\n  }\n}\n")
    tail = _by_emitter(result, "codegen/contracts.py:_dec_self_tail_prefix")
    body = wat_fn_body(result.wat, "f")
    assert len(tail) == body.count("return_call $f") == 2, (
        len(tail), body.count("return_call $f"))


# ---------------------------------------------------------------------------
# What is NOT listed
# ---------------------------------------------------------------------------

_SKIPPED_HELPER = (
    "private fn tally(-> @Int) requires(true) ensures(true) effects(pure) {\n"
    '  let @Map<String, Array<Int>> = map_insert(map_new(), "a", [1, 2]);\n'
    "  map_size(@Map<String, Array<Int>>.0)\n}\n"
)


def test_a_dropped_function_takes_its_checks_with_it() -> None:
    """`g` compiles — emitting its division check — and is then dropped as
    a caller of a skipped function ([E620]); its check is not the module's.
    The surviving sibling's is."""
    source = _SKIPPED_HELPER + (
        "public fn g(@Int -> @Int)\n" + _HEAD
        + "{\n  tally() / @Int.0\n}\n"
        "public fn h(@Int -> @Int)\n" + _HEAD + "{\n  10 / @Int.0\n}\n")
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source, file="d.vera")
    result = codegen_compile(
        program, source=source, file="d.vera",
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    assert "g" not in result.exports and "h" in result.exports
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    assert [c.function for c in div] == ["h"], div


def test_a_byte_operand_is_recorded_once() -> None:
    """A Byte comparison lowers its operands twice — once generally, then
    again at i32 — and emits only the second; the index check inside the
    operand must be listed once, not once per translation."""
    result = _compile(
        "public fn f(@Array<Byte>, @Byte -> @Bool)\n"
        "  requires(array_length(@Array<Byte>.0) > 0) ensures(true) "
        "effects(pure)\n"
        "{\n  @Array<Byte>.0[0] < @Byte.0\n}\n")
    index = _by_emitter(result, "wasm/data.py:_translate_index_expr")
    assert len(index) == 1, index


# ---------------------------------------------------------------------------
# Clones and imports
# ---------------------------------------------------------------------------

def test_a_generic_contributes_one_entry_per_clone() -> None:
    result = _compile(
        "private forall<T> fn pick(@T, @Int -> @T)\n" + _HEAD
        + "{\n  let @Int = 10 / @Int.0;\n  @T.0\n}\n"
        "public fn f(@Int -> @Int)\n" + _HEAD
        + "{\n  let @Bool = pick(true, @Int.0);\n  pick(1, @Int.0)\n}\n")
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    clones = sorted(c.function for c in div)
    assert len(clones) == 2 and all(n.startswith("pick$") for n in clones), (
        clones)
    assert {c.line for c in div} == {4}


def test_an_imported_body_names_its_own_file(tmp_path: Path) -> None:
    files = {
        "lib.vera": (
            "module lib;\n"
            "public fn quot(@Int -> @Int)\n" + _HEAD
            + "{\n  100 / @Int.0\n}\n"),
        "main.vera": (
            "import lib(quot);\n"
            "public fn main(-> @Int)\n" + _HEAD + "{\n  quot(5)\n}\n"),
    }
    _verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, cg_errors
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    assert div, [c.emitter for c in result.emitted_checks]
    assert all(Path(c.file or "").name == "lib.vera" for c in div), div
    assert {c.line for c in div} == {5}


def test_the_record_matches_the_signals_in_the_module() -> None:
    """Per function, the record's contract / narrowing / widening entries
    number exactly the module's calls to those signals — one call per
    check, so a phantom entry or a missed one shows as a count mismatch."""
    result = _compile(
        "type Pos = { @Int | @Int.0 > 0 };\n"
        "public fn f(@Pos, @Int, @Nat -> @Int)\n"
        "  requires(@Int.0 != 3) ensures(@Int.result != 4) effects(pure)\n"
        "{\n  let @Nat = @Int.0;\n  let @Int = @Nat.1;\n  @Int.0\n}\n")
    body = wat_fn_body(result.wat, "f")
    recorded = Counter(c.kind for c in result.emitted_checks
                       if c.function == "f")
    for kind in ("contract_violation", "nat_guard", "widen_guard"):
        emitted = len(signal_call_pattern(kind).findall(body))
        assert recorded[kind] == emitted > 0, (kind, recorded[kind], emitted)


def _record_mismatches(
    result: CompileResult, function: str,
) -> dict[str, tuple[int, int]]:
    """``kind -> (recorded, emitted)`` for every signalled kind on which the
    record and *function*'s body in the module disagree.  A native check (a
    division's `overflow` condition among them) has no signal to count, so
    only signalling entries are compared."""
    body = wat_fn_body(result.wat, function)
    recorded = Counter(
        c.kind for c in result.emitted_checks
        if c.function == function
        and not TRAP_EMITTERS[c.emitter].via.startswith("native:"))
    out: dict[str, tuple[int, int]] = {}
    for kind, row in TRAP_KINDS.items():
        if not row.code and kind != "contract_violation":
            continue
        emitted = len(signal_call_pattern(kind).findall(body))
        if recorded[kind] != emitted:
            out[kind] = (recorded[kind], emitted)
    return out


#: An arithmetic measure: the self-tail prefix evaluates it, so every copy
#: of the prefix carries the measure's own overflow guard.  `down` splices
#: the prefix at two tail sites; `nontail` builds it and splices it nowhere.
_ARITHMETIC_MEASURE = """\
public fn down(@Int, @Int -> @Int)
  requires(@Int.1 >= @Int.0)
  ensures(true)
  decreases(@Int.1 - @Int.0)
  effects(pure)
{
  if @Int.1 == @Int.0 then {
    0
  } else {
    if @Int.1 - @Int.0 > 5 then {
      down(@Int.1 - 2, @Int.0)
    } else {
      down(@Int.1 - 1, @Int.0)
    }
  }
}

public fn nontail(@Int, @Int -> @Int)
  requires(@Int.1 >= @Int.0)
  ensures(true)
  decreases(@Int.1 - @Int.0)
  effects(pure)
{
  if @Int.1 == @Int.0 then {
    0
  } else {
    1 + nontail(@Int.1 - 1, @Int.0)
  }
}
"""


@pytest.mark.parametrize(("function", "splices"), [("down", 2), ("nontail", 0)])
def test_the_self_tail_prefix_records_its_measure_per_splice(
    function: str, splices: int,
) -> None:
    """Every check the prefix's lowering emits — here the measure's own
    overflow guard — is in the module once per splice, and so in the
    record: twice for two tail sites, not at all for recursion the prefix
    never reaches."""
    result = _compile(_ARITHMETIC_MEASURE)
    body = wat_fn_body(result.wat, function)
    assert body.count(f"return_call ${function}") == splices, body
    assert not _record_mismatches(result, function)


#: `f`'s refined formal lifts a closure whose own refinement leads back to
#: itself, so its worklist fails after one lift (E602) and hands its closure
#: id back; `main`'s closure is then emitted under that same id.
_RECYCLED_CLOSURE_ID = """\
type SelfRef = { @Int | @Int.0 > 0 && apply_fn(fn(@SelfRef -> @Int)
  effects(pure) { @SelfRef.0 }, 3) > 0 };

private fn f(@SelfRef -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @SelfRef.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  apply_fn(fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }, 41)
}
"""


def test_a_failed_closure_worklist_takes_its_records_with_it() -> None:
    """The closure the failed worklist did lift recorded its refinement
    check; its id is reused by `main`'s closure, so a record that kept the
    entry would credit `$anon_0` with a check its body does not hold."""
    result = _compile(_RECYCLED_CLOSURE_ID)
    assert "E602" in {d.error_code for d in result.diagnostics}
    assert "(func $anon_0 " in result.wat
    assert not _record_mismatches(result, "anon_0")
    assert {c.kind for c in result.emitted_checks
            if c.function == "anon_0"} == {"overflow"}


#: A measure whose first component lowers (with its own overflow guard)
#: and whose second, a parameterised ADT, cannot be ranked: the whole
#: translation is abandoned, at the function's entry and at its self-tail
#: site, and the guard lowered for the first component is in neither.
_ABANDONED_MEASURE = """\
private data Seq<T> {
  Empty,
  More(T, Seq<T>)
}

public fn walk(@Int, @Seq<Int> -> @Int)
  requires(@Int.0 >= 0)
  ensures(true)
  decreases(@Int.0 + 1, @Seq<Int>.0)
  effects(pure)
{
  match @Seq<Int>.0 {
    Empty -> @Int.0,
    More(@Int, @Seq<Int>) -> walk(@Int.1, @Seq<Int>.0)
  }
}
"""


def test_an_abandoned_measure_translation_leaves_no_record() -> None:
    result = _compile(_ABANDONED_MEASURE)
    assert not _record_mismatches(result, "walk")
    assert "overflow" not in {c.kind for c in result.emitted_checks
                              if c.function == "walk"}


def test_no_record_marker_reaches_the_module_text() -> None:
    """The record is read back from the assembled text through markers on
    the checks' instructions, and the markers are taken out after: the WAT a
    caller sees is the WAT without them."""
    result = _compile(_ARITHMETIC_MEASURE)
    assert result.emitted_checks
    assert not CHECK_MARKER_RE.search(result.wat), result.wat[:400]


#: A program whose own text spells markers: a string it prints, and one inside
#: an assertion, whose trap message quotes it — both land in data segments.
_SPELLS_MARKERS = """\
private fn half(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{
  assert(string_length(" (;vera-check:1;)") == 17);
  @Int.0 / 2
}

public fn main(-> @Int)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(" (;vera-check:2;) (;vera-check:999999999;)");
  half(8)
}
"""


def test_a_program_string_that_spells_a_marker_is_left_alone() -> None:
    """Marker text inside a string literal is the program's, not a marker: it
    compiles, prints byte for byte, and the record lists the real checks."""
    result = _compile(_SPELLS_MARKERS)
    run = execute(result, fn_name="main")
    assert run.value == 4
    assert run.stdout == " (;vera-check:2;) (;vera-check:999999999;)"
    assert not _record_mismatches(result, "half")
    assert sorted(c.kind for c in result.emitted_checks
                  if c.function == "half") == [
        "assertion_failed", "divide_by_zero"]


def _marked(body: str) -> str:
    return f"(module\n  (func $f\n{body}\n  )\n)\n"


def test_a_marker_naming_no_entry_is_an_invariant_error() -> None:
    generator = CodeGenerator(source="", file="x.vera")
    with pytest.raises(CodegenInvariantError, match="names no entry"):
        generator._assemble_emitted_checks(
            _marked("    i64.div_s (;vera-check:424242;)"))


def test_a_marker_outside_every_function_is_an_invariant_error() -> None:
    generator = CodeGenerator(source="", file="x.vera")
    generator._emitted_checks[424243] = (
        "wasm/operators.py:_translate_binary", None)
    with pytest.raises(CodegenInvariantError, match="outside every function"):
        generator._assemble_emitted_checks(
            "(module\n  (global $g i32 (i32.const 0)) (;vera-check:424243;)\n"
            + _marked("    nop")[len("(module\n"):])


@pytest.mark.parametrize(("body", "params", "kinds"), [
    ("@Int.1 / @Int.0", "@Int, @Int", ["divide_by_zero", "overflow"]),
    ("@Int.0 / (0 - 1)", "@Int", ["divide_by_zero", "overflow"]),
    ("@Int.0 / 5", "@Int", ["divide_by_zero"]),
    ("@Int.1 % @Int.0", "@Int, @Int", ["divide_by_zero"]),
    ("@Nat.1 / @Nat.0", "@Nat, @Nat", ["divide_by_zero", "overflow"]),
    ("@Nat.0 / 18446744073709551615", "@Nat",
     ["divide_by_zero", "overflow"]),
    ("@Nat.0 / 7", "@Nat", ["divide_by_zero"]),
], ids=["int-by-int", "by-a-computed-minus-one", "by-five", "remainder",
        "nat-by-nat", "nat-by-the-bits-of-minus-one", "nat-by-seven"])
def test_a_division_lists_its_overflow_condition_where_it_can_occur(
    body: str, params: str, kinds: list[str],
) -> None:
    """`i64.div_s` traps on a zero divisor and on `INT_MIN / -1`: a division
    lowered to it whose divisor can hold -1's bits is two checks on one
    instruction.  A `@Nat` division is `i64.div_s` today and meets the pair
    at 2^63 / (2^64 - 1) (#1504); a remainder cannot overflow, and a literal
    divisor whose bits are not -1's cannot meet it."""
    result = _compile(
        f"public fn f({params} -> @Int)\n" + _HEAD + "{\n  " + body + "\n}\n")
    division = {"wasm/operators.py:_translate_binary",
                "wasm/operators.py:_note_quotient_overflow"}
    assert sorted(c.kind for c in result.emitted_checks
                  if c.function == "f" and c.emitter in division) == kinds


def test_a_stubbed_closure_takes_its_checks_with_it() -> None:
    """A closure calling a skipped function is kept as a one-instruction
    `unreachable` stub (its table slot must survive), so the division its
    body was compiled with is not in the module and must not be listed."""
    source = _SKIPPED_HELPER + (
        "public fn g(@Int -> @Int)\n" + _HEAD
        + "{\n  let @Array<Int> = array_map([1, 2], fn(@Int -> @Int)"
        " effects(pure) { tally() / @Int.0 });\n  @Array<Int>.0[0]\n}\n"
        "public fn h(@Int -> @Int)\n" + _HEAD + "{\n  10 / @Int.0\n}\n")
    program = parse_to_ast(source)
    _diags, arts = typecheck_with_artifacts(program, source, file="d.vera")
    result = codegen_compile(
        program, source=source, file="d.vera",
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )
    assert "(func $anon_0 unreachable)" in result.wat, (
        "the fixture no longer produces a stubbed closure")
    div = _by_emitter(result, "wasm/operators.py:_translate_binary")
    assert [c.function for c in div] == ["h"], div
