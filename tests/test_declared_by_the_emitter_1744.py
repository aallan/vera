"""A module declares the `State` cells and `Exn` tags its emitted code
uses, and a handler's block declares the result its arms leave (#1744).

Code generation's compilability pre-scans (`vera/codegen/compilability.py`)
registered each `State<T>` cell and `Exn<E>` tag from the program's text: a
handler the walk met, an effect row the function declares.  So a declaration
and the code that uses it were decided by two rules, and three members of
the class were measured:

* a cell or tag declared for a function code generation drops (E602): with
  a `handle[State<Int>]` or an `effects(<State<Int>>)` row in it, the module
  declares `state_get_Int`, `state_put_Int`, `state_push_Int` and
  `state_pop_Int`, nothing calls them, and `--target wasi-p2` refuses the
  module (`state (Int)`);
* an `Exn` handler whose handled body and `throw` clause each hold a `State`
  handler compiles to a module that does not load: the handler's block took
  its result from code generation's own reading of the two arms, which has
  no answer for a block that ends in a handler, so the block declared no
  result while both arms leave a value (`values remaining on stack at end of
  block`);
* `_scan_io_ops`, whose walk registered no host import since #1717 and
  reached only what the handler walk reaches.

Each emitter that calls a cell or uses a tag records it on its function's
context, and the record joins the module's at the per-function and the
closure merge, as the host imports' records do (#735): a function code
generation drops (E602) declares nothing.  An `Exn` handler's block
declares the result the checker typed its arms at: the handler's type, or
its `throw` clause's where the handled body always throws.

The matrix crosses the handler's shape (a `State` handler, an `Exn` handler,
each nested in the other's body, and an `Exn` handler with a `State`
handler in its body and in its `throw` clause) with its position (the
function's body, an `if` arm, a `match` arm, a closure's body, a `let`'s
value and a statement whose value is dropped) and the function kept or
dropped (a `map_insert` ahead of it, which the `skip_map_inserts` injection
makes code generation refuse: E602).  Each cell asserts that the module
declares exactly
the cells and tags its code uses, the kept function's being its handlers'
(the premise), that `vera run` runs `main` and the kept function to its
value, and that `--target wasi-p2` builds the module exactly when it
declares no cell, refusing it naming the cell otherwise.  `vera run` and
the WASI build run in process, through `tests/pipeline.py`'s `cli`: a
module that does not load is an exit status there.

Not a cell: a function dropped after it compiled, as a caller of a dropped
function (E620), keeps its record in the module (#1795), pinned by one
strict `xfail`.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

from tests import pipeline
from tests.codegen_helpers import skip_map_inserts  # noqa: F401  (the fixture)

pytestmark = pytest.mark.matrix(decides=[
    "vera/codegen/compilability.py",
    "vera/codegen/functions.py",
    "vera/codegen/closures.py",
    "vera/codegen/contracts.py",
    "vera/wasm/context.py",
    "vera/wasm/calls.py",
    "vera/wasm/calls_handlers.py",
    "vera/wasm/operators.py",
    "vera/wasm/inference.py",
])

_STATE_DECL = re.compile(r'\(import "vera" "state_(?:get|put|push|pop)_([^"]+)"')
_STATE_CALL = re.compile(r"call \$vera\.state_(?:get|put|push|pop)_([^\s)]+)")
_TAG_DECL = re.compile(r"\(tag \$exn_([^\s)]+)")
_TAG_USE = re.compile(r"(?:catch|throw) \$exn_([^\s)]+)")


def _cells(wat: str) -> tuple[set[str], set[str]]:
    """The cells *wat* declares, and the cells its code calls."""
    return set(_STATE_DECL.findall(wat)), set(_STATE_CALL.findall(wat))


def _tags(wat: str) -> tuple[set[str], set[str]]:
    """The tags *wat* declares, and the tags its code throws or catches."""
    return set(_TAG_DECL.findall(wat)), set(_TAG_USE.findall(wat))


def _write(tmp_path: Path, source: str) -> Path:
    path = tmp_path / "program.vera"
    path.write_text(source, encoding="utf-8")
    return path


def _fn(name: str, formals: str, ret: str, effect: str, body: str,
        visibility: str = "public") -> str:
    indented = "\n".join(f"  {line}" if line else line
                         for line in body.splitlines())
    return (f"{visibility} fn {name}({formals} -> @{ret})\n"
            "  requires(true)\n  ensures(true)\n"
            f"  effects({effect})\n{{\n{indented}\n}}\n")


_MAIN = _fn("main", "", "Unit", "<IO>", 'IO.print("ok\\n")')

#: A statement code generation refuses (E602) under the `skip_map_inserts`
#: injection, so the function holding it is dropped before the code after it
#: is emitted: no shape the check accepts is dropped at E602 (the one
#: check-green drop left, #1783's, is a caller's E620).  It uses no cell and
#: no tag.
_DROPPER = 'let @Map<String, Int> = map_insert(map_new(), "a", 1);'


def _state(init: str, body: str) -> str:
    """A `State<Int>` handler starting at *init*, around *body*."""
    inner = "\n".join(f"  {line}" for line in body.splitlines())
    return (f"handle[State<Int>](@Int = {init}) {{\n"
            "  get(@Unit) -> { resume(@Int.0) },\n"
            "  put(@Int) -> { resume(()) }\n"
            f"}} in {{\n{inner}\n}}")


def _exn(clause: str, body: str) -> str:
    """An `Exn<Int>` handler whose `throw` clause is *clause*, around
    *body*."""
    cl = "\n".join(f"    {line}" for line in clause.splitlines())
    inner = "\n".join(f"  {line}" for line in body.splitlines())
    return (f"handle[Exn<Int>] {{\n  throw(@Int) -> {{\n{cl}\n  }}\n"
            f"}} in {{\n{inner}\n}}")


#: Each shape: the handler, written over the function's `@Int` input, its
#: value at the input 7 by the language's rules, and the cells and tags it
#: uses.
_SHAPES: dict[str, tuple[str, int, set[str], set[str]]] = {
    # 7 is stored, 8 put and read.
    "state": (_state("@Int.0", "put(get(()) + 1);\nget(())"), 8, {"Int"}, set()),
    # 7 is thrown, the clause adds 1.
    "exn": (_exn("@Int.0 + 1",
                 "if @Int.0 > 0 then { throw(@Int.0) } else { 0 }"),
            8, set(), {"Int"}),
    # The cell reaches 8, which is thrown; the clause adds 2.
    "state_in_exn": (_exn("@Int.0 + 2", _state(
        "@Int.0",
        "put(get(()) + 1);\nif get(()) > 5 then { throw(get(())) } else { get(()) }")),
        10, {"Int"}, {"Int"}),
    # The cell reaches 8; 1 is thrown, and the clause adds the cell to it.
    # The handled body always throws, so the handler's value is the
    # clause's.
    "exn_in_state": (_state("@Int.0", "put(get(()) + 1);\n" + _exn(
        "@Int.0 + get(())", "throw(1)")), 9, {"Int"}, {"Int"}),
    # The body's cell reaches 8, which is thrown; the clause's cell starts
    # at it and reaches 18.  The member of #1744 that did not load.
    "state_in_both": (_exn(
        _state("@Int.0", "put(get(()) + 10);\nget(())"),
        _state("@Int.0",
               "put(get(()) + 1);\n"
               "if get(()) > 5 then { throw(get(())) } else { get(()) }")),
        18, {"Int"}, {"Int"}),
}


def _positioned(position: str, handler: str) -> str:
    """The function body holding *handler* at *position*."""
    h = "\n".join(f"  {line}" for line in handler.splitlines())
    if position == "body":
        return handler
    if position == "if_arm":
        return f"if @Int.0 > 5 then {{\n{h}\n}} else {{\n  0\n}}"
    if position == "match_arm":
        hh = "\n".join(f"  {line}" for line in h.splitlines())
        return (f"match Some(@Int.0) {{\n  Some(@Int) -> {{\n{hh}\n  }},\n"
                "  None -> 0\n}")
    if position == "closure":
        return f"apply_fn(fn(@Int -> @Int) effects(pure) {{\n{h}\n}}, @Int.0)"
    if position == "let_value":
        return f"let @Int = {handler};\n@Int.0"
    assert position == "statement", position
    return f"{handler};\n@Int.0"


#: Where the handler stands, and what the function returns there, given the
#: handler's value: its value, but for a statement, whose value is dropped
#: and after which the function returns its input.
_POSITIONS: dict[str, object] = {
    "body": None, "if_arm": None, "match_arm": None, "closure": None,
    "let_value": None, "statement": 7,
}


def _program(shape: str, position: str, dropped: bool) -> str:
    body = _positioned(position, _SHAPES[shape][0])
    if dropped:
        body = f"{_DROPPER}\n{body}"
    return _fn("f", "@Int", "Int", "pure", body) + "\n" + _MAIN


def _wasi(tmp_path: Path, path: Path) -> pipeline.CliResult:
    return pipeline.cli("compile", "--target", "wasi-p2", path,
                        "-o", tmp_path / "program.wasm")


@pytest.mark.parametrize("dropped", [False, True], ids=["kept", "dropped"])
@pytest.mark.parametrize("position", list(_POSITIONS))
@pytest.mark.parametrize("shape", list(_SHAPES))
def test_the_module_declares_what_its_code_uses(
        shape: str, position: str, dropped: bool, tmp_path: Path,
        request: pytest.FixtureRequest) -> None:
    """The module declares the cells and tags its code calls, `vera run`
    runs it, and the WASI target builds it exactly when it declares no
    cell."""
    if dropped:
        request.getfixturevalue("skip_map_inserts")
    source = _program(shape, position, dropped)
    compiled = pipeline.compile(source)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert ("E602" in {d.error_code for d in compiled.warnings}) is dropped
    assert ("f" in compiled.exports) is not dropped
    _, value, cells, tags = _SHAPES[shape]
    declared, called = _cells(compiled.wat)
    assert declared == called, (declared, called)
    assert declared == (set() if dropped else cells)
    declared_tags, used_tags = _tags(compiled.wat)
    assert declared_tags == used_tags, (declared_tags, used_tags)
    assert declared_tags == (set() if dropped else tags)
    path = _write(tmp_path, source)
    ran = pipeline.cli("run", path)
    assert (ran.returncode, ran.stdout) == (0, "ok\n"), ran.stderr
    if not dropped:
        returned = _POSITIONS[position]
        ran_f = pipeline.cli("run", path, "--fn", "f", "--", "7")
        assert (ran_f.returncode, ran_f.stdout.strip()) == (
            0, str(value if returned is None else returned)), ran_f.stderr
    wasi = _wasi(tmp_path, path)
    if declared:
        assert wasi.returncode == 1, wasi.stdout
        assert "state (Int)" in wasi.stderr, wasi.stderr
    else:
        assert wasi.returncode == 0, wasi.stderr


# ---------------------------------------------------------------------
# The reported members
# ---------------------------------------------------------------------


_DEAD_HANDLER = _fn("dead", "@Int", "Int", "pure", f"""\
{_DROPPER}
{_state("3", "get(())")}""") + "\n" + _MAIN

_DEAD_ROW = _fn("dead", "@Int", "Int", "<State<Int>>", f"""\
{_DROPPER}
get(())""") + "\n" + _MAIN


@pytest.mark.usefixtures("skip_map_inserts")
def test_repro_a_dropped_handler_declares_no_cell(tmp_path: Path) -> None:
    """The issue's first member, in a handler: a function code generation
    drops (E602) with a `handle[State<Int>]` in it declares no cell, and
    the WASI target builds the module and runs it."""
    compiled = pipeline.compile(_DEAD_HANDLER)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert "E602" in {d.error_code for d in compiled.warnings}
    assert compiled.exports == ["main"]
    assert _cells(compiled.wat) == (set(), set())
    assert compiled.result.state_types == []
    path = _write(tmp_path, _DEAD_HANDLER)
    assert _wasi(tmp_path, path).returncode == 0
    ran = pipeline.cli("run", "--target", "wasi-p2", path)
    assert (ran.returncode, ran.stdout) == (0, "ok\n"), ran.stderr


@pytest.mark.usefixtures("skip_map_inserts")
def test_repro_a_dropped_state_row_declares_no_cell(tmp_path: Path) -> None:
    """The issue's first member, in a row: the same function declaring
    `effects(<State<Int>>)` and calling `get(())`."""
    compiled = pipeline.compile(_DEAD_ROW)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert "E602" in {d.error_code for d in compiled.warnings}
    assert compiled.exports == ["main"]
    assert _cells(compiled.wat) == (set(), set())
    assert compiled.result.state_types == []
    path = _write(tmp_path, _DEAD_ROW)
    assert _wasi(tmp_path, path).returncode == 0
    ran = pipeline.cli("run", "--target", "wasi-p2", path)
    assert (ran.returncode, ran.stdout) == (0, "ok\n"), ran.stderr


_DEAD_EXN = _fn("dead", "@Int", "Int", "pure", f"""\
{_DROPPER}
{_exn("@Int.0 + 1", "throw(@Int.0)")}""") + "\n" + _MAIN


@pytest.mark.usefixtures("skip_map_inserts")
def test_repro_a_dropped_exn_handler_declares_no_tag(tmp_path: Path) -> None:
    """The first member's `Exn` twin: a function code generation drops
    (E602) with a `handle[Exn<Int>]` in it declares no tag."""
    compiled = pipeline.compile(_DEAD_EXN)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert "E602" in {d.error_code for d in compiled.warnings}
    assert compiled.exports == ["main"]
    assert _tags(compiled.wat) == (set(), set())
    ran = pipeline.cli("run", _write(tmp_path, _DEAD_EXN))
    assert (ran.returncode, ran.stdout) == (0, "ok\n"), ran.stderr


_BOTH_ARMS = _fn("main", "@Unit", "Int", "pure", _exn(
    _state("1", "get(())"), _state("3", "get(())")))


def test_repro_an_exn_handler_with_state_handlers_in_both_arms_loads() -> None:
    """The issue's second member, as filed: the handled body's cell is read
    at 3, and nothing throws."""
    ran = pipeline.cli("run", "-", stdin=_BOTH_ARMS)
    assert (ran.returncode, ran.stdout.strip()) == (0, "3"), ran.stderr


def test_repro_the_io_pre_scan_is_gone() -> None:
    """The issue's third member: `_scan_io_ops` is deleted, and of the
    compilability checks only the two declarations touch the module's cells
    and tags, which the per-function and closure merges call with what the
    emitted code used."""
    import ast as pyast

    from vera.codegen import compilability

    assert not hasattr(compilability.CompilabilityMixin, "_scan_io_ops")
    tree = pyast.parse(Path(compilability.__file__).read_text(encoding="utf-8"))
    touching = {
        node.name for node in pyast.walk(tree)
        if isinstance(node, pyast.FunctionDef)
        and any(isinstance(sub, pyast.Attribute)
                and sub.attr in ("_state_types", "_exn_types")
                for sub in pyast.walk(node))}
    assert touching == {"_declare_state_cell", "_declare_exn_tag"}, touching


# ---------------------------------------------------------------------
# Each emitter's record, alone
# ---------------------------------------------------------------------


_OLD_ONLY = """\
public fn keep(@Int -> @Int)
  requires(true)
  ensures(@Int.result == @Int.0 || old(State<Int>) > @Int.0)
  effects(<State<Int>>)
{
  @Int.0
}
"""

_NEW_ONLY = _OLD_ONLY.replace("old(State<Int>)", "new(State<Int>)")


def test_an_old_snapshot_alone_declares_its_cell(tmp_path: Path) -> None:
    """A cell whose one use is a postcondition's `old` snapshot is declared
    by the snapshot, at its width."""
    compiled = pipeline.compile(_OLD_ONLY)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _cells(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _OLD_ONLY), "--fn", "keep", "--", "3")
    assert (ran.returncode, ran.stdout.strip()) == (0, "3"), ran.stderr


def test_a_new_read_alone_declares_its_cell(tmp_path: Path) -> None:
    """A cell whose one use is a postcondition's `new` read is declared by
    the read."""
    compiled = pipeline.compile(_NEW_ONLY)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _cells(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _NEW_ONLY), "--fn", "keep", "--", "3")
    assert (ran.returncode, ran.stdout.strip()) == (0, "3"), ran.stderr


_BOUNDARY_ONLY = _fn("quiet", "@Int", "Int", "<Exn<Int>>", "@Int.0 + 1")

_THROW_ONLY = _fn("raise", "@Int", "Int", "<Exn<Int>>", "throw(@Int.0)",
                  visibility="private") + "\n" + _MAIN


def test_an_entry_point_s_exn_boundary_alone_declares_its_tag(
        tmp_path: Path) -> None:
    """An exported function whose row declares `Exn<Int>` and which throws
    nothing: the export's boundary catches the tag (#1479), and is its one
    use."""
    compiled = pipeline.compile(_BOUNDARY_ONLY)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _tags(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _BOUNDARY_ONLY),
                       "--fn", "quiet", "--", "4")
    assert (ran.returncode, ran.stdout.strip()) == (0, "5"), ran.stderr


def test_a_throw_alone_declares_its_tag(tmp_path: Path) -> None:
    """A `throw` in a function nothing calls is the tag's one use."""
    compiled = pipeline.compile(_THROW_ONLY)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _tags(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _THROW_ONLY))
    assert (ran.returncode, ran.stdout) == (0, "ok\n"), ran.stderr


_ROW_BARE = _fn("keep", "@Int", "Int", "<State<Int>>", "put(@Int.0);\nget(())")

_ROW_QUALIFIED = _fn("keep", "@Int", "Int", "<State<Int>>",
                     "State.put(@Int.0);\nState.get(())")

_CATCH_ONLY = _fn("keep", "@Int", "Int", "pure", _exn("0", "@Int.0 + 1"))

_CLOSURE_HANDLER = _fn("keep", "@Int", "Int", "pure", _positioned(
    "closure", _state("@Int.0", "put(get(()) + 1);\nget(())")))

_STATE_HANDLER_ONLY = _fn("keep", "@Int", "Int", "pure",
                          _state("@Int.0", "@Int.0 + 1"))


def test_a_row_s_bare_operations_declare_its_cell(tmp_path: Path) -> None:
    """A row's cell whose one use is a bare `put` and `get` is declared by
    the two calls; 4 is stored and read."""
    compiled = pipeline.compile(_ROW_BARE)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _cells(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _ROW_BARE), "--fn", "keep", "--", "4")
    assert (ran.returncode, ran.stdout.strip()) == (0, "4"), ran.stderr


def test_a_row_s_qualified_operations_declare_its_cell(tmp_path: Path) -> None:
    """The same, through `State.put` and `State.get`, which the qualified
    route hands to the bare one."""
    compiled = pipeline.compile(_ROW_QUALIFIED)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _cells(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _ROW_QUALIFIED), "--fn", "keep", "--", "4")
    assert (ran.returncode, ran.stdout.strip()) == (0, "4"), ran.stderr


def test_a_handler_s_catch_alone_declares_its_tag(tmp_path: Path) -> None:
    """An `Exn` handler whose body throws nothing: its catch is the tag's
    one use.  4 comes back as 5."""
    compiled = pipeline.compile(_CATCH_ONLY)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _tags(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _CATCH_ONLY), "--fn", "keep", "--", "4")
    assert (ran.returncode, ran.stdout.strip()) == (0, "5"), ran.stderr


def test_a_closure_s_handler_declares_its_cell(tmp_path: Path) -> None:
    """A `State` handler in a closure's body, the cell's one use: the lifted
    closure's record is declared at the closure merge.  4 is stored, 5 put
    and read."""
    compiled = pipeline.compile(_CLOSURE_HANDLER)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _cells(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _CLOSURE_HANDLER),
                       "--fn", "keep", "--", "4")
    assert (ran.returncode, ran.stdout.strip()) == (0, "5"), ran.stderr


def test_a_state_handler_alone_declares_its_cell(tmp_path: Path) -> None:
    """A `State` handler whose body calls no operation: its push, put and
    pop are the cell's one use."""
    compiled = pipeline.compile(_STATE_HANDLER_ONLY)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert _cells(compiled.wat) == ({"Int"}, {"Int"})
    ran = pipeline.cli("run", _write(tmp_path, _STATE_HANDLER_ONLY),
                       "--fn", "keep", "--", "4")
    assert (ran.returncode, ran.stdout.strip()) == (0, "5"), ran.stderr


# ---------------------------------------------------------------------
# A handler's block declares the result its arms leave
# ---------------------------------------------------------------------


_BODY_ALWAYS_THROWS = _fn("main", "@Unit", "Int", "pure", _exn(
    "@Int.0 + 1", "throw(41)"))

_ARMS_FOLD = _fn("fold_both", "@Bool", "Int", "pure", """\
let @Array<Int> = [0, 1, 8];
""" + _exn(
    "array_fold(@Array<Int>.0, @Int.0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })",
    "if @Bool.0 then { throw(1) } else { 0 };\n"
    "array_fold(@Array<Int>.0, 0, fn(@Int, @Int -> @Int) effects(pure) { @Int.1 + @Int.0 })"))


_WIDTHS = _fn("widths", "@Int", "Int", "pure", """\
let @Option<Int> = handle[Exn<Int>] {
  throw(@Int) -> { Some(@Int.0 + 1) }
} in {
  if @Int.0 > 5 then { throw(@Int.0) } else { Some(0) }
};
let @String = handle[Exn<Int>] {
  throw(@Int) -> { "thrown" }
} in {
  if @Int.0 > 5 then { throw(@Int.0) } else { "quiet" }
};
match @Option<Int>.0 {
  Some(@Int) -> @Int.0 + string_length(@String.0),
  None -> 0
}""")


def test_a_handler_valued_at_a_pointer_or_a_pair_declares_its_width(
        tmp_path: Path) -> None:
    """A handler valued at a data type declares an `i32` result and one
    valued at a `String` an `(i32, i32)` result, the widths the checker's
    types give.  At 7 both throw: `Some(8)` and `"thrown"`, so 8 + 6; at 2
    neither does: `Some(0)` and `"quiet"`, so 0 + 5."""
    compiled = pipeline.compile(_WIDTHS)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    results = re.findall(r"block \$hd_\d+ \(result ([^)]*)\)", compiled.wat)
    assert results == ["i32", "i32 i32"], results
    path = _write(tmp_path, _WIDTHS)
    thrown = pipeline.cli("run", path, "--fn", "widths", "--", "7")
    assert (thrown.returncode, thrown.stdout.strip()) == (0, "14"), thrown.stderr
    quiet = pipeline.cli("run", path, "--fn", "widths", "--", "2")
    assert (quiet.returncode, quiet.stdout.strip()) == (0, "5"), quiet.stderr


def test_a_handler_whose_body_always_throws_takes_its_clause_s_value() -> None:
    """The checker types a handler at its handled body's type, `Never` for
    a body that always throws, while the clause leaves the handler's value:
    the block's result is the clause's."""
    ran = pipeline.cli("run", "-", stdin=_BODY_ALWAYS_THROWS)
    assert (ran.returncode, ran.stdout.strip()) == (0, "42"), ran.stderr


def test_an_exn_handler_whose_arms_are_folds_over_closures_loads(
        tmp_path: Path) -> None:
    """Arms whose type code generation's own reading has no answer for, an
    `array_fold` over a closure in each, which no `State` handler is in:
    the block's result is the checker's type of the arms, whatever they
    are.  Without a throw the body's fold is 9; with one, the clause's fold
    starts at the thrown 1 and is 10."""
    path = _write(tmp_path, _ARMS_FOLD)
    quiet = pipeline.cli("run", path, "--fn", "fold_both", "--", "false")
    assert (quiet.returncode, quiet.stdout.strip()) == (0, "9"), quiet.stderr
    thrown = pipeline.cli("run", path, "--fn", "fold_both", "--", "true")
    assert (thrown.returncode, thrown.stdout.strip()) == (0, "10"), thrown.stderr


# ---------------------------------------------------------------------
# Not this class: a caller dropped after it compiled (#1795)
# ---------------------------------------------------------------------


_DROPPED_CALLEE = _fn("g", "@Int", "Int", "pure", f"""\
{_DROPPER}
@Int.0""", visibility="private")

_E620_CALLER = _DROPPED_CALLEE + "\n" + _fn("f", "@Int", "Int", "pure", f"""\
let @Float64 = sin(1.0);
{_state("@Int.0", "g(get(()))")}""") + "\n" + _MAIN


@pytest.mark.xfail(strict=True, reason=(
    "#1795: a function's record of the host imports, flags, cells and tags "
    "its code uses joins the module's at the per-function and closure "
    "merges, while it compiles, and `_drop_dangling_callers` drops a caller "
    "of a dropped function (E620) after every function has compiled, "
    "taking nothing back out"))
@pytest.mark.usefixtures("skip_map_inserts")
def test_a_caller_of_a_dropped_function_declares_nothing(tmp_path: Path) -> None:
    """A function dropped as a caller of a dropped function (E620) declares
    neither the host import nor the cell its code used, and the WASI target
    builds the module."""
    compiled = pipeline.compile(_E620_CALLER)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert {"E602", "E620"} <= {d.error_code for d in compiled.warnings}
    assert compiled.exports == ["main"]
    assert _cells(compiled.wat) == (set(), set())
    assert '"sin"' not in compiled.wat
    assert _wasi(tmp_path, _write(tmp_path, _E620_CALLER)).returncode == 0
