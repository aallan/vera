"""A value declared at a type the program writes is laid out by the type the
checker resolved it to (#1525).

Code generation read a declared value's width, pair-ness and GC-rootness
off the type's spelling: the slot name a `let`, a parameter, a binder or a
cell is bound under.  A parameterised alias names nothing there, so
`let @Id<Nat> = 5` and `match Some(5) { Some(@Id<Nat>) -> ... }` dropped
their function, `@W<Int>.0` under `type W<T> = String` was read as one
word of a pair, a `State<Future<Int>>` cell's locals were pointers where
its host imports take an i64, and a sub-pattern with no binder (a wildcard
over a `Tuple` component, a literal) had no width at all.  The checker now
records the type each type expression resolves to and the type each
pattern is matched at, the typed program carries both into every clone,
and code generation reads them.

The matrix is every site a program declares a value at (a `let`, a
parameter, a return, a match binder top-level and nested, a tuple-pattern
component and a wildcard beside one, a destructure, a `State` cell, an
`Exn` payload, a closure parameter, an array element, a closure capture,
and a heap binding that must stay rooted across allocations under eager
collection) x every width class (an i64, an i32 scalar, an f64, a `String`
pair, an `Array` pair, a data pointer, a tuple pointer, a closure, a
`Future`) x every spelling (the type itself, a plain alias, `Id<V>` under
`type Id<T> = T`, and a phantom `W<Int>` under `type W<T> = V`).  Each cell
is its own test, unparametrised, so the mutation lane never samples one
out; each checks, verifies with the reconciliation join, compiles, and runs
`cell` to the value its kind's use gives.  A `State` cell of a pair is the
checker's refusal (E340), asserted as such.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tests import pipeline

pytestmark = pytest.mark.matrix(decides=[
    "vera/checker/resolution.py",
    "vera/checker/control.py",
    "vera/typed.py",
    "vera/wasm/inference.py",
    "vera/wasm/helpers.py",
    "vera/wasm/context.py",
    "vera/wasm/data.py",
    "vera/wasm/operators.py",
    "vera/wasm/closures.py",
    "vera/wasm/calls_handlers.py",
    "vera/codegen/contracts.py",
])

_C = "  requires(true)\n  ensures(true)\n  effects({effects})\n"


@dataclass(frozen=True)
class Kind:
    """A width class: its type, a value of it, an `Int` use of a slot."""

    name: str
    type: str
    value: str
    use: str
    expect: int
    heap: str | None = None
    """A value of the type the heap holds, for the rooted site."""


KINDS = (
    Kind("nat", "Nat", "5", "nat_to_int({s})", 5),
    Kind("bool", "Bool", "true", "if {s} then {{ 1 }} else {{ 0 }}", 1),
    Kind("float", "Float64", "2.5", "float_to_int({s})", 2),
    Kind("string", "String", '"abc"', "nat_to_int(string_length({s}))", 3,
         heap='string_concat("ab", "c")'),
    Kind("array", "Array<Int>", "[41, 2]", "{s}[0]", 41,
         heap="array_append([41], 2)"),
    Kind("option", "Option<Int>", "Some(4)", "option_unwrap_or({s}, 0)", 4,
         heap="Some(nat_to_int(array_length(array_append([1, 2], 3))) + 1)"),
    Kind("tuple", "Tuple<Int, Int>", "Tuple(4, 5)",
         "match {s} {{\n    Tuple(@Int, @Int) -> @Int.1\n  }}", 4,
         heap="Tuple(4, nat_to_int(array_length([1, 2])))"),
    Kind("closure", "F", "fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }",
         "apply_fn({s}, 3)", 4),
    Kind("future", "Future<Int>", "async(4)", "await({s})", 4),
)

SPELLINGS = ("direct", "alias", "id", "phantom")

SITES = ("let", "param", "ret", "binder", "top_binder", "component",
         "wildcard", "destructure", "state", "exn", "closure_param",
         "element", "capture", "rooted")


def _spelled(kind: Kind, spelling: str) -> tuple[str, str]:
    """The declared type's text, and the declarations it needs."""
    header = ("type F = fn(Int -> Int) effects(pure);\n"
              if kind.name == "closure" else "")
    if spelling == "direct":
        return kind.type, header
    if spelling == "alias":
        return "A", header + f"type A = {kind.type};\n"
    if spelling == "id":
        return f"Id<{kind.type}>", header + "type Id<T> = T;\n"
    return "W<Int>", header + f"type W<T> = {kind.type};\n"


@dataclass(frozen=True)
class Cell:
    """One site, width class and spelling."""

    site: str
    kind: Kind
    spelling: str

    @property
    def name(self) -> str:
        return f"{self.site}_{self.kind.name}_{self.spelling}"

    @property
    def refused(self) -> bool:
        """A `State` cell of a pair, which the checker refuses (E340)."""
        return self.site == "state" and self.kind.name in ("string", "array")

    @property
    def expect(self) -> int:
        return 7 if self.site == "wildcard" else self.kind.expect

    def source(self) -> str:
        x, header = _spelled(self.kind, self.spelling)
        kind, v = self.kind, self.kind.value
        use = kind.use.format(s=f"@{x}.0")
        effects = "<Async>" if kind.name == "future" else "pure"
        contract = _C.format(effects=effects)
        helpers = ""
        site = self.site
        if site == "let":
            body = f"  let @{x} = {v};\n  {use}"
        elif site == "param":
            helpers = f"private fn take(@{x} -> @Int)\n{contract}{{\n  {use}\n}}\n\n"
            body = f"  take({v})"
        elif site == "ret":
            helpers = f"private fn mk(@Unit -> @{x})\n{contract}{{\n  {v}\n}}\n\n"
            body = "  " + kind.use.format(s="mk(())")
        elif site == "binder":
            body = (f"  match Some({v}) {{\n    Some(@{x}) -> {use},\n"
                    f"    None -> 0\n  }}")
        elif site == "top_binder":
            body = f"  match {v} {{\n    @{x} -> {use}\n  }}"
        elif site == "component":
            body = (f"  match Tuple({v}, 7) {{\n"
                    f"    Tuple(@{x}, @Int) -> {use}\n  }}")
        elif site == "wildcard":
            body = (f"  match Tuple({v}, 7) {{\n"
                    f"    Tuple(_, @Int) -> @Int.0\n  }}")
        elif site == "destructure":
            body = f"  let Tuple<@{x}, @Int> = Tuple({v}, 7);\n  {use}"
        elif site == "state":
            body = (f"  handle[State<{x}>](@{x} = {v}) {{\n"
                    f"    get(@Unit) -> {{ resume(@{x}.0) }},\n"
                    f"    put(@{x}) -> {{ resume(()) }}\n"
                    f"  }} in {{\n    put({v});\n"
                    f"    {kind.use.format(s='get(())')}\n  }}")
        elif site == "exn":
            body = (f"  handle[Exn<{x}>] {{\n    throw(@{x}) -> {{ {use} }}\n"
                    f"  }} in {{\n    throw({v})\n  }}")
        elif site == "closure_param":
            body = (f"  apply_fn(fn(@{x} -> @Int) effects({effects}) "
                    f"{{ {use} }}, {v})")
        elif site == "element":
            body = (f"  let @Array<{x}> = [{v}];\n  "
                    + kind.use.format(s=f"@Array<{x}>.0[0]"))
        elif site == "capture":
            body = (f"  let @{x} = {v};\n  apply_fn(fn(@Int -> @Int) "
                    f"effects({effects}) {{ {use} + @Int.0 }}, 0)")
        else:
            # Two allocations between the binding and its use, at types no
            # width class is spelled as, so the binding's slot is its own.
            body = (f"  let @{x} = {kind.heap or v};\n"
                    "  let @Array<Bool> = array_append([true], false);\n"
                    "  let @Array<Float64> = array_append([1.5], 2.5);\n"
                    f"  {use}")
        return (header + "\n" + helpers + "public fn cell(@Unit -> @Int)\n"
                + contract + "{\n" + body + "\n}\n")


_CELLS = tuple(Cell(site, kind, spelling) for site in SITES for kind in KINDS
               for spelling in SPELLINGS)


def _observe(cell: Cell, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
             ) -> None:
    path = tmp_path / "cell.vera"
    path.write_text(cell.source(), encoding="utf-8")
    if cell.refused:
        checked = pipeline.check(path)
        assert {d.error_code for d in checked.errors} == {"E340"}, [
            d.format() for d in checked.diagnostics]
        return
    if cell.site == "rooted":
        monkeypatch.setenv("VERA_EAGER_GC", "1")
    verified = pipeline.verify(path, reconcile=True)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    joined = verified.reconciled
    assert joined is not None and joined.reconciliation is not None, (
        "the reconciliation join did not run")
    report = joined.report()
    assert report["mismatches"] == [], report
    ran = pipeline.run(path, "cell", [])
    assert ran.ok, ran.stderr or ran.trap
    assert ran.value == cell.expect, ran.value


def _cell_test(cell: Cell) -> Callable[[Path, pytest.MonkeyPatch], None]:
    def test(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
        _observe(cell, tmp_path, monkeypatch)
    test.__name__ = f"test_{cell.name}"
    test.__doc__ = (f"A {cell.kind.name} declared at its {cell.spelling} "
                    f"spelling at a {cell.site} site.")
    return test


#: The `Nat` cells whose join reports a guard with no record: a binder
#: (top-level, nested, a tuple component's) or a destructure binding at
#: `@Nat` over a component the construction built from a non-negative
#: literal.  Code generation guards by the component's type (`Int`, a
#: literal being an `Int`, spec §4.2), and the verifier, tracing the
#: component to its source (`vera.narrowing.component_narrows`), records
#: nothing (#1695's (a) member).
_DEAD_NAT_GUARD = frozenset({
    "binder_nat_alias",
    "binder_nat_direct",
    "binder_nat_id",
    "binder_nat_phantom",
    "component_nat_alias",
    "component_nat_direct",
    "component_nat_id",
    "component_nat_phantom",
    "destructure_nat_alias",
    "destructure_nat_direct",
    "destructure_nat_id",
    "destructure_nat_phantom",
    "top_binder_nat_alias",
    "top_binder_nat_direct",
    "top_binder_nat_id",
    "top_binder_nat_phantom",
})


for _cell in _CELLS:
    _test = _cell_test(_cell)
    if _cell.name in _DEAD_NAT_GUARD:
        _test = pytest.mark.xfail(strict=True, reason=(
            "#1695 (a): code generation guards a binder by its component's "
            "type where the verifier reads the component's source"))(_test)
    globals()[f"test_{_cell.name}"] = _test
del _cell, _test


def test_the_matrix_spans_every_combination() -> None:
    """504 cells: 14 sites, 9 width classes, 4 spellings; the 8 `State`
    cells of a pair are the checker's refusal."""
    assert len(_CELLS) == len({c.name for c in _CELLS}) == 504
    assert sum(c.refused for c in _CELLS) == 8


# ---------------------------------------------------------------------
# What the matrix's runs cannot see
# ---------------------------------------------------------------------

_LITERALS = """\
private data Tag {
  Num(Int),
  Flag(Bool),
  Small(Byte),
  Word(String)
}

public fn pick(@Tag -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Tag.0 {
    Num(3) -> 1,
    Flag(true) -> 2,
    Small(7) -> 3,
    Word("hi") -> 4,
    _ -> 0
  }
}

public fn num(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Num(@Int.0))
}

public fn flag(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Flag(@Int.0 > 0))
}

public fn small(@Byte -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Small(@Byte.0))
}

public fn word(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Word(if @Int.0 > 0 then { "hi" } else { "ho" }))
}
"""


def test_repro_a_literal_sub_pattern_compares_its_field(tmp_path: Path,
                                                        ) -> None:
    """A literal sub-pattern is a comparison of its field: the arm is taken
    when the field equals the literal and only then, at each width (an i64,
    a `Bool`, a `Byte`, a `String` pair)."""
    path = tmp_path / "literals.vera"
    path.write_text(_LITERALS, encoding="utf-8")
    verified = pipeline.verify(path)
    assert verified.ok, [d.format() for d in verified.diagnostics]
    compiled = pipeline.compile(path)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    for fn, hit, miss, taken in (("num", 3, 4, 1), ("flag", 1, -1, 2),
                                 ("small", 7, 8, 3), ("word", 1, -1, 4)):
        assert pipeline.run(compiled, fn, [hit]).value == taken, fn
        assert pipeline.run(compiled, fn, [miss]).value == 0, fn


_COMPOSITE_CLONES = """\
private data Box<T> {
  MkBox(T)
}

private forall<T> fn unbox(@Box<T> -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Box<T>.0 {
    MkBox(@T) -> @T.0
  }
}

private forall<T> fn same(@T, @T -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0 == @T.1
}

public fn main(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Map<String, Int> = map_insert(map_new(), "k", 1);
  let @Box<Option<Int>> = MkBox(Some(nat_to_int(map_size(@Map<String, Int>.0))));
  same(unbox(@Box<Option<Int>>.0), Some(1))
}
"""


def _untyped(checked: pipeline.Checked) -> list[str]:
    """Every type expression and pattern of a compiled body (each function
    that is not generic, and every instance's clone) the typed program
    holds no type for; a refinement's predicate and an effect row are not
    a declared value's type."""
    from dataclasses import fields

    from vera import ast

    typed = checked.typed
    decls = [t.decl for t in checked.program.declarations
             if isinstance(t.decl, ast.FnDecl) and not t.decl.forall_vars]
    decls += [inst.clone for inst in typed.instances if inst.clone]
    missing: list[str] = []
    for decl in decls:
        stack: list[object] = [decl]
        while stack:
            item = stack.pop()
            if isinstance(item, tuple):
                stack.extend(item)
                continue
            if not isinstance(item, ast.Node):
                continue
            if isinstance(item, (ast.TypeExpr, ast.Pattern)) and (
                    item.node_id is None
                    or item.node_id not in typed.semantic):
                missing.append(f"{decl.name}: {type(item).__name__}")
            for f in fields(item):
                if f.name in ("span", "predicate", "effect") or (
                        f.metadata.get("identity")):
                    continue
                stack.append(getattr(item, f.name))
    return missing


def test_repro_every_declared_type_of_a_clone_is_typed(tmp_path: Path,
                                                       ) -> None:
    """A clone's type expressions are typed, the parts its substitution
    parsed from a type argument's name (`T` at `Option<Int>`, a slot
    reference's `Map<String, Int>`) among them, and so is every pattern."""
    path = tmp_path / "clones.vera"
    path.write_text(_COMPOSITE_CLONES, encoding="utf-8")
    checked = pipeline.check(path)
    assert checked.ok, [d.format() for d in checked.diagnostics]
    assert [i.name for i in checked.typed.instances if i.clone], "no clone"
    assert _untyped(checked) == []
    assert pipeline.run(path, "main", []).value == 1


_PERMUTED_ALIAS = """\
type Swap<A, B> = Result<B, A>;

private forall<A, B> fn side(@Swap<A, B> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Swap<A, B>.0 {
    Ok(@B) -> 1,
    Err(@A) -> 2
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Swap<Option<Int>, Array<String>> = Ok(["a"]);
  side(@Swap<Option<Int>, Array<String>>.0)
}
"""


def test_repro_a_permuted_alias_types_each_part_as_itself(tmp_path: Path,
                                                          ) -> None:
    """An alias applied to arguments resolves to another constructor's
    arguments, here in the other order (`Swap<Option<Int>, Array<String>>`
    is a `Result<Array<String>, Option<Int>>`): each part the clone's
    substitution parsed is typed as what it names.  Paired by position with
    the resolved type's arguments, the parameter's and the slot reference's
    `Int` were recorded at `String`, and their `String` at `Int`."""
    from dataclasses import fields

    from vera import ast
    from vera.types import pretty_type

    path = tmp_path / "swap.vera"
    path.write_text(_PERMUTED_ALIAS, encoding="utf-8")
    checked = pipeline.check(path)
    assert checked.ok, [d.format() for d in checked.diagnostics]
    typed = checked.typed
    clones = [inst.clone for inst in typed.instances if inst.clone]
    assert clones, "no clone"
    parts: list[tuple[str, str | None]] = []
    stack: list[object] = list(clones)
    while stack:
        item = stack.pop()
        if isinstance(item, tuple):
            stack.extend(item)
            continue
        if not isinstance(item, ast.Node):
            continue
        if (isinstance(item, ast.NamedType) and not item.type_args
                and item.name in ("Int", "String")):
            ty = (typed.semantic.get(item.node_id)
                  if item.node_id is not None else None)
            parts.append((item.name, None if ty is None else pretty_type(ty)))
        stack.extend(getattr(item, f.name) for f in fields(item)
                     if f.name != "span" and not f.metadata.get("identity"))
    # The parameter's, the slot reference's and the binders' parsed parts,
    # two each, and the return type's `Int`.
    assert len(parts) == 7, parts
    assert all(name == recorded for name, recorded in parts), parts
    assert pipeline.run(path, "main", []).value == 1


def test_repro_an_untyped_expression_has_no_stack_shape() -> None:
    """Whether an expression leaves words on the stack is its checked
    type's question: a `Unit` leaves none and an `Int` one, and an
    expression the check did not type is refused as a broken invariant,
    never read as one that leaves nothing, which would leave its value with
    no `drop` and no root."""
    from vera import ast
    from vera.skip import CodegenInvariantError
    from vera.types import INT, UNIT
    from vera.wasm.context import WasmContext
    from vera.wasm.helpers import StringPool

    ctx = WasmContext(StringPool())
    unit, one, bare = (ast.IntLit(value=1, node_id=ast.fresh_node_id())
                       for _ in range(3))
    assert unit.node_id is not None and one.node_id is not None
    ctx.set_expr_semantic_types({unit.node_id: UNIT, one.node_id: INT})
    assert ctx._is_void_expr(unit) is True
    assert ctx._is_void_expr(one) is False
    assert ctx._compute_stack_shape(one) == "i64"
    with pytest.raises(CodegenInvariantError):
        ctx._is_void_expr(bare)
    with pytest.raises(CodegenInvariantError):
        ctx._compute_stack_shape(bare)


_HELLO = """\
public fn main(@Unit -> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("hello\\n")
}
"""


def test_repro_an_unreferenced_prelude_template_adds_nothing(tmp_path: Path,
                                                             ) -> None:
    """A generic's template declares values at its bare type variables,
    which have no width: a prelude template the program never names is
    dropped where it always was, with nothing reported and no collector
    pulled into the module."""
    path = tmp_path / "hello.vera"
    path.write_text(_HELLO, encoding="utf-8")
    compiled = pipeline.compile(path)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert compiled.diagnostics == ()
    assert "(func $alloc" not in compiled.wat


_RANGED = """\
type SmallByte = { @Byte | @Byte.0 < 10 };
type Few = { @Nat | @Nat.0 < 10 };

public fn id_small(@SmallByte -> @SmallByte)
  requires(true)
  ensures(true)
  effects(pure)
{
  @SmallByte.0
}

public fn id_few(@Few -> @Few)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Few.0
}
"""


def test_repro_a_refined_byte_and_nat_parameter_guard_its_range(
        tmp_path: Path) -> None:
    """A refinement over `Byte` or `Nat` guards its predicate conjoined with
    its base's range, nodes built after the check and typed where they are
    built: in range passes, out of range traps."""
    path = tmp_path / "ranged.vera"
    path.write_text(_RANGED, encoding="utf-8")
    compiled = pipeline.compile(path)
    assert compiled.ok, [d.format() for d in compiled.diagnostics]
    assert pipeline.run(compiled, "id_small", [3]).value == 3
    assert pipeline.run(compiled, "id_few", [4]).value == 4
    for fn, bad in (("id_small", 12), ("id_few", 11)):
        ran = pipeline.run(compiled, fn, [bad])
        assert not ran.ok and ran.trap is not None, (fn, bad, ran.value)
