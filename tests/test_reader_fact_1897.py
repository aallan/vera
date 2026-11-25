"""A narrowing is never proved from the fact its own reader reads (#1897).

A `match` arm that binds a component of a composite takes the component's
declared refinement as a fact (`ContractVerifier._subpattern_source_facts`),
read off the scrutinee's declared type, and the SMT layer asserts it into the
solver's base context while it translates the body (`_translate_match`).  A
slot bound by a narrowing (`let @Tuple<Small, Int> = @Tuple<Int, Int>.0`)
holds the source value's own term, so that fact is the goal of the
narrowing's own `refine_bind`, asserted before the binding walk asks it.  The
narrowing was recorded `verified`, and so was every other obligation over the
same term (an `ensures`, a call's precondition, a second narrowing of the same
value at a call, a `put`, a return); a payload no boundary checks reached its
reader with every gate green.

THE RULE.  A producer's own obligation is discharged without the fact it
publishes (spec §6.2.5, §2.6.4).  A narrowing row below a type's head (the
table lists one exactly where the value's own type does not state the
refinement its position writes) is the producer of every fact a reader takes
off that type, so the translation records the narrowed value
(`ContractVerifier._note_narrowing`): at the row's value, at the component a
binder row takes apart, at the stand-in a walk binds where it cannot read the
value, at a join whose leaf narrows, and at a built-in's result over a
narrowed value (a store, a read back out of it).  The one gate every reader
asks, `_established_facts`, withholds a fact over a term that holds a
narrowed value, as it withholds a disclosed producer's: offered only on a
second attempt, so a goal that needs it is Tier 3 (E534, E532), and the
narrowing's own query (`check_valid`'s *own*) is offered it on no attempt, so
a narrowing nothing else establishes is refuted (E505) or left to its check.

THE INSTRUMENT.  The generated matrix crosses where the narrowed value comes
from (a parameter, a call's result, a `let`-bound slot, a `match` binder, a
destructured component, an `if` join, a handler clause's parameter, a
`handle`'s value), where it narrows (a `let`, a constructor field, a tuple
component, a `State` `put`, a call argument, an `apply_fn` argument, a return,
a narrowing `match` binder, a destructured component), the shape
(`Tuple<Small, Int>`, `Option<Small>`, a data type `Wrap<Small>`, a nested
tuple), the reader (a binding sub-pattern at the base type, one at the
refined type, a wildcard, a destructure, none), where the reader stands (the
narrowed value itself, a `let` narrowing of the same value before the
position, or after it), and the predicate (one the solver decides, one
outside its fragment).  The value is 50 at every run, which `Small` refuses
under both predicates, so in every cell:

* no `refine_bind` record at the narrowing is `verified`;
* a run that delivers the value does so only where verification refuses the
  program or discloses the narrowing (`tier3_unguarded`, E506);
* the differential: every `verified` record of the program is `verified`
  again with every reader fact withheld (`_subpattern_source_facts` returning
  none), so no record rests on a reader's fact.

The narrowing `match` binder and the destructured component below a binder's
head have no record at all: they are #1542's, pinned here as they are (no
record) for the lane that adds them.
"""

from __future__ import annotations

import itertools
import re
import textwrap
from dataclasses import dataclass
from typing import Any, Callable

import pytest

from tests import pipeline
from vera import verifier as verifier_mod
from vera.reconcile import reconcile

# The modules that decide the class: the translation that records a narrowed
# value and asserts a reader's facts, and the verifier's gate, its hook and
# the narrowing discharges.
pytestmark = pytest.mark.matrix(decides=["vera/smt.py", "vera/verifier.py"])

FILE = "reader_fact_1897.vera"
VIOLATING = 50

PREDICATES = {
    "solver": "@Int.0 < 10",
    "outside": "string_length(to_string(@Int.0)) < 2",
}


@dataclass(frozen=True)
class Shape:
    refined: str
    base: str
    build: str
    valid: str
    bind: tuple[tuple[str, str], ...]
    ref: tuple[tuple[str, str], ...]
    wild: tuple[tuple[str, str], ...]
    destr: tuple[tuple[str, ...], str] | None


SHAPES = {
    "tuple": Shape(
        "Tuple<Small, Int>", "Tuple<Int, Int>", "Tuple(@Int.0, 0)",
        "Tuple(1, 0)",
        (("Tuple(@Int, @Int)", "@Int.1"),),
        (("Tuple(@Small, @Int)", "@Small.0"),),
        (("Tuple(_, @Int)", "1"),),
        (("let Tuple<@Int, @Int> = {E};",), "@Int.1")),
    "option": Shape(
        "Option<Small>", "Option<Int>", "Some(@Int.0)", "Some(1)",
        (("Some(@Int)", "@Int.0"), ("None", "0")),
        (("Some(@Small)", "@Small.0"), ("None", "0")),
        (("Some(_)", "1"), ("None", "0")),
        None),
    "data": Shape(
        "Wrap<Small>", "Wrap<Int>", "W(@Int.0)", "W(1)",
        (("W(@Int)", "@Int.0"),),
        (("W(@Small)", "@Small.0"),),
        (("W(_)", "1"),),
        None),
    "nested": Shape(
        "Tuple<Tuple<Small, Int>, Int>", "Tuple<Tuple<Int, Int>, Int>",
        "Tuple(Tuple(@Int.0, 0), 0)", "Tuple(Tuple(1, 0), 0)",
        (("Tuple(Tuple(@Int, @Int), _)", "@Int.1"),),
        (("Tuple(Tuple(@Small, @Int), _)", "@Small.0"),),
        (("Tuple(Tuple(_, @Int), _)", "1"),),
        (("let Tuple<@Tuple<Int, Int>, @Int> = {E};",
          "let Tuple<@Int, @Int> = @Tuple<Int, Int>.0;"), "@Int.1")),
}
SOURCES = ("param", "call", "let", "binder", "destructure", "ifjoin",
           "clause", "handleval")
POSITIONS = ("let", "field", "tcomp", "put", "call", "apply", "return",
             "mbind", "destrp")
READERS = ("bind", "ref", "wild", "destr", "none")
#: The positions #1542 owns: a binder below the head with no record.
NO_RECORD_1542 = ("mbind", "destrp")


def _slot(t: str) -> str:
    return "@" + t


def _reader(shape: Shape, kind: str, expr: str,
            wrap: Callable[[str], str] = lambda p: p,
            wrap_bind: str | None = None) -> tuple[list[str], str] | None:
    """The statements reading *expr* (of the refined type) and the Int
    they leave, through a container pattern *wrap* where one is given."""
    if kind == "none":
        return [], "0"
    if kind == "destr":
        if shape.destr is None:
            return None
        stmts, res = shape.destr
        if wrap_bind is None:
            return [s.replace("{E}", expr) for s in stmts], res
        inner = " ".join(s.replace("{E}", _slot(shape.refined) + ".0")
                         for s in stmts)
        return ([f"let @Int = match {expr} {{ {wrap_bind} -> "
                 f"{{ {inner} {res} }} }};"], "@Int.0")
    arms = ", ".join(f"{wrap(p)} -> {r}" for p, r in getattr(shape, kind))
    return [f"let @Int = match {expr} {{ {arms} }};"], "@Int.0"


def _orders(position: str, reader: str) -> tuple[str, ...]:
    if reader == "none":
        return ("none",)
    if position in ("let", "mbind", "destrp"):
        return ("self",)
    if position in ("field", "tcomp"):
        return ("self", "pre", "post")
    if position == "return":
        return ("pre",)
    return ("pre", "post")


def _shift(expr: str, by: int) -> str:
    m = re.fullmatch(r"@Int\.(\d+)", expr)
    return f"@Int.{int(m.group(1)) + by}" if m else expr


@dataclass(frozen=True)
class Cell:
    source: str
    position: str
    shape: str
    reader: str
    predicate: str
    order: str

    @property
    def id(self) -> str:
        return "-".join((self.source, self.position, self.shape, self.reader,
                         self.predicate, self.order))


def _program(cell: Cell) -> tuple[str, str] | None:
    """The cell's program and the text of the narrowed expression's line
    (whose records are the narrowing's), or None for a product that is
    no program (a destructure reader of a non-tuple shape)."""
    sh = SHAPES[cell.shape]
    S, B = sh.refined, sh.base
    pre: list[str] = []
    post: list[str] = []
    inner_param, go_arg = "@Int", "@Int.0"

    def x_of(k: int) -> str:
        return {
            "param": f"{_slot(B)}.0", "let": f"{_slot(B)}.0",
            "binder": f"{_slot(B)}.0", "destructure": f"{_slot(B)}.0",
            "clause": f"{_slot(B)}.0",
            "call": f"mk(@Int.{k})",
            "ifjoin": (f"if @Int.{k} > 100 then {{ mk(@Int.{k}) }} "
                       f"else {{ mk(@Int.{k} + 1) }}"),
            "handleval": (f"handle[Exn<Int>] {{ throw(@Int) -> mk(@Int.0) }}"
                          f" in {{ mk(@Int.{k}) }}"),
        }[cell.source]

    if cell.source == "param":
        inner_param, go_arg = _slot(B), "mk(@Int.0)"
    elif cell.source == "let":
        pre = [f"let {_slot(B)} = mk(@Int.0);"]
    elif cell.source == "binder":
        pre, post = [f"match hold(@Int.0) {{ H({_slot(B)}) -> {{"], ["} }"]
    elif cell.source == "destructure":
        pre = [f"let Tuple<{_slot(B)}, @Int> = pair(@Int.0);"]
    elif cell.source == "clause":
        pre = [f"handle[Exn<{B}>] {{", f"throw({_slot(B)}) -> {{"]
        post = ["}", "} in {", "throw(mk(@Int.0))", "}"]

    extra: list[str] = []
    ret = "@Int"
    go_tail: tuple[list[str], str] | None = None
    order, reader = cell.order, cell.reader

    if cell.position in NO_RECORD_1542:
        if cell.position == "mbind":
            extra.append(_fn("wrapH", f"{_slot(B)}", f"@Hold<{B}>",
                             f"H({_slot(B)}.0)"))
        else:
            extra.append(_fn("pairOf", f"{_slot(B)}", f"@Tuple<{B}, Int>",
                             f"Tuple({_slot(B)}.0, 0)"))
        r = _reader(sh, reader, f"{_slot(S)}.0")
        if r is None:
            return None
        st, res = r
        if cell.position == "mbind":
            head = f"match wrapH({x_of(0)}) {{ H({_slot(S)}) ->"
            body = [head, "{ " + " ".join(st) + f" {res} }}", "}"]
        else:
            head = f"let Tuple<{_slot(S)}, @Int> = pairOf({x_of(0)});"
            body = [head, *st, res]
        return _assemble(cell, sh, pre + body + post, inner_param, go_arg,
                         ret, extra, go_tail), head

    def site(k: int) -> tuple[list[str], str, int]:
        x = x_of(k)
        pos = cell.position
        if pos == "let":
            return [f"let {_slot(S)} = {x};"], x, 0
        if pos == "field":
            return [f"let @Bx = MkBx({x});"], x, 0
        if pos == "tcomp":
            return [f"let @Tuple<{S}, Int> = Tuple({x}, 1);"], x, 0
        if pos == "put":
            return [f"put({x});"], x, 0
        if pos == "call":
            return [f"let @Int = consume({x});"], x, 1
        if pos == "apply":
            st, res = _reader(sh, "bind", f"{_slot(S)}.0")  # type: ignore[misc]
            clo = (f"fn({_slot(S)} -> @Int) effects(pure) {{ "
                   + " ".join(st) + f" {res} }}")
            return [f"let @Int = apply_fn({clo}, {x});"], x, 1
        return [x], x, 0  # return

    if cell.position == "field":
        extra.append(f"public data Bx {{ MkBx({S}) }}")
    if cell.position == "call":
        st, res = _reader(sh, "bind", f"{_slot(S)}.0")  # type: ignore[misc]
        extra.append(_fn("consume", _slot(S), "@Int", "\n  ".join([*st, res])))
    if cell.position == "return":
        ret = _slot(S)
        go_tail = _reader(sh, "bind", f"{_slot(S)}.0")  # type: ignore[assignment]

    def let_reader(k: int) -> tuple[list[str], str] | None:
        r = _reader(sh, reader, f"{_slot(S)}.0")
        if r is None:
            return None
        return [f"let {_slot(S)} = {x_of(k)};", *r[0]], r[1]

    if order == "none":
        lines, _x, n_site = site(0)
        body = lines + ([] if cell.position == "return"
                        else ["@Int.0" if n_site else "0"])
    elif order == "self":
        lines, _x, _n = site(0)
        if cell.position == "let":
            r = _reader(sh, reader, f"{_slot(S)}.0")
        elif cell.position == "field":
            r = _reader(sh, reader, "@Bx.0", wrap=lambda p: f"MkBx({p})",
                        wrap_bind=f"MkBx({_slot(S)})")
        else:
            r = _reader(sh, reader, f"@Tuple<{S}, Int>.0",
                        wrap=lambda p: f"Tuple({p}, _)",
                        wrap_bind=f"Tuple({_slot(S)}, _)")
        if r is None:
            return None
        body = lines + r[0] + [r[1]]
    elif order == "pre":
        lr = let_reader(0)
        if lr is None:
            return None
        st, res = lr
        n = _int_binders(st)
        lines, _x, n_site = site(n)
        body = st + lines + ([] if cell.position == "return"
                             else [_shift(res, n_site)])
    else:  # post
        lines, _x, n_site = site(0)
        lr = let_reader(n_site)
        if lr is None:
            return None
        body = lines + lr[0] + [lr[1]]

    if cell.position == "put":
        body = [f"handle[State<{S}>]({_slot(S)} = {sh.valid}) {{",
                f"get(@Unit) -> {{ resume({_slot(S)}.0) }},",
                f"put({_slot(S)}) -> {{ resume(()) }}",
                "} in {", *body, "}"]
    line_of_site = lines[0]
    return _assemble(cell, sh, pre + body + post, inner_param, go_arg, ret,
                     extra, go_tail), line_of_site


def _int_binders(stmts: list[str]) -> int:
    """How many `@Int` slots *stmts* bind, so a later `@Int.k` still names
    the function's parameter."""
    n = 0
    for s in stmts:
        if s.startswith("let @Int "):
            n += 1
        elif s.startswith("let Tuple<@Int, @Int>"):
            n += 2
        elif s.startswith("let Tuple<@Tuple<Int, Int>, @Int>"):
            n += 1
    return n


def _fn(name: str, param: str, ret: str, body: str) -> str:
    return (f"private fn {name}({param} -> {ret})\n  requires(true)\n"
            f"  ensures(true)\n  effects(pure)\n{{\n  {body}\n}}")


def _assemble(cell: Cell, sh: Shape, body: list[str], inner_param: str,
              go_arg: str, ret: str, extra: list[str],
              go_tail: tuple[list[str], str] | None) -> str:
    B = sh.base
    parts = [f"type Small = {{ @Int | {PREDICATES[cell.predicate]} }};",
             "public data Wrap<T> { W(T) }",
             "public data Hold<T> { H(T) }"]
    parts += [d for d in extra if d.startswith("public data")]
    parts += [_fn("mk", "@Int", _slot(B), sh.build),
              _fn("hold", "@Int", f"@Hold<{B}>", "H(mk(@Int.0))"),
              _fn("pair", "@Int", f"@Tuple<{B}, Int>", "Tuple(mk(@Int.0), 0)")]
    parts += [d for d in extra if not d.startswith("public data")]
    parts.append(
        f"private fn inner({inner_param} -> {ret})\n  requires(true)\n"
        "  ensures(true)\n  effects(pure)\n{\n"
        + "\n".join("  " + ln for ln in body) + "\n}")
    if go_tail is None:
        go_body = f"inner({go_arg})"
    else:
        go_body = "\n  ".join(
            [f"let {_slot(sh.refined)} = inner({go_arg});", *go_tail[0],
             go_tail[1]])
    parts.append(_fn("go", "@Int", "@Int", go_body).replace(
        "private fn go", "public fn go"))
    return "\n\n".join(parts) + "\n"


CELLS = [
    Cell(source, position, shape, reader, predicate, order)
    for source, position, shape, reader, predicate in itertools.product(
        SOURCES, POSITIONS, SHAPES, READERS, PREDICATES)
    for order in _orders(position, reader)
    if not (reader == "destr" and SHAPES[shape].destr is None)
]


# =====================================================================
# Helpers
# =====================================================================


def _status(o: Any) -> str:
    code = getattr(o, "error_code", None)
    return f"{o.status}/{code}" if code else o.status


def _verify(source: str) -> pipeline.Verified:
    verified = pipeline.verify(source, file=FILE)
    assert not verified.checked.errors, [
        (d.error_code, d.description[:80]) for d in verified.checked.errors]
    return verified


def _run(source: str, args: list[int]) -> pipeline.Ran:
    ran = pipeline.run(source, "go", args, file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, (
        [(d.error_code, d.description[:80]) for d in ran.compiled.errors]
        if ran.compiled is not None else "no compile")
    return ran


def _line(source: str, text: str) -> int:
    for n, ln in enumerate(source.splitlines(), 1):
        if ln.strip() == text.strip():
            return n
    raise AssertionError(f"no line {text!r}")


def _at_line(verified: pipeline.Verified, line: int,
             kind: str = "refine_bind") -> list[str]:
    return sorted(_status(o) for o in verified.obligations
                  if o.kind == kind and o.line == line)


def _site_records(verified: pipeline.Verified, source: str, line: int,
                  position: str) -> list[str]:
    """The narrowing's `refine_bind` records.  A return's are every one in
    `inner`, whose only narrowings are the return's and the `let` a reader
    before it reads (of the same value, or, for a `handle`, of the same
    expression evaluated again): at the body (column 3), at the leaves a
    join hands the requirement down to (a `handle`'s, whose value is its
    clauses' and its body's), and at the `let`; an `apply_fn` argument's
    at the argument, after the closure on the same line, whose own records
    stand inside it; every other position's at its line."""
    if position == "return":
        return sorted(_status(o) for o in verified.obligations
                      if o.kind == "refine_bind" and o.fn_name == "inner")
    first = 0
    if position == "apply":
        text = source.splitlines()[line - 1]
        first = text.rindex("}, ") + len("}, ") + 1
    return sorted(_status(o) for o in verified.obligations
                  if o.kind == "refine_bind" and o.line == line
                  and o.column >= first)


def _verified_records(verified: pipeline.Verified) -> set[tuple[str, int, int]]:
    return {(o.kind, o.line, o.column) for o in verified.obligations
            if o.status == "verified"}


@pytest.fixture
def withheld_readers(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every reader fact withheld: a `match` arm states nothing off the
    scrutinee's declared type."""
    monkeypatch.setattr(
        verifier_mod.ContractVerifier, "_subpattern_source_facts",
        lambda self, scrutinee, scrutinee_z3, pattern, smt: [])


# =====================================================================
# The reported instance and the class lines, unparametrised
# =====================================================================

SMALL = "type Small = { @Int | @Int.0 < 10 };\n\n"
SHORT = "type Short = { @Int | string_length(to_string(@Int.0)) < 3 };\n\n"

ISSUE = SMALL + textwrap.dedent("""\
    private fn inner(@Tuple<Int, Int> -> @Int)
      requires(true)
      ensures(@Int.result < 10)
      effects(pure)
    {
      let @Tuple<Small, Int> = @Tuple<Int, Int>.0;
      match @Tuple<Small, Int>.0 { Tuple(@Int, @Int) -> @Int.1 }
    }

    public fn go(@Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      inner(Tuple(@Int.0, 0))
    }
    """)


def test_repro_issue_1897() -> None:
    """The reported program: the `let` was `verified` from its reader's
    fact.  Now the narrowing is refuted (E505): its own query never reads
    the fact.  The `ensures` is Tier 3 (E534), by rule 2 (spec §2.6.5): a
    tuple component at a `let` is no position code generation checks, so
    the `let` establishes nothing and the reader's fact is withheld; the
    `ensures`'s own check traps the run."""
    verified = _verify(ISSUE)
    let = _line(ISSUE, "let @Tuple<Small, Int> = @Tuple<Int, Int>.0;")
    assert _at_line(verified, let) == ["violated/E505"]
    assert _at_line(verified, _line(ISSUE, "ensures(@Int.result < 10)"),
                    "ensures") == ["tier3/E534"]
    assert _run(ISSUE, [VIOLATING]).trap is not None


def _let_program(shape: str, reader: str, refined: str = "Small",
                 head: str = SMALL) -> str:
    sh = SHAPES[shape]
    S = sh.refined.replace("Small", refined)
    arms = reader.replace("Small", refined)
    return head + textwrap.dedent(f"""\
        public data Wrap<T> {{ W(T) }}

        private fn mk(@Int -> @{sh.base})
          requires(true)
          ensures(true)
          effects(pure)
        {{
          {sh.build}
        }}

        public fn go(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {{
          let @{S} = mk(@Int.0);
          match @{S}.0 {{ {arms} }}
        }}
        """)


@pytest.mark.parametrize("shape", list(SHAPES))
def test_repro_let_at_each_shape(shape: str) -> None:
    """Class line 1: a `let` at `Tuple<Small, Int>`, `Option<Small>`,
    `Wrap<Small>` or a nested tuple from a call, read by a binding
    sub-pattern: `verified` and 50 delivered; now refuted (E505)."""
    arms = ", ".join(f"{p} -> {r}" for p, r in SHAPES[shape].bind)
    source = _let_program(shape, arms)
    verified = _verify(source)
    let = _line(source, f"let @{SHAPES[shape].refined} = mk(@Int.0);")
    assert _at_line(verified, let) == ["violated/E505"]


def test_repro_outside_the_solver() -> None:
    """The issue's comment of 24 Nov: `Short` outside the solver's fragment
    at an `Option` from a call, read by a binding sub-pattern: the `let` was
    `verified` and 5000 delivered.  Now no record at the `let` is
    `verified`."""
    source = _let_program("option", "Some(@Int) -> @Int.0, None -> 0",
                          refined="Short", head=SHORT)
    verified = _verify(source)
    let = _line(source, "let @Option<Short> = mk(@Int.0);")
    assert "verified" not in _at_line(verified, let)
    assert _at_line(verified, let)


def _cell_program(**kw: str) -> tuple[str, int]:
    cell = Cell(**kw)  # type: ignore[arg-type]
    made = _program(cell)
    assert made is not None
    source, site = made
    return source, _line(source, site)


@pytest.mark.parametrize("position", ["field", "tcomp"])
def test_repro_field_and_tuple_component(position: str) -> None:
    """Class line 2: a constructor field and a tuple component given the
    parameter, beside a `let` narrowing of it that a reader reads: the store
    was `verified` and 50 delivered; now refuted."""
    source, line = _cell_program(source="param", position=position,
                                 shape="tuple", reader="bind",
                                 predicate="solver", order="pre")
    verified = _verify(source)
    assert _at_line(verified, line) == ["violated/E505"]


def test_repro_state_put() -> None:
    """Class line 3: a `put` of the parameter after a reader of it at
    `State<Tuple<Small, Int>>`: `verified` and 50 delivered; now refuted."""
    source, line = _cell_program(source="param", position="put",
                                 shape="tuple", reader="bind",
                                 predicate="solver", order="pre")
    verified = _verify(source)
    assert _at_line(verified, line) == ["violated/E505"]


@pytest.mark.parametrize(("position", "order"), [
    ("call", "pre"), ("call", "post"), ("apply", "pre"), ("apply", "post"),
    ("return", "pre"),  # a return has nothing after it
])
def test_repro_call_apply_and_return(position: str, order: str) -> None:
    """Class line 4: a call argument, an `apply_fn` argument and a return,
    before or after a reader of the same value: `verified`; an `Option`
    payload was delivered.  Now refuted."""
    source, line = _cell_program(source="param", position=position,
                                 shape="option", reader="bind",
                                 predicate="solver", order=order)
    verified = _verify(source)
    if position == "return":
        records = sorted(_status(o) for o in verified.obligations
                         if o.kind == "refine_bind" and o.fn_name == "inner"
                         and o.line >= line - 2)
        assert "verified" not in records, records
        assert "violated/E505" in records, records
    else:
        assert _at_line(verified, line) == ["violated/E505"]


def test_repro_other_obligations_over_the_value() -> None:
    """Class line 5: an `ensures` over the value read, and a call's
    precondition after the reader, were `verified` beside a narrowing
    proved from the same fact.  The narrowing is now refuted; the two are
    Tier 3, by rule 2 (spec §2.6.5): the `let`'s tuple component is
    disclosed, not checked, so it establishes no fact for its reader, and
    their own checks trap the run."""
    body = textwrap.dedent("""\
        private fn need(@Int -> @Int)
          requires(@Int.0 < 10)
          ensures(@Int.result == @Int.0)
          effects(pure)
        {
          @Int.0
        }

        private fn inner(@Tuple<Int, Int> -> @Int)
          requires(true)
          ensures(@Int.result < 10)
          effects(pure)
        {
          let @Tuple<Small, Int> = @Tuple<Int, Int>.0;
          let @Int = match @Tuple<Small, Int>.0 { Tuple(@Int, @Int) -> @Int.1 };
          need(@Int.0)
        }

        public fn go(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          inner(Tuple(@Int.0, 0))
        }
        """)
    source = SMALL + body
    verified = _verify(source)
    ensures = _line(source, "ensures(@Int.result < 10)")
    call = _line(source, "need(@Int.0)")
    let = _line(source, "let @Tuple<Small, Int> = @Tuple<Int, Int>.0;")
    assert _at_line(verified, let) == ["violated/E505"]
    assert _at_line(verified, ensures, "ensures") == ["tier3/E522"]
    assert [r.split("/")[0] for r in _at_line(verified, call, "call_pre")] \
        == ["tier3"]
    ran = _run(source, [VIOLATING])
    assert ran.trap is not None


READ_BACKS = {
    "array_literal": (
        "let @Array<Tuple<Small, Int>> = [mk(@Int.0)];",
        "match @Array<Tuple<Small, Int>>.0[0] { Tuple(@Int, @Int) -> @Int.1 }"),
    "map_insert": (
        "let @Map<Int, Tuple<Small, Int>> = "
        "map_insert(map_new(), 1, mk(@Int.0));",
        "match map_get(@Map<Int, Tuple<Small, Int>>.0, 1) "
        "{ Some(Tuple(@Int, @Int)) -> @Int.1, None -> 0 }"),
    "array_append": (
        "let @Array<Tuple<Small, Int>> = "
        "array_append([Tuple(1, 0)], mk(@Int.0));",
        "match @Array<Tuple<Small, Int>>.0[1] { Tuple(@Int, @Int) -> @Int.1 }"),
}


@pytest.mark.parametrize("store", list(READ_BACKS))
def test_repro_read_back_from_a_store(store: str) -> None:
    """Class line 6: an `ensures` over a component read back from an array
    literal, a `map_insert` value or an `array_append` element at a refined
    component type was proved from the read-back's declared type, which only
    the store's narrowing establishes.  Now Tier 3 (E534)."""
    let, read = READ_BACKS[store]
    source = SMALL + textwrap.dedent(f"""\
        private fn mk(@Int -> @Tuple<Int, Int>)
          requires(true)
          ensures(true)
          effects(pure)
        {{
          Tuple(@Int.0, 0)
        }}

        public fn go(@Int -> @Int)
          requires(true)
          ensures(@Int.result < 10)
          effects(pure)
        {{
          {let}
          {read}
        }}
        """)
    verified = _verify(source)
    ensures = _line(source, "ensures(@Int.result < 10)")
    assert _at_line(verified, ensures, "ensures") == ["tier3/E534"]
    if store == "array_literal":
        # The Tier 3 note says whose fact it is: a narrowing in this very
        # function, not a disclosed call.
        [note] = [d for d in verified.warnings if d.error_code == "E534"]
        assert "a narrowing in this function" in note.rationale, note.rationale


POS_MK_OPTION = textwrap.dedent("""\
    type Pos = { @Int | @Int.0 > 0 };

    private fn mk(@Int -> @Option<Int>)
      requires(true)
      ensures(true)
      effects(pure)
    {
      Some(@Int.0)
    }

    """)


def test_repro_a_handle_value_whose_leaves_narrow_is_narrowed() -> None:
    """A `handle` whose value a narrowing takes: the requirement is handed
    down to the clause's and the body's leaves, and the handle's own term is
    a stand-in that holds neither by occurrence, so only the join's record
    carries the narrowing to the reader after it.  The leaves are `Option`
    payloads, whose rows no check covers, so the `ensures` the reader's fact
    proves is Tier 3 (E534), and each leaf's narrowing discloses (E506)."""
    source = POS_MK_OPTION + textwrap.dedent("""\
        public fn go(@Int -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          let @Option<Pos> = handle[Exn<Int>] { throw(@Int) -> mk(@Int.0) } in { mk(@Int.0) };
          match @Option<Pos>.0 { Some(@Int) -> @Int.0, None -> 1 }
        }
        """)
    verified = _verify(source)
    let = _line(source, "let @Option<Pos> = handle[Exn<Int>] "
                        "{ throw(@Int) -> mk(@Int.0) } in { mk(@Int.0) };")
    assert _at_line(verified, let) == ["tier3_unguarded/E506"] * 2
    ensures = _line(source, "ensures(@Int.result > 0)")
    assert _at_line(verified, ensures, "ensures") == ["tier3/E534"]


def test_repro_a_clause_binder_the_walk_cannot_read_is_narrowed() -> None:
    """A `let` narrowing inside a handler clause binds a stand-in (the
    clause's parameter does not translate), and the stand-in is the
    narrowed value: the `Option` payload's row is unchecked, so the `@Nat`
    narrowing the reader's fact would prove is Tier 3, never `verified`."""
    source = POS_MK_OPTION + textwrap.dedent("""\
        public fn go(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          handle[Exn<Option<Int>>] {
            throw(@Option<Int>) -> {
              let @Option<Pos> = @Option<Int>.0;
              match @Option<Pos>.0 {
                Some(@Int) -> {
                  let @Nat = @Int.0;
                  nat_to_int(@Nat.0)
                },
                None -> 1
              }
            }
          } in {
            throw(mk(@Int.0))
          }
        }
        """)
    verified = _verify(source)
    let = _line(source, "let @Option<Pos> = @Option<Int>.0;")
    assert _at_line(verified, let) == ["tier3_unguarded/E506"]
    nat = _line(source, "let @Nat = @Int.0;")
    assert _at_line(verified, nat, "nat_bind") == ["tier3"]


def test_a_built_in_over_a_call_on_an_unestablished_narrowing_is_not_proved(
) -> None:
    """A call's result over a narrowed value is NOT established by the
    callee's return type: the callee's guarantee holds under what it assumed
    of its parameters, and `idp` hands back the unchecked argument it was
    passed (W155; this test pinned the `ensures` `verified` before, a false
    proof: `go(0)` violates it).  So an array literal holding the result
    holds an unestablished value, and the `ensures` its reader proves is not
    Tier 1."""
    source = POS_MK_OPTION + textwrap.dedent("""\
        private fn idp(@Option<Pos>, @Int -> @Option<Pos>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          if @Int.0 > 3 then { @Option<Pos>.0 } else { Some(7) }
        }

        public fn go(@Int -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          let @Option<Pos> = mk(@Int.0);
          let @Array<Option<Pos>> = [idp(@Option<Pos>.0, @Int.0)];
          match @Array<Option<Pos>>.0[0] { Some(@Int) -> @Int.0, None -> 1 }
        }
        """)
    verified = _verify(source)
    assert _at_line(verified, _line(source, "let @Option<Pos> = mk(@Int.0);")) \
        == ["violated/E505"]
    ensures = _line(source, "ensures(@Int.result > 0)")
    assert "verified" not in _at_line(verified, ensures, "ensures")


# The established twin: a narrowing code generation checks (a `Nat`
# payload) or the context proves (a `requires` over the parameter).
_ESTABLISHED_OVER_A_CALL = {
    # name: (the payload type, the ensures, go's requires, the narrowed
    #        value, the narrowing's row kind and status)
    "checked": ("Nat", "@Int.result >= 0", "true", "mk(@Int.0)",
                "nat_bind", "tier3"),
    "proved": ("Pos", "@Int.result > 0", "@Int.0 > 0", "Some(@Int.0)",
               "refine_bind", "verified"),
}


@pytest.mark.parametrize("narrowing", sorted(_ESTABLISHED_OVER_A_CALL))
def test_a_built_in_over_a_call_on_an_established_narrowing_keeps_its_fact(
        narrowing: str) -> None:
    """Over a narrowing that is established (checked, or proved), the call's
    result is no unestablished value: the reader of the array literal's
    element keeps its fact and the `ensures` stays `verified`."""
    ty, ens, pre, value, kind, row = _ESTABLISHED_OVER_A_CALL[narrowing]
    source = POS_MK_OPTION + textwrap.dedent(f"""\
        private fn idp(@Option<{ty}>, @Int -> @Option<{ty}>)
          requires(true)
          ensures(true)
          effects(pure)
        {{
          if @Int.0 > 3 then {{ @Option<{ty}>.0 }} else {{ Some(7) }}
        }}

        public fn go(@Int -> @Int)
          requires({pre})
          ensures({ens})
          effects(pure)
        {{
          let @Option<{ty}> = {value};
          let @Array<Option<{ty}>> = [idp(@Option<{ty}>.0, @Int.0)];
          match @Array<Option<{ty}>>.0[0] {{ Some(@Int) -> @Int.0, None -> 1 }}
        }}
        """)
    verified = _verify(source)
    let = _line(source, f"let @Option<{ty}> = {value};")
    assert _at_line(verified, let, kind) == [row]
    assert _at_line(verified, _line(source, f"ensures({ens})"), "ensures") \
        == ["verified"]


# =====================================================================
# What stays: the shapes the rule leaves at Tier 1
# =====================================================================


def test_a_reader_of_a_parameter_at_its_own_type_keeps_its_fact() -> None:
    """A slot whose type its producer established (a parameter declared at
    the refined type) is no narrowing: its reader's fact proves the
    `ensures`, as before."""
    source = SMALL + textwrap.dedent("""\
        public fn go(@Tuple<Small, Int> -> @Int)
          requires(true)
          ensures(@Int.result < 10)
          effects(pure)
        {
          match @Tuple<Small, Int>.0 { Tuple(@Int, @Int) -> @Int.1 }
        }
        """)
    verified = _verify(source)
    assert verified.ok
    assert _at_line(verified, _line(source, "ensures(@Int.result < 10)"), "ensures") == ["verified"]


def test_a_proved_narrowing_still_proves_its_readers() -> None:
    """A narrowing the context proves (a `requires` over the component) is
    `verified` without the fact, and what its reader proves stays Tier 1:
    the premises that prove the narrowing are in the reader's context."""
    source = SMALL + textwrap.dedent("""\
        private fn inner(@Tuple<Int, Int> -> @Int)
          requires(match @Tuple<Int, Int>.0 { Tuple(@Int, @Int) -> @Int.1 < 10 })
          ensures(@Int.result < 10)
          effects(pure)
        {
          let @Tuple<Small, Int> = @Tuple<Int, Int>.0;
          match @Tuple<Small, Int>.0 { Tuple(@Int, @Int) -> @Int.1 }
        }

        public fn go(@Int -> @Int)
          requires(@Int.0 < 10)
          ensures(true)
          effects(pure)
        {
          inner(Tuple(@Int.0, 0))
        }
        """)
    verified = _verify(source)
    let = _line(source, "let @Tuple<Small, Int> = @Tuple<Int, Int>.0;")
    assert _at_line(verified, let) == ["verified"]
    assert _at_line(verified, _line(source, "ensures(@Int.result < 10)"), "ensures") == ["verified"]


POS = "type Pos = { @Int | @Int.0 > 0 };\n\n"

CHECKED_AFTER_READER = {
    # name: (the function's ensures, its tail over the component @Int.0,
    #        the kind of the record the reader's fact proves)
    "ensures": ("ensures(@Int.result > 0)", "@Int.0", "ensures"),
    "divisor": ("ensures(true)", "100 / @Int.0", "div_zero"),
    "nat": ("ensures(true)", "{ let @Nat = @Int.0; nat_to_int(@Nat.0) }",
            "nat_bind"),
}


def _checked_narrowing(shape: str, ensures: str, tail: str) -> str:
    refined, base, reader = {
        "tuple": ("Tuple<Pos, Int>", "Tuple<Int, Int>",
                  "match @Tuple<Pos, Int>.0 { Tuple(@Int, @Int) -> @Int.1 }"),
        "option": ("Option<Pos>", "Option<Int>",
                   "match @Option<Pos>.0 { Some(@Int) -> @Int.0, None -> 1 }"),
    }[shape]
    return POS + (
        f"type MkT = fn(Int -> {base}) effects(pure);\n\n"
        "public fn go(@MkT, @Int -> @Int)\n"
        f"  requires(true)\n  {ensures}\n  effects(pure)\n{{\n"
        f"  let @{refined} = apply_fn(@MkT.0, @Int.0);\n"
        f"  let @Int = {reader};\n"
        f"  {tail}\n}}\n")


@pytest.mark.parametrize("obligation", list(CHECKED_AFTER_READER))
def test_repro_a_tuple_let_narrowing_withholds_its_readers_fact_rule_2(
        obligation: str) -> None:
    """Rule 2 (spec §2.6.5): a refined tuple component at a `let` is no
    position code generation checks, so the narrowing, over a value the
    solver cannot read, is disclosed (E506, `tier3_unguarded`) and
    establishes nothing.  An obligation after the reader that the reader's
    fact would prove is Tier 3, as it is for the same reader over an
    `Option` payload, whose row no check covers either."""
    ensures, tail, kind = CHECKED_AFTER_READER[obligation]
    source = _checked_narrowing("tuple", ensures, tail)
    verified = _verify(source)
    let = _line(source, "let @Tuple<Pos, Int> = apply_fn(@MkT.0, @Int.0);")
    assert _at_line(verified, let) == ["tier3_unguarded/E506"]
    line = _line(source, ensures if kind == "ensures" else tail)
    assert [r.split("/")[0] for r in _at_line(verified, line, kind)] \
        == ["tier3"]
    payload = _checked_narrowing("option", ensures, tail)
    verified = _verify(payload)
    line = _line(payload, ensures if kind == "ensures" else tail)
    assert [r.split("/")[0] for r in _at_line(verified, line, kind)] \
        == ["tier3"]


LET_TUPLE_NO_READER = POS + textwrap.dedent("""\
    type MkT = fn(Int -> Tuple<Int, Int>) effects(pure);

    public fn go(@MkT, @Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      let @Tuple<Pos, Int> = apply_fn(@MkT.0, @Int.0);
      1
    }

    public fn main_go(@Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      go(fn(@Int -> @Tuple<Int, Int>) effects(pure) { Tuple(@Int.0, 0) },
        @Int.0)
    }
    """)


def _unanswered(verified: pipeline.Verified, source: str,
                fn: str, line: int) -> list[str]:
    ran = pipeline.run(source, fn, [0], file=FILE)
    assert ran.compiled is not None
    return [m.kind for m in reconcile(
        verified.result, ran.compiled.result,
        program=verified.checked.program, file=verified.checked.file)
        if m.line == line]


def test_repro_a_let_tuple_component_is_disclosed_rule_2() -> None:
    """Rule 2 (spec §2.6.5): a refined tuple component is checked only
    where code generation takes the tuple apart (a function's or a
    closure's entry, a return, an `apply_fn` argument).  At a `let` no
    check is emitted, so its row is disclosed (E506, `tier3_unguarded`),
    with nothing for the join to miss (no E541), and the run delivers the
    violating tuple, which is what the disclosure says."""
    source = LET_TUPLE_NO_READER
    verified = _verify(source)
    let = _line(source, "let @Tuple<Pos, Int> = apply_fn(@MkT.0, @Int.0);")
    assert _at_line(verified, let) == ["tier3_unguarded/E506"]
    assert _unanswered(verified, source, "main_go", let) == []
    assert pipeline.run(source, "main_go", [0], file=FILE).value == 1


def test_repro_a_disclosed_tuple_let_withholds_its_readers_fact_rule_2(
) -> None:
    """Rule 2: the `let` of a refined tuple component is disclosed, not
    checked, so it establishes nothing: the fact its reader reads is
    withheld, and the `ensures` it would prove is Tier 3, not `verified`.
    No E541 stands at the `let`."""
    source = _checked_narrowing("tuple", "ensures(@Int.result > 0)", "@Int.0")
    caller = source + textwrap.dedent("""
        public fn main_go(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          go(fn(@Int -> @Tuple<Int, Int>) effects(pure) { Tuple(@Int.0, 0) },
            @Int.0)
        }
        """)
    verified = _verify(caller)
    let = _line(caller, "let @Tuple<Pos, Int> = apply_fn(@MkT.0, @Int.0);")
    assert _at_line(verified, let) == ["tier3_unguarded/E506"]
    ensures = _line(caller, "ensures(@Int.result > 0)")
    assert [r.split("/")[0] for r in _at_line(verified, ensures, "ensures")] \
        == ["tier3"]
    assert _unanswered(verified, caller, "main_go", let) == []


COMPONENT_OF_A_NARROWING = {
    # shape: (the composite at Pos, its base, the reader of the component,
    #         the `@Nat` narrowing's status)
    "tuple": ("Tuple<Pos, Int>", "Tuple<Int, Int>",
              "match @Tuple<Pos, Int>.0 { Tuple(@Int, @Int) -> @Int.1 }",
              "tier3"),
    "nested": ("Tuple<Tuple<Pos, Int>, Int>", "Tuple<Tuple<Int, Int>, Int>",
               "match @Tuple<Tuple<Pos, Int>, Int>.0 "
               "{ Tuple(Tuple(@Int, @Int), _) -> @Int.1 }",
               "tier3"),
    "option": ("Option<Pos>", "Option<Int>",
               "match @Option<Pos>.0 { Some(@Int) -> @Int.0, None -> 1 }",
               "tier3"),
    "data": ("Wrap<Pos>", "Wrap<Int>",
             "match @Wrap<Pos>.0 { W(@Int) -> @Int.0 }", "tier3"),
}


@pytest.mark.parametrize("shape", list(COMPONENT_OF_A_NARROWING))
def test_repro_a_component_narrowing_is_not_the_composites_own(
        shape: str) -> None:
    """A `@Nat` narrowing of a component read off a narrowed composite is
    a narrowing of its own value, not of the composite: the composite's
    reader facts are kept from the composite's own query only.  It reads
    them as any query does: Tier 3 where they are withheld, which at a `let`
    is every shape (a payload, and by rule 2, spec §2.6.5, a tuple
    component, which no check at a `let` covers), and never refuted (E503)
    for a value the composite's type bounds."""
    refined, base, reader, status = COMPONENT_OF_A_NARROWING[shape]
    source = POS + "public data Wrap<T> { W(T) }\n\n" + (
        f"public fn go(@{base} -> @Nat)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
        f"  let @{refined} = @{base}.0;\n"
        f"  let @Int = {reader};\n"
        "  let @Nat = @Int.0;\n"
        "  @Nat.0\n}\n")
    verified = _verify(source)
    let = _line(source, f"let @{refined} = @{base}.0;")
    assert _at_line(verified, let) == ["violated/E505"]
    nat = _line(source, "let @Nat = @Int.0;")
    assert [r.split("/")[0] for r in _at_line(verified, nat, "nat_bind")] \
        == [status]


CLAUSE_LET_1542 = POS + textwrap.dedent("""\
    private fn mk(@Int -> @Tuple<Int, Int>)
      requires(true)
      ensures(true)
      effects(pure)
    {
      Tuple(@Int.0, 0)
    }

    public fn go(@Int -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      handle[Exn<Tuple<Int, Int>>] {
        throw(@Tuple<Int, Int>) -> {
          let @Tuple<Pos, Int> = @Tuple<Int, Int>.0;
          match @Tuple<Pos, Int>.0 {
            Tuple(@Int, @Int) -> {
              let @Nat = @Int.1;
              nat_to_int(@Nat.0)
            }
          }
        }
      } in {
        throw(mk(@Int.0))
      }
    }
    """)


def test_a_clause_let_the_table_discloses_rule_2() -> None:
    """A `let` narrowing of a tuple component inside a handler clause: by
    rule 2 (spec §2.6.5) the table lists its row as disclosed (E506,
    `tier3_unguarded`), which is what code generation does (no check, so
    no E541 at the `let`).  It establishes nothing, so the `@Nat`
    narrowing its reader's fact would prove is Tier 3, not `verified`.
    Until rule 2 the table listed the row as checked and the join reported
    E541 (#1542's line 2)."""
    verified = _verify(CLAUSE_LET_1542)
    let = _line(CLAUSE_LET_1542, "let @Tuple<Pos, Int> = @Tuple<Int, Int>.0;")
    assert _at_line(verified, let) == ["tier3_unguarded/E506"]
    nat = _line(CLAUSE_LET_1542, "let @Nat = @Int.1;")
    assert _at_line(verified, nat, "nat_bind") == ["tier3"]
    ran = _run(CLAUSE_LET_1542, [5])
    assert ran.compiled is not None
    unanswered = [m for m in reconcile(
        verified.result, ran.compiled.result,
        program=verified.checked.program, file=verified.checked.file)
        if m.line == let]
    assert unanswered == []


def _nested_builtins(depth: int, narrow: bool) -> str:
    expr = "@Int.0"
    for i in range(depth):
        expr = f"max({expr}, {i})"
    let = "  let @Tuple<Small, Int> = @Tuple<Int, Int>.0;\n" if narrow else ""
    return SMALL + (
        "public fn go(@Tuple<Int, Int>, @Int -> @Int)\n"
        "  requires(true)\n  ensures(true)\n  effects(pure)\n{\n"
        f"{let}  {expr}\n}}\n")


def _translations(source: str, monkeypatch: pytest.MonkeyPatch) -> int:
    from vera.smt import SmtContext
    original = SmtContext.translate_expr
    count = [0]

    def counting(self: Any, *args: Any, **kwargs: Any) -> Any:
        count[0] += 1
        return original(self, *args, **kwargs)

    with monkeypatch.context() as m:
        m.setattr(SmtContext, "translate_expr", counting)
        pipeline.verify(source, file=FILE)
    return count[0]


def test_repro_a_built_in_over_its_parts_is_translated_once(
        monkeypatch: pytest.MonkeyPatch) -> None:
    """Asking whether a built-in's part holds a narrowed value reads the
    term the translation already made of it: a part is translated again
    only where the translation did not reach it.  Re-translating every part
    ran the hook on the part's own parts, so a chain of nested built-ins in
    a function with a narrowing cost twice as much at each level (16 levels
    of `max` took seconds where the same chain without the narrowing takes
    a fraction of one).  Counted, not timed: doubling the depth at most
    doubles the translations, give or take the function's fixed part."""
    shallow = _translations(_nested_builtins(8, narrow=True), monkeypatch)
    deep = _translations(_nested_builtins(16, narrow=True), monkeypatch)
    assert deep <= 2.5 * shallow, (shallow, deep)


# =====================================================================
# The class instrument
# =====================================================================


@pytest.mark.parametrize("cell", CELLS, ids=[c.id for c in CELLS])
def test_no_narrowing_is_proved_from_its_readers_fact(cell: Cell) -> None:
    """The rule, per cell (see the module docstring)."""
    made = _program(cell)
    assert made is not None
    source, site = made
    verified = _verify(source)
    line = _line(source, site)
    records = _site_records(verified, source, line, cell.position)
    if cell.position in NO_RECORD_1542:
        # #1542's: a binder below the head has no record yet.
        assert records == [], records
    else:
        assert records, f"no record at line {line}"
        assert "verified" not in records, records
    ran = _run(source, [VIOLATING])
    if ran.trap is None and cell.position not in NO_RECORD_1542:
        # Delivered: verification refused the program, disclosed the
        # narrowing (E506), or claimed a check the module does not hold,
        # which `vera verify` reports as the E541 error (#1542's loud line).
        disclosed = any(r.startswith("tier3_unguarded") or r.endswith("/E506")
                        for r in records)
        assert ran.compiled is not None
        unanswered = [m for m in reconcile(
            verified.result, ran.compiled.result,
            program=verified.checked.program, file=verified.checked.file)
            if m.line == line]
        assert not verified.ok or disclosed or unanswered, (
            records, [d.error_code for d in verified.warnings])


@pytest.mark.parametrize("cell", CELLS, ids=[c.id for c in CELLS])
def test_every_proof_survives_with_the_readers_facts_withheld(
    cell: Cell, withheld_readers: None,
) -> None:
    """The differential: a record of the cell's program `verified` only
    because a reader's fact was assumed rests on a check the run executes
    before it.  The fact is established only where the narrowing's row is
    checked, and that check runs where the value takes the type: at the
    violating value the run traps.  No narrowing record at the site is
    among them (its own query never reads the fact)."""
    made = _program(cell)
    assert made is not None
    source, site = made
    without = _verified_records(_verify(source))
    with_facts = _verified_with_facts(source)
    extra = sorted(with_facts - without)
    if not extra:
        return
    line = _line(source, site)
    assert not [r for r in extra if r[0] == "refine_bind" and r[1] == line], \
        extra
    ran = _run(source, [VIOLATING])
    assert ran.trap is not None, extra


def _verified_with_facts(source: str) -> set[tuple[str, int, int]]:
    """The verified records with the readers' facts in force: the
    fixture's patch is lifted for this one verification."""
    patched = verifier_mod.ContractVerifier._subpattern_source_facts
    verifier_mod.ContractVerifier._subpattern_source_facts = _ORIGINAL_READER
    try:
        return _verified_records(_verify(source))
    finally:
        verifier_mod.ContractVerifier._subpattern_source_facts = patched


_ORIGINAL_READER = verifier_mod.ContractVerifier._subpattern_source_facts


def test_the_matrix_is_the_product() -> None:
    """Every product is a cell bar the destructure reader of a shape with no
    tuple to destructure, and every id names one product."""
    ids = [c.id for c in CELLS]
    assert len(ids) == len(set(ids))
    expected = sum(
        len(_orders(position, reader))
        for source, position, shape, reader, predicate in itertools.product(
            SOURCES, POSITIONS, SHAPES, READERS, PREDICATES)
        if not (reader == "destr" and SHAPES[shape].destr is None))
    assert len(ids) == expected == 4160


# =====================================================================
# The lineage of a term made from a narrowed one (W135's f1, f1b, the
# Option twin, f2, f2b).  A flow that makes a NEW term from a narrowed
# value (an array literal holding it, a `handle`'s stand-in whose leaves
# are it) still carries that narrowing: the narrowing's own query never
# reads a fact read off the new term, and a fact read off it is
# established no further than the narrowing is.
# =====================================================================

NEED = textwrap.dedent("""\
    private fn need(@Int -> @Int)
      requires(@Int.0 > 0)
      ensures(@Int.result == @Int.0)
      effects(pure)
    {
      @Int.0
    }

    """)


def _go(call: str) -> str:
    return textwrap.dedent(f"""\

        public fn go(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {{
          {call}
        }}
        """)


def test_repro_f1_a_narrowing_read_back_through_an_array_literal() -> None:
    """f1: the narrowed tuple is put in an array literal and read back by
    a `match` on `[0]`.  The literal's term is the reader's only owner; it
    was made from the tuple, so the `let`'s own query never reads its fact:
    refuted (E505), as with the reader on the slot.  Was disclosed (E506)."""
    source = POS + NEED + textwrap.dedent("""\
        private fn inner(@Tuple<Int, Int> -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Tuple<Pos, Int> = @Tuple<Int, Int>.0;
          let @Array<Tuple<Pos, Int>> = [@Tuple<Pos, Int>.0];
          match @Array<Tuple<Pos, Int>>.0[0] { Tuple(@Int, @Int) -> need(@Int.1) }
        }
        """) + _go("inner(Tuple(@Int.0, 0))")
    verified = _verify(source)
    let = _line(source, "let @Tuple<Pos, Int> = @Tuple<Int, Int>.0;")
    assert _at_line(verified, let) == ["violated/E505"]


def test_repro_f1b_an_array_read_back_whose_consumer_is_the_ensures() -> None:
    """f1 with the reader's consumer the function's own postcondition:
    the `let` is refuted (E505), never proved or disclosed from the fact
    read back through the literal.  Was disclosed (E506)."""
    source = POS + textwrap.dedent("""\
        private fn inner(@Tuple<Int, Int> -> @Int)
          requires(true)
          ensures(@Int.result > 0)
          effects(pure)
        {
          let @Tuple<Pos, Int> = @Tuple<Int, Int>.0;
          let @Array<Tuple<Pos, Int>> = [@Tuple<Pos, Int>.0];
          match @Array<Tuple<Pos, Int>>.0[0] { Tuple(@Int, @Int) -> @Int.1 }
        }
        """) + _go("inner(Tuple(@Int.0, 0))")
    verified = _verify(source)
    let = _line(source, "let @Tuple<Pos, Int> = @Tuple<Int, Int>.0;")
    assert _at_line(verified, let) == ["violated/E505"]


def test_repro_f1_option_twin_read_back_through_an_array_literal() -> None:
    """f1's `Option` twin: the payload row is unchecked, so the fact read
    back through the literal is withheld; it was offered to the `let`'s
    own second attempt (the literal's owner is not the `let`'s value) and
    the `let` disclosed (E506).  Its lineage keeps it out: E505."""
    source = POS + NEED + textwrap.dedent("""\
        private fn inner(@Option<Int> -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Option<Pos> = @Option<Int>.0;
          let @Array<Option<Pos>> = [@Option<Pos>.0];
          match @Array<Option<Pos>>.0[0] { Some(@Int) -> need(@Int.0), None -> 1 }
        }
        """) + _go("inner(Some(@Int.0))")
    verified = _verify(source)
    let = _line(source, "let @Option<Pos> = @Option<Int>.0;")
    assert _at_line(verified, let) == ["violated/E505"]


_F2_TAIL = textwrap.dedent("""\
      let @Option<Pos> = handle[Exn<Int>] { throw(@Int) -> @Option<Pos>.0 } in { @Option<Pos>.0 };
      match @Option<Pos>.0 {
        Some(@Int) -> {
          let @Nat = @Int.0 - 1;
          nat_to_int(@Nat.0)
        },
        None -> 1
      }
    }
    """)


def test_repro_f2_a_handle_whose_leaves_are_a_narrowed_slot() -> None:
    """f2: a `handle` whose clause and body leaves are a slot an unchecked
    payload narrowing typed.  The handle's term is a stand-in the leaves
    do not occur in; its leaves hold the narrowed value, so it is narrowed
    and unestablished, and the `@Nat` the reader's fact proves is Tier 3.
    Was `verified` (the fact had no owner, so it came in as established)."""
    source = POS + textwrap.dedent("""\
        private fn mk(@Int -> @Option<Int>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          Some(@Int.0)
        }

        public fn go(@Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Option<Pos> = mk(@Int.0);
        """) + textwrap.indent(_F2_TAIL, "  ")[2:]
    verified = _verify(source)
    nat = _line(source, "let @Nat = @Int.0 - 1;")
    assert _at_line(verified, nat, "nat_bind") == ["tier3"]


def test_repro_f2b_a_handle_over_an_apply_fn_narrowing() -> None:
    """f2 over `apply_fn`'s result, a program `vera verify` accepts: the
    `@Nat` is Tier 3, its check kept, never `verified`."""
    source = POS + textwrap.dedent("""\
        type MkO = fn(Int -> Option<Int>) effects(pure);

        public fn go(@MkO, @Int -> @Int)
          requires(true)
          ensures(true)
          effects(pure)
        {
          let @Option<Pos> = apply_fn(@MkO.0, @Int.0);
        """) + textwrap.indent(_F2_TAIL, "  ")[2:]
    verified = _verify(source)
    nat = _line(source, "let @Nat = @Int.0 - 1;")
    assert _at_line(verified, nat, "nat_bind") == ["tier3"]


# The coordinator's probes (W155): an unchecked narrowing of an opaque
# `apply_fn` result, disclosed (E506) in a program `vera verify` accepts,
# carried to the reader by a flow the lineage cannot follow.  Each was a
# false proof: the `@Nat` `verified`, and `main_go(0)` traps at its check.
_ACC_DECLS = {
    "generic": textwrap.dedent("""\
        private forall<T> fn ident(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @T.0
        }

        """),
    "pass": textwrap.dedent("""\
        private fn pass(@Option<Pos> -> @Option<Pos>)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @Option<Pos>.0
        }

        """),
    "closure": "type MkS = fn(Int -> Option<Pos>) effects(pure);\n\n",
}
_ACC_BODY = {
    "generic": ("let @Option<Pos> = apply_fn(@MkO.0, @Int.0);",
                "ident(@Option<Pos>.0)"),
    "pass": ("let @Option<Pos> = apply_fn(@MkO.0, @Int.0);",
             "pass(@Option<Pos>.0)"),
    "state": ("let @Option<Pos> = apply_fn(@MkO.0, @Int.0);\n"
              "let @Option<Pos> = handle[State<Option<Pos>>](@Option<Pos> = "
              "Some(1)) { get(@Unit) -> { resume(@Option<Pos>.0) }, "
              "put(@Option<Pos>) -> { resume(()) } } in "
              "{ put(@Option<Pos>.0); get(()) };", "@Option<Pos>.0"),
    "closure": ("let @Option<Pos> = apply_fn(@MkO.0, @Int.0);\n"
                "let @MkS = fn(@Int -> @Option<Pos>) effects(pure) "
                "{ @Option<Pos>.0 };", "apply_fn(@MkS.0, 0)"),
    "a_norow": ("let @Option<Pos> = handle[Exn<Option<Pos>>] "
                "{ throw(@Option<Pos>) -> @Option<Pos>.0 } in "
                "{ let @Option<Pos> = apply_fn(@MkO.0, @Int.0); "
                "throw(@Option<Pos>.0) };", "@Option<Pos>.0"),
}


def _acc_program(probe: str) -> str:
    """One probe: `go` narrows an `apply_fn` result and reads it back."""
    narrow, scrut = _ACC_BODY[probe]
    extra = ", @Option<Pos>" if probe == "a_norow" else ""
    arg = ", None" if probe == "a_norow" else ""
    body = textwrap.indent(narrow, "  ")
    return (POS + "type MkO = fn(Int -> Option<Int>) effects(pure);\n\n"
            + _ACC_DECLS.get(probe, "")
            + f"public fn go(@MkO{extra}, @Int -> @Int)\n  requires(true)\n"
            + "  ensures(true)\n  effects(pure)\n{\n" + body + "\n"
            + f"  match {scrut} {{\n    Some(@Int) -> {{\n"
            + "      let @Nat = @Int.0 - 1;\n      nat_to_int(@Nat.0)\n"
            + "    },\n    None -> 1\n  }\n}\n\n"
            + "public fn main_go(@Int -> @Int)\n  requires(true)\n"
            + "  ensures(true)\n  effects(pure)\n{\n"
            + "  go(fn(@Int -> @Option<Int>) effects(pure) { Some(@Int.0) }"
            + f"{arg}, @Int.0)\n}}\n")


def _acc_check(probe: str) -> None:
    source = _acc_program(probe)
    verified = _verify(source)
    assert verified.ok, probe
    nat = _line(source, "let @Nat = @Int.0 - 1;")
    assert _at_line(verified, nat, "nat_bind") == ["tier3"], probe
    ran = pipeline.run(source, "main_go", [0], file=FILE)
    assert ran.trap is not None, (probe, ran.value)
    assert str(ran.trap).startswith(_OWN_CHECK["nat"]), (probe, str(ran.trap))


def test_repro_acc_generic_a_generic_call_carries_the_narrowing() -> None:
    _acc_check("generic")


def test_repro_acc_pass_a_non_generic_call_carries_the_narrowing() -> None:
    """The reason no call is exempt: `pass`'s own return row establishes
    nothing about the unchecked argument it returns."""
    _acc_check("pass")


def test_repro_acc_state_a_get_carries_the_put_narrowing() -> None:
    _acc_check("state")


def test_repro_acc_closure_an_apply_fn_carries_the_capture() -> None:
    _acc_check("closure")


def test_repro_a_norow_a_clause_binder_carries_the_thrown_narrowing() -> None:
    _acc_check("a_norow")


# =====================================================================
# The class instrument for the lineage (#1897, W145).  Every flow that
# carries a narrowed value to a reader in the same function: the fact the
# reader takes off the value's type is tied to the narrowing that typed it,
# whatever the flow made of the value on the way.
#
# Axes: FLOW (how the value reaches the reader) x SHAPE (where the
# refinement sits) x CONSUMER (what reads the fact) x NARROWING (u: a `let`
# over a parameter the solver refutes, no check; c: a `Nat` component, whose
# check code generation emits; p: a constructor over a parameter the
# function's `requires` establishes).  Each cell is a differential: `vera
# verify` (the narrowing's row, the consumer's obligation, and the row again
# with every reader fact withheld) against `vera run` of `go` at a violating
# input (-3, not the zero a stand-in takes) and a satisfying one (7).
#
# 1. No false Tier 1: under (u) the consumer is not `verified`, unless the
#    violating run is stopped by a check on the flow before the consumer's
#    own (a closure's return check: the flow established the value).
# 2. No demotion: under (u) the narrowing's row is what it is with every
#    reader fact withheld, and `violated` (E505) wherever it is the `let`
#    the direct flow writes (the clause-leaf flow narrows a clause binder the
#    solver cannot read: disclosed, E506, with or without the reader).
# 3. Nothing withheld that holds: under (c) and (p) the consumer is
#    `verified`, or as it is on the direct flow.
# 4. The run agrees: a violating input never returns normally past a
#    `verified` consumer; and the satisfying input returns the value the
#    flow carried (so the template carries it at all).
#
# No flow is refused by the language: every cell type-checks.  The cells
# that fail an assertion are strict xfails named in FLOW_MEMBERS.
# =====================================================================

FLOW_VIOLATING = -3
FLOW_SATISFYING = 7


@dataclass(frozen=True)
class FlowShape:
    wrap: str      # the type, over {x}
    ctor: str      # a value, over {e}
    lit: str       # a literal the refinement proves
    pattern: str   # the reader's pattern
    ref: str       # the refined component, inside the arm
    other: str     # the other arms


FLOW_SHAPES = {
    "tuple": FlowShape("Tuple<{x}, Int>", "Tuple({e}, 0)", "Tuple(1, 0)",
                       "Tuple(@Int, @Int)", "@Int.1", ""),
    "option": FlowShape("Option<{x}>", "Some({e})", "Some(1)",
                        "Some(@Int)", "@Int.0", ",\n    None -> 1"),
    "nested": FlowShape("Tuple<Tuple<{x}, Int>, Int>", "Tuple(Tuple({e}, 0), 0)",
                        "Tuple(Tuple(1, 0), 0)", "Tuple(Tuple(@Int, @Int), @Int)",
                        "@Int.2", ""),
}
FLOWS = ("direct", "array_literal", "array_append", "map", "if_join",
         "match_join", "block_tail", "handle_body", "clause_outer",
         "clause_leaf", "throw_outer", "throw_inner", "throw_inner_noouter",
         "closure", "generic", "state", "pass")
# The second source of an unchecked narrowing (W155): an opaque `apply_fn`
# result, whose row is disclosed (E506) and which `vera verify` accepts,
# over every flow that held a soundness member and the direct control.
FLOW_SOURCES = ("param", "apply")
APPLY_FLOWS = ("direct", "throw_inner", "throw_inner_noouter", "closure",
               "generic", "state", "pass")
FLOW_CONSUMERS = {"requires": "call_pre", "nat": "nat_bind", "ensures": "ensures"}
NARROWINGS = ("u", "c", "p")

# The consumer's own check, as the run names its trap.
_OWN_CHECK = {"requires": "Precondition violation in need(",
              "nat": "Negative value bound into a @Nat slot",
              "ensures": "Postcondition violation in inner("}

# The 38 soundness members W145 found (a thrown value, a generic call's
# result, a `State` `get`, an `Option` closure result) are closed by the
# minted-term rule (`ContractVerifier._note_minted`, W155); every member
# left is an incompleteness.
_JOIN_NAT = ("a checked `Nat` component through a join with a literal leaf: "
             "the reader's fact is lost entirely, the consumer is REFUTED "
             "(E501/E503/postcondition) though it holds; the same at main")
_CLOSURE_ENSURES = ("an `ensures` over a closure's `apply_fn` result is "
                    "Tier 3 (E522, body undecidable) where the direct flow "
                    "proves it; the same at main")


def _flow_members() -> dict[str, str]:
    members: dict[str, str] = {}
    for shape, consumer in itertools.product(FLOW_SHAPES, FLOW_CONSUMERS):
        for flow in ("if_join", "match_join"):
            members[f"{flow}-{shape}-{consumer}-c"] = "incompleteness: " + _JOIN_NAT
    for shape, narrowing in itertools.product(FLOW_SHAPES, ("c", "p")):
        members[f"closure-{shape}-ensures-{narrowing}"] = (
            "incompleteness: " + _CLOSURE_ENSURES)
    return members


FLOW_MEMBERS = _flow_members()


@dataclass(frozen=True)
class FlowCell:
    flow: str
    shape: str
    consumer: str
    narrowing: str
    source: str = "param"

    @property
    def id(self) -> str:
        tail = "" if self.source == "param" else f"-{self.source}"
        return f"{self.flow}-{self.shape}-{self.consumer}-{self.narrowing}{tail}"


def _flow_statements(flow: str, s: str, lit: str, narrow: str,
                     leaf: str) -> tuple[list[str], str, str]:
    """The statements that carry the narrowed value, the reader's
    scrutinee, and the extra declarations the flow needs."""
    slot = f"@{s}.0"
    if flow == "direct":
        return [narrow], slot, ""
    if flow in ("array_literal", "array_append"):
        made = f"[{slot}]" if flow == "array_literal" else f"array_append([], {slot})"
        return [narrow, f"let @Array<{s}> = {made};"], f"@Array<{s}>.0[0]", ""
    if flow == "map":
        return ([narrow, f"let @Map<Int, {s}> = map_insert(map_new(), 0, {slot});"],
                f"map_get(@Map<Int, {s}>.0, 0)", "")
    joined = {
        "if_join": f"if true then {{ {slot} }} else {{ {lit} }}",
        "match_join": f"match 0 {{ 0 -> {slot}, _ -> {lit} }}",
        "block_tail": f"{{ let @Bool = true; {slot} }}",
        "handle_body": f"handle[Exn<Int>] {{ throw(@Int) -> {lit} }} in {{ {slot} }}",
        "clause_outer": f"handle[Exn<Int>] {{ throw(@Int) -> {slot} }} in {{ throw(1) }}",
        "throw_outer": f"handle[Exn<{s}>] {{ throw(@{s}) -> {slot} }} in {{ throw({slot}) }}",
        "state": (f"handle[State<{s}>](@{s} = {lit}) {{ get(@Unit) -> {{ resume(@{s}.0) }}, "
                  f"put(@{s}) -> {{ resume(()) }} }} in {{ put({slot}); get(()) }}"),
    }
    if flow in joined:
        return [narrow, f"let @{s} = {joined[flow]};"], slot, ""
    if flow == "clause_leaf":
        return [f"let @{s} = {leaf};"], slot, ""
    if flow in ("throw_inner", "throw_inner_noouter"):
        outer = [f"let @{s} = {lit};"] if flow == "throw_inner" else []
        return outer + [f"let @{s} = handle[Exn<{s}>] {{ throw(@{s}) -> {slot} }} in {{",
                        f"  {narrow}", f"  throw({slot})", "};"], slot, ""
    if flow == "closure":
        return ([narrow, f"let @MkS = fn(@Int -> @{s}) effects(pure) {{ {slot} }};"],
                "apply_fn(@MkS.0, 0)", f"type MkS = fn(Int -> {s}) effects(pure);\n\n")
    if flow == "pass":
        # A NON-generic pass-through: its return type is the narrowed one,
        # and it returns the argument it was handed (W155).
        return [narrow], f"pass({slot})", textwrap.dedent(f"""\
            private fn pass(@{s} -> @{s})
              requires(true)
              ensures(true)
              effects(pure)
            {{
              @{s}.0
            }}

            """)
    assert flow == "generic", flow
    return [narrow], f"ident({slot})", textwrap.dedent("""\
        private forall<T> fn ident(@T -> @T)
          requires(true)
          ensures(true)
          effects(pure)
        {
          @T.0
        }

        """)


def _flow_program(cell: FlowCell) -> tuple[str, str, str]:
    """The program, the narrowing's line text and the consumer's."""
    sh = FLOW_SHAPES[cell.shape]
    s = sh.wrap.format(x="Nat" if cell.narrowing == "c" else "Pos")
    base = sh.wrap.format(x="Int")
    if cell.narrowing == "p":
        param, pre, call = "@Int", "@Int.0 > 0", "inner(@Int.0)"
        narrow = f"let @{s} = {sh.ctor.format(e='@Int.0')};"
        leaf = (f"handle[Exn<Int>] {{ throw(@Int) -> {sh.ctor.format(e='@Int.1')} }} "
                "in { throw(@Int.0) }")
    elif cell.source == "apply":
        param, pre = "@MkO, @Int", "true"
        call = (f"inner(fn(@Int -> @{base}) effects(pure) "
                f"{{ {sh.ctor.format(e='@Int.0')} }}, @Int.0)")
        narrow = f"let @{s} = apply_fn(@MkO.0, @Int.0);"
        leaf = ""
    else:
        param, pre = f"@{base}", "true"
        call = f"inner({sh.ctor.format(e='@Int.0')})"
        narrow = f"let @{s} = @{base}.0;"
        leaf = f"handle[Exn<{base}>] {{ throw(@{base}) -> @{base}.0 }} in {{ throw(@{base}.0) }}"
    stmts, scrut, decls = _flow_statements(cell.flow, s, sh.lit, narrow, leaf)
    if cell.source == "apply":
        decls = f"type MkO = fn(Int -> {base}) effects(pure);\n\n" + decls
    narrow_line = stmts[0] if cell.flow == "clause_leaf" else narrow
    ge = ">=" if cell.narrowing == "c" else ">"
    ensures = "true"
    if cell.consumer == "requires":
        decls += textwrap.dedent(f"""\
            private fn need(@Int -> @Int)
              requires(@Int.0 {ge} 0)
              ensures(@Int.result == @Int.0)
              effects(pure)
            {{
              @Int.0
            }}

            """)
        body = f"need({sh.ref})"
        consumer = f"{sh.pattern} -> {body}"
    elif cell.consumer == "nat":
        bind = f"let @Nat = {sh.ref}{'' if cell.narrowing == 'c' else ' - 1'};"
        body, consumer = f"{{\n      {bind}\n      nat_to_int(@Nat.0)\n    }}", bind
    else:
        ensures = f"@Int.result {ge} 0"
        body, consumer = sh.ref, f"ensures({ensures})"
    arm = f"{sh.pattern} -> {body}{sh.other}"
    if cell.flow == "map":
        reader = (f"match {scrut} {{\n    Some(@{s}) -> match @{s}.0 {{\n    {arm}\n    }},\n"
                  "    None -> 1\n  }")
    else:
        reader = f"match {scrut} {{\n    {arm}\n  }}"
    lines = "\n".join(f"  {t}" for t in stmts)
    go_pre = "@Int.0 > 0" if cell.narrowing == "p" else "true"
    source = (POS + decls
              + f"private fn inner({param} -> @Int)\n  requires({pre})\n"
              + f"  ensures({ensures})\n  effects(pure)\n{{\n{lines}\n  {reader}\n}}\n\n"
              + f"public fn go(@Int -> @Int)\n  requires({go_pre})\n  ensures(true)\n"
              + f"  effects(pure)\n{{\n  {call}\n}}\n")
    return source, narrow_line, consumer


def _first_line(source: str, text: str) -> int:
    for n, ln in enumerate(source.splitlines(), 1):
        if ln.strip().startswith(text.strip()):
            return n
    raise AssertionError(f"no line {text!r}")


def _flow_verdicts(cell: FlowCell) -> tuple[list[str], list[str]]:
    """The narrowing's rows and the consumer's obligation, in `inner`."""
    source, narrow, consumer = _flow_program(cell)
    verified = _verify(source)
    at_narrow, at_consumer = _first_line(source, narrow), _first_line(source, consumer)
    inner = [o for o in verified.obligations if o.fn_name == "inner"]
    rows = sorted(_status(o) for o in inner if o.line == at_narrow
                  and o.kind in ("refine_bind", "nat_bind"))
    used = sorted(_status(o) for o in inner if o.line == at_consumer
                  and o.kind == FLOW_CONSUMERS[cell.consumer])
    assert used, (cell.id, "no consumer obligation")
    return rows, used


def _flow_run(source: str, arg: int) -> tuple[str, Any]:
    ran = pipeline.run(source, "go", [arg], file=FILE)
    assert ran.compiled is not None and ran.compiled.ok, (arg, "no compile")
    if ran.trap is not None:
        return "trap", str(ran.trap).splitlines()[0]
    return "ret", ran.value


FLOW_CELLS = [FlowCell(*p) for p in itertools.product(
    FLOWS, FLOW_SHAPES, FLOW_CONSUMERS, NARROWINGS)] + [
    FlowCell(flow, shape, consumer, "u", "apply")
    for flow, shape, consumer in itertools.product(
        APPLY_FLOWS, FLOW_SHAPES, FLOW_CONSUMERS)]


def _flow_param(cell: FlowCell) -> Any:
    reason = FLOW_MEMBERS.get(cell.id)
    marks = [pytest.mark.xfail(strict=True, reason=reason)] if reason else []
    return pytest.param(cell, id=cell.id, marks=marks)


def test_the_flow_matrix_is_the_product() -> None:
    """Every flow, shape, consumer and narrowing is a cell, every member
    names a cell, and the direct flow (the yardstick) has none."""
    ids = [c.id for c in FLOW_CELLS]
    assert len(ids) == len(set(ids)) == 17 * 3 * 3 * 3 + 7 * 3 * 3 == 522
    assert set(FLOW_MEMBERS) <= set(ids)
    assert {c.source for c in FLOW_CELLS} == set(FLOW_SOURCES)
    assert not [m for m in FLOW_MEMBERS if m.startswith("direct-")]


@pytest.mark.parametrize("cell", [_flow_param(c) for c in FLOW_CELLS])
def test_a_flow_keeps_the_narrowings_lineage(
        cell: FlowCell, monkeypatch: pytest.MonkeyPatch) -> None:
    source, _, _ = _flow_program(cell)
    rows, used = _flow_verdicts(cell)
    violating = _flow_run(source, FLOW_VIOLATING)
    satisfying = _flow_run(source, FLOW_SATISFYING)
    expect = FLOW_SATISFYING - (1 if cell.consumer == "nat" and cell.narrowing != "c" else 0)
    # 4, and the template carries the value at all.
    assert satisfying == ("ret", expect), (cell.id, satisfying)
    assert not ("verified" in used and violating[0] == "ret"), (cell.id, used, violating)
    if cell.narrowing == "u":
        # 1: no false Tier 1, unless a check on the flow stopped the value.
        own = violating[0] == "trap" and violating[1].startswith(_OWN_CHECK[cell.consumer])
        assert "verified" not in used or not own, (cell.id, used, violating)
        # 2: no demotion: the row is the row with the readers withheld.
        with monkeypatch.context() as m:
            m.setattr(verifier_mod.ContractVerifier, "_subpattern_source_facts",
                      lambda self, scrutinee, scrutinee_z3, pattern, smt: [])
            withheld, _ = _flow_verdicts(cell)
        assert rows == withheld, (cell.id, rows, withheld)
        if cell.source == "apply":
            # Disclosed, and the program accepted: the false proof would
            # ship.
            assert rows == ["tier3_unguarded/E506"], (cell.id, rows)
            assert _verify(source).ok, cell.id
        elif cell.flow != "clause_leaf":
            assert rows == ["violated/E505"], (cell.id, rows)
    else:
        # 3: nothing withheld that holds.
        direct = _flow_verdicts(FlowCell("direct", cell.shape, cell.consumer,
                                         cell.narrowing))[1]
        assert used in (["verified"], direct), (cell.id, used, direct)
