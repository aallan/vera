"""A value written as the program would write it (#1871, #1768).

A diagnostic that quotes a value — a refuted contract's counterexample, a
`vera test` trial's arguments — quotes it as the literal that denotes it in
Vera source: the expression a model would write to mean that value, in the
form `vera fmt` gives it (spec §0.2.3, one canonical form; DESIGN.md
principle 1, a diagnostic is an instruction).  A value reaches here in one
of two representations, the solver's model term (:func:`z3_text`) or the
Python value a compiled function was called with (:func:`value_text`); each
is turned into the literal node of its Vera type, and
:func:`vera.formatter.format_expr_canonical` writes every node.  So the
rule for each type is stated once:

- `Bool`: `true` / `false`, never the `1` / `0` WebAssembly carries.
- `Int`, `Nat`, `Byte`: the decimal integer.
- `Float64`: the shortest decimal that reads back as the same value,
  written positionally (`FLOAT_LIT` has no exponent), so `0.1` is `0.1`
  and `1e23` is `100000000000000000000000.0`; NaN is `nan()`, positive
  infinity `infinity()` and negative infinity `0.0 - infinity()`, the
  expressions the language makes them with.
- `String`: the quoted literal with the formatter's escapes (`\\n`, `\\"`,
  `\\u{200B}`).
- A constructor value: the constructor applied to its fields' literals,
  `Some(7)`, `None`, `Tuple(7, true)`.
- An array: `[a, b]`; past :data:`ARRAY_CAP` elements its first ones and
  how many more there are (`[0, 1, ..., ... and 2 more]` is no expression,
  so it cannot be pasted as the whole value).
- Any value past :data:`VALUE_BUDGET` parts: its first parts, each later
  one written ``...``, and ` (elided past 64 parts)` after it.

A value of a type with no literal (a `Map`, a `Set`, a function, a type
variable's) is not written: :data:`NO_LITERAL` says so where it is listed.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence

import z3

from vera import ast
from vera.formatter import format_expr_canonical

#: The elements of an array a diagnostic writes whole; a longer array shows
#: this many and the count of the rest.
ARRAY_CAP = 8

#: The parts (a constructor, a scalar, an array) one value's literal in a
#: diagnostic writes before the rest is written ``...``: a model value is a
#: term with shared subterms, and its literal repeats a subterm at each place
#: it stands, so a value built from n inputs, each a constructor over the
#: next twice, is 2^n parts long.  Sixty-four parts is a few lines of text,
#: past which a counterexample is no longer an instruction a reader can act
#: on; the value a `vera test` trial is called with is never cut, only the
#: text of a value in a diagnostic.
VALUE_BUDGET = 64

#: What a part past :data:`VALUE_BUDGET` is written as: no expression, so the
#: text cannot be taken for the whole value.
ELIDED = "..."

#: What a listed input with no literal form shows after its name.
NO_LITERAL = "its value has no literal form"

#: The array elements a solver value holds, for :func:`z3_text`: the array's
#: length and its first elements' values (at most ``ARRAY_CAP``), or
#: ``None`` where the model does not fix them.
ArrayReader = Callable[[z3.ExprRef], "tuple[int, list[z3.ExprRef]] | None"]


def text(node: ast.Expr) -> str:
    """*node* in canonical source form: the one writer of a value."""
    return format_expr_canonical(node)


def bool_literal(value: bool) -> ast.Expr:
    return ast.BoolLit(value)


def int_literal(value: int) -> ast.Expr:
    return ast.IntLit(value)


def string_literal(value: str) -> ast.Expr:
    return ast.StringLit(value)


def float_literal(value: float) -> ast.Expr:
    """A `Float64` as the expression that makes it: a literal for a finite
    value, `nan()` and `infinity()` for the values no literal spells."""
    if math.isnan(value):
        return ast.FnCall("nan", ())
    if math.isinf(value):
        inf = ast.FnCall("infinity", ())
        return inf if value == math.inf else ast.BinaryExpr(
            ast.BinOp.SUB, ast.FloatLit(0.0), inf)
    return ast.FloatLit(value)


def value_text(value: bool | int | float | str) -> str:
    """The literal of a `vera test` trial's argument, a value of one of the
    types it generates held as the Python value of that type: a `Bool` as
    a ``bool``, an `Int`, `Nat` or `Byte` as an ``int``, a `Float64` as a
    ``float``, a `String` as a ``str``."""
    if isinstance(value, bool):
        return text(bool_literal(value))
    if isinstance(value, str):
        return text(string_literal(value))
    if isinstance(value, float):
        return text(float_literal(value))
    return text(int_literal(value))


def z3_float(value: z3.ExprRef) -> float:
    """A Z3 floating-point model value as the Python float it is (#797):
    NaN and the infinities to theirs, a finite value through `fpToReal`
    (exact), the sign of zero kept."""
    fp = z3.simplify(value)
    assert isinstance(fp, z3.FPNumRef), fp  # noqa: S101 — a model value
    if fp.isNaN():
        return math.nan
    if fp.isInf():
        return -math.inf if fp.isNegative() else math.inf
    f = float(z3.simplify(z3.fpToReal(fp)).as_fraction())
    return -0.0 if (f == 0.0 and fp.isNegative()) else f


def holds_string(value: str) -> bool:
    """Whether Z3's string sort can hold every character of *value* (#802):
    its alphabet ends at U+2FFFF, and a lone surrogate (U+D800..U+DFFF) is
    no character a UTF-8 `String` can hold."""
    return not any(ord(ch) > 0x2FFFF or 0xD800 <= ord(ch) <= 0xDFFF
                   for ch in value)


def string_term(value: str) -> z3.SeqRef | None:
    """The solver's string term for the string *value*, every character
    read as itself; ``None`` where the sort cannot hold one of them
    (:func:`holds_string`).  The inverse of :func:`z3_string`, and the one
    builder of a solver string from a Vera or Python string (#1871).

    ``z3.StringVal`` reads escape syntax in the text it is given: in
    z3-solver 5.4.1, ``\\u{h}`` to ``\\u{hhhhh}`` up to U+2FFFF and
    ``\\uhhhh``, each as the character it names, so the Vera literal
    ``"\\\\u{41}"`` (six characters) became ``"A"`` and a proof over it
    was a proof about another string.  ``\\x41``, ``\\U00000041``, ``\\n``,
    ``\\\\`` and a lone ``\\`` it keeps as written.  Every backslash is
    handed to it as the escape ``\\u{5c}``, which it reads as one
    backslash and after which nothing that follows begins an escape, so
    no character of *value* is read as anything but itself."""
    if not holds_string(value):
        return None
    return z3.StringVal(value.replace(
        "\\",
        "\\u{5c}",  # pragma: no mutate — equivalent: Z3 reads its hex digits in either case, `\\u{5C}` is one backslash too
    ))


def z3_string(value: z3.ExprRef) -> str:
    """A Z3 string model value as the Python string it holds, read one code
    point at a time (#1871, #1768).  Not Z3's text of it: ``as_string``
    writes an invisible character (U+200B) and one outside the Basic
    Multilingual Plane as the escape `\\u{...}`, and a backslash where it
    would read as one, so the text is a spelling of the
    string, not the string.  The one reader of a string model value: what a
    diagnostic shows and what a `vera test` trial is called with."""
    length = z3.simplify(z3.Length(value))
    assert z3.is_int_value(length), value  # noqa: S101 — a model value
    codes = [z3.simplify(z3.StrToCode(z3.SubString(value, i, 1)))
             for i in range(length.as_long())]
    assert all(z3.is_int_value(c) for c in codes), value  # noqa: S101
    return "".join(chr(c.as_long()) for c in codes)


class _Budget:
    """The parts one value's literal may still write (:data:`VALUE_BUDGET`),
    and whether a part was left out."""

    def __init__(self) -> None:
        self.left = VALUE_BUDGET
        self.elided = False

    def take(self) -> bool:
        """Spend one part; ``False``, and the value marked elided, where
        none is left."""
        if self.left <= 0:
            self.elided = True
            return False
        self.left -= 1
        return True


def _z3_node(
    value: z3.ExprRef, arrays: ArrayReader | None, budget: _Budget,
) -> ast.Expr | str | None:
    """*value*'s literal node; text where it is written in part (an array
    past :data:`ARRAY_CAP`, a value past :data:`VALUE_BUDGET`); ``None``
    where it has no literal.  Each part spends one of *budget*'s, and a part
    past it is written ``...``, so a value of any size, a shared subterm
    counted at each place it stands, costs at most the budget's parts."""
    if not budget.take():
        return ELIDED
    sort = value.sort()
    if sort == z3.BoolSort():
        if z3.is_true(value) or z3.is_false(value):
            return bool_literal(z3.is_true(value))
        return None
    if sort == z3.IntSort():
        return int_literal(value.as_long()) if z3.is_int_value(value) else None
    if isinstance(sort, z3.FPSortRef):
        return float_literal(z3_float(value))
    if isinstance(sort, z3.SeqSortRef) and sort.is_string():
        return string_literal(z3_string(value))
    if isinstance(sort, z3.DatatypeSortRef):
        decl = value.decl()
        if decl.kind() != z3.Z3_OP_DT_CONSTRUCTOR:
            return None
        if value.num_args() == 0:
            return ast.NullaryConstructor(decl.name())
        fields = [_z3_node(value.arg(i), arrays, budget)  # pragma: no mutate — equivalent as None: no data type's sort holds an `Array` (an `Array` field leaves the type a placeholder integer), so a field never reads one
                  for i in range(value.num_args())]
        if any(f is None for f in fields):
            return None
        if all(isinstance(f, ast.Expr) for f in fields):
            return ast.ConstructorCall(
                decl.name(), tuple(f for f in fields if isinstance(f, ast.Expr)))
        return f"{decl.name()}({', '.join(_as_text(f) for f in fields)})"
    if arrays is not None:
        read = arrays(value)
        if read is not None:
            return _array_node(read, arrays, budget)
    return None


def _as_text(node: ast.Expr | str | None) -> str:
    assert node is not None  # noqa: S101 — filtered by the callers
    return node if isinstance(node, str) else text(node)


def _array_node(
    read: tuple[int, Sequence[z3.ExprRef]], arrays: ArrayReader | None,
    budget: _Budget,
) -> ast.Expr | str | None:
    length, shown = read
    elements = [_z3_node(e, arrays, budget) for e in shown]
    if any(e is None for e in elements):
        return None
    # Written as the formatter writes an `ArrayLit` (`[a, b]`), each element
    # by the formatter, so a whole array and one written in part share one
    # spelling.
    parts = [_as_text(e) for e in elements]
    more = length - len(elements)
    if more > 0:
        parts.append(f"... and {more} more")
    return f"[{', '.join(parts)}]"


def z3_text(value: z3.ExprRef, arrays: ArrayReader | None = None) -> str | None:
    """The literal of a solver model value, by its sort; ``None`` where the
    value has no literal (an uninterpreted carrier *arrays* cannot read).
    Past :data:`VALUE_BUDGET` parts the rest is ``...`` and the text says
    the value is elided."""
    budget = _Budget()
    node = _z3_node(value, arrays, budget)
    if node is None:
        return None
    written = _as_text(node)
    if budget.elided:
        written += f" (elided past {VALUE_BUDGET} parts)"
    return written
