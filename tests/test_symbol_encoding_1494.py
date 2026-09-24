"""Every composed internal symbol decodes to exactly what built it (#1494).

:mod:`vera.symbols` is the one builder and the one reader of every composed
function and data symbol: a module's qualified declaration, the prelude's own
declaration, a hoisted ``where`` helper, a monomorphized clone, and the
runtime's and the host's names.  The encoding is meant to be injective by
construction.  Three instruments hold it to that:

* **round trip** — ``decode(encode(s)) == s`` and ``encode(decode(t)) == t``
  over an ADVERSARIAL set: identifiers and path segments equal to every
  marker word the grammar uses (``mod``, ``where``, ``rt``, ``vera``,
  ``prelude``, ``anon``, the ``show_``/``eq_``/``hash_``/``compare_``
  families, …), composed through every step kind and every owner;
* **pairwise uniqueness** — no two distinct decoded symbols of that set
  encode to one string, and no two declarations of any program in the
  corpus below are emitted under one symbol;
* **one builder** — no module outside :mod:`vera.symbols` spells a
  qualifier, a helper step or a clone step itself, so there is no second
  encoding to drift from this one.

The corpus includes the collision the old ``mod$<path>$<name>`` spelling
allowed (R-1507 round 1): a function ``mod`` whose ``where`` helper is ``h``
hoisted to the same name as a module at path ``where`` qualifying its own
``h``.  One body was silently dropped and the other module's calls ran it.
"""

from __future__ import annotations

import ast as pyast
import itertools
import re
from pathlib import Path

import pytest

import vera
from tests.codegen_helpers import wat_fn_names
from tests.module_fixture_helpers import build_multi_module, module_value
from vera import symbols
from vera.monomorphize import mangle_type_name

_VERA = Path(vera.__file__).resolve().parent

# ---------------------------------------------------------------------------
# The adversarial set
# ---------------------------------------------------------------------------

#: Identifiers equal to every word the grammar or the runtime uses as a
#: marker or a family prefix.  ``where`` is reserved (E153) and cannot be a
#: declaration's name, but it CAN be a module path segment, so it is kept in
#: both lists: the encoding must survive it wherever the language allows it.
_WORDS = (
    "mod", "where", "rt", "vera", "prelude", "anon", "anon_0", "alloc",
    "gc_collect", "show_Int", "eq_List", "hash_x", "compare_x",
    "dec_size_x", "cabi_realloc", "wasi_run", "trap_kind_x", "exn_x",
    "closure_sig_0", "x", "h", "gen", "a_b",
)
_SEGMENTS = ("mod", "where", "rt", "prelude", "lib", "a", "b", "anon_0")
_PATHS = tuple(
    path
    for n in (1, 2)
    for path in itertools.product(_SEGMENTS, repeat=n)
)
#: Type arguments a clone step escapes, including owner-qualified data names
#: built by the builder itself, whose paths are marker words too.
_TYPES = (
    "Int", "Bool", "Option<Int>", "Map<String, Int>", "Tuple<Int, Bool>",
    symbols.module_symbol(("where",), "Shape"),
    symbols.module_symbol(("rt", "x"), "Shape"),
    symbols.prelude_symbol("Shape"),
)
_CLONE_ARGS = tuple(
    "_J".join(mangle_type_name(t) for t in combo)
    for n in (1, 2)
    for combo in itertools.product(_TYPES[:4], repeat=n)
) + tuple(mangle_type_name(t) for t in _TYPES[4:])


def _steps() -> tuple[tuple[symbols.Step, ...], ...]:
    one = [symbols.Step("helper", w) for w in _WORDS] + [
        symbols.Step("clone", c) for c in _CLONE_ARGS
    ]
    two = [
        (symbols.Step("clone", "Int"), symbols.Step("helper", w))
        for w in _WORDS
    ] + [
        (symbols.Step("helper", w), symbols.Step("clone", "Bool"))
        for w in _WORDS
    ] + [
        (symbols.Step("helper", "where"), symbols.Step("helper", w))
        for w in _WORDS
    ]
    return ((),) + tuple((s,) for s in one) + tuple(two)


def _adversarial() -> list[symbols.Symbol]:
    out: list[symbols.Symbol] = []
    steps = _steps()
    for base in _WORDS:
        for st in steps:
            out.append(symbols.Symbol(symbols.LOCAL, (), base, st))
            out.append(symbols.Symbol(symbols.PRELUDE, (), base, st))
        for path in _PATHS:
            for st in steps[:40]:
                out.append(symbols.Symbol(symbols.MODULE, path, base, st))
    for name in _WORDS + ("eq_" + mangle_type_name("Option<Int>"),):
        out.append(symbols.Symbol(symbols.RUNTIME, (), name))
        out.append(symbols.Symbol(symbols.HOST, (), name))
    # Data names: an upper-case base, owned by a module or by nobody.
    for data in ("Shape", "Circle", "Option"):
        out.append(symbols.Symbol(symbols.LOCAL, (), data))
        for path in _PATHS:
            out.append(symbols.Symbol(symbols.MODULE, path, data))
    return out


_ADVERSARIAL = _adversarial()


class TestRoundTrip:
    def test_the_set_is_large_and_adversarial(self) -> None:
        # Every marker word appears as a base, a helper, and a path segment.
        assert len(_ADVERSARIAL) > 10_000
        assert {"where", "mod", "rt", "vera"} <= set(_SEGMENTS) | set(_WORDS)

    def test_decode_inverts_encode(self) -> None:
        bad = [
            (sym, symbols.encode(sym), symbols.decode(symbols.encode(sym)))
            for sym in _ADVERSARIAL
            if symbols.decode(symbols.encode(sym)) != sym
        ]
        assert bad == [], bad[:5]

    def test_encode_inverts_decode(self) -> None:
        texts = {symbols.encode(sym) for sym in _ADVERSARIAL}
        bad = [t for t in texts if symbols.encode(symbols.decode(t)) != t]
        assert bad == [], bad[:5]

    def test_no_two_symbols_share_a_spelling(self) -> None:
        seen: dict[str, symbols.Symbol] = {}
        clashes = []
        for sym in _ADVERSARIAL:
            text = symbols.encode(sym)
            prior = seen.setdefault(text, sym)
            if prior != sym:
                clashes.append((text, prior, sym))
        assert clashes == [], clashes[:5]

    def test_the_old_spelling_was_not_injective(self) -> None:
        """The control: the pre-fix ``mod$<path>$<name>`` spelling maps two
        of the adversarial symbols to one string — a module at path
        ``where`` qualifying ``h``, and a function ``mod`` whose helper is
        ``h`` — so the instrument above can tell the two encodings apart."""
        def old(sym: symbols.Symbol) -> str:
            chain = symbols.join_chain(sym.base, sym.steps)
            if sym.owner == symbols.MODULE:
                return "mod$" + "$".join(sym.path) + "$" + chain
            return chain

        qualified = symbols.Symbol(symbols.MODULE, ("where",), "h")
        hoisted = symbols.Symbol(
            symbols.LOCAL, (), "mod", (symbols.Step("helper", "h"),),
        )
        assert old(qualified) == old(hoisted) == "mod$where$h"
        assert symbols.encode(qualified) != symbols.encode(hoisted)


class TestDisplay:
    """What a person reads: the source spelling, never a marker."""

    @pytest.mark.parametrize("text,shown", [
        ("liba::h", "liba::h"),
        ("a.b::f", "a.b::f"),
        ("gen$Int", "gen"),
        ("liba::x$where$h", "liba::h"),
        ("outer$Int$where$ginner$Bool", "ginner"),
        ("<prelude>::json_get", "json_get"),
        ("rt.anon_3", "fn(...)"),
        ("rt.alloc", "alloc"),
        ("vera.contract_fail", "contract_fail"),
        ("main", "main"),
    ])
    def test_display(self, text: str, shown: str) -> None:
        assert symbols.display(text) == shown

    def test_no_marker_survives_display(self) -> None:
        """A step or the prelude's owner never reaches a person.  A module
        path is source and stays (``rt.util::f`` is how the call is spelled)."""
        markers = ("$", "<prelude>")
        leaks = [
            (sym, symbols.display(symbols.encode(sym)))
            for sym in _ADVERSARIAL
            if sym.owner not in (symbols.RUNTIME, symbols.HOST)
            and any(m in symbols.display(symbols.encode(sym)) for m in markers)
        ]
        assert leaks == [], leaks[:5]


# ---------------------------------------------------------------------------
# One builder
# ---------------------------------------------------------------------------

#: Files that may spell ``::`` in a code string, each with its reason.  The
#: qualifier is also the SOURCE syntax of a qualified call (``vera.math::abs``),
#: so a module that renders or diagnoses source may quote it.  Anything else
#: that spells it is building a symbol outside the builder.
_SPELLS_SOURCE_SYNTAX = {
    "ast.py": "renders a qualified call as source",
    "formatter.py": "formats a qualified call",
    "disclosure.py": "names a qualified call in a disclosure",
    "codegen/modules.py": "names a qualified call in a diagnostic",
    "checker/modules.py": "quotes a qualified call in a diagnostic's fix",
    "checker/registration.py": "quotes a qualified call in a diagnostic",
    "errors.py": "the parse diagnostic for a mistyped qualified call",
    "codegen/assembly.py": "a WAT comment citing a pytest node id",
    "runtime/db.py": "SQLite's in-memory database name",
}


def _code_strings(path: Path) -> list[str]:
    """The string constants and f-string templates of *path*'s code.

    Docstrings are skipped; an f-string is its literal text with each
    interpolation shown as ``{``.
    """
    tree = pyast.parse(path.read_text(encoding="utf-8"))
    docstrings = {
        id(node.body[0].value)
        for node in pyast.walk(tree)
        if isinstance(node, (pyast.Module, pyast.ClassDef, pyast.FunctionDef,
                             pyast.AsyncFunctionDef))
        and node.body and isinstance(node.body[0], pyast.Expr)
        and isinstance(node.body[0].value, pyast.Constant)
    }
    out: list[str] = []
    for node in pyast.walk(tree):
        if isinstance(node, pyast.JoinedStr):
            out.append("".join(
                str(v.value) if isinstance(v, pyast.Constant) else "{"
                for v in node.values
            ))
        elif (isinstance(node, pyast.Constant) and isinstance(node.value, str)
              and id(node) not in docstrings):
            out.append(node.value)
    return out


def _modules() -> list[tuple[str, list[str]]]:
    return [
        (path.relative_to(_VERA).as_posix(), _code_strings(path))
        for path in sorted(_VERA.rglob("*.py"))
        if path.name != "symbols.py"
    ]


class TestOneBuilder:
    """No module but :mod:`vera.symbols` composes a symbol."""

    def test_no_module_spells_a_helper_step_or_the_old_qualifier(self) -> None:
        offenders = [
            (rel, text[:60])
            for rel, texts in _modules()
            for text in texts
            if symbols.HELPER_STEP in text or text.startswith("mod$")
        ]
        assert offenders == [], offenders

    def test_only_source_renderers_spell_the_qualifier(self) -> None:
        offenders = sorted({
            rel
            for rel, texts in _modules()
            if rel not in _SPELLS_SOURCE_SYNTAX
            and any(symbols.QUALIFIER in text for text in texts)
        })
        assert offenders == [], offenders

    def test_every_allowance_is_still_used(self) -> None:
        """An allowance cannot outlive its reason."""
        unused = [
            rel for rel, texts in _modules()
            if rel in _SPELLS_SOURCE_SYNTAX
            and not any(symbols.QUALIFIER in text for text in texts)
        ]
        assert unused == [], unused
        assert set(_SPELLS_SOURCE_SYNTAX) <= {rel for rel, _ in _modules()}


# ---------------------------------------------------------------------------
# The corpus: no two declarations share a symbol, and none is lost
# ---------------------------------------------------------------------------

_WHERE_H = """\
{vis} fn mod(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  h(@Int.0)
}}
where {{
  fn h(@Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{
    @Int.0 + 100
  }}
}}
"""

_WHERE_MODULE = """\
module where;

private fn h(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 200
}

public fn y(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  h(@Int.0)
}
"""

_MAIN_TAIL = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mod(1) * 1000 + y(1)
}
"""


def _corpus() -> dict[str, dict[str, str]]:
    return {
        # R-1507 round 1, finding 1: the helper in a module that owns `mod`.
        "module-helper": {
            "moda.vera": "module moda;\n\n" + _WHERE_H.format(vis="public"),
            "where.vera": _WHERE_MODULE,
            "main.vera": "import moda(mod);\nimport where(y);\n\n" + _MAIN_TAIL,
        },
        # The helper in the entry instead.
        "entry-helper": {
            "where.vera": _WHERE_MODULE,
            "main.vera": "import where(y);\n\n"
            + _WHERE_H.format(vis="private") + "\n" + _MAIN_TAIL,
        },
        # A module whose path begins `rt`, beside the runtime's own names.
        "rt-path": {
            "rt/util.vera": "module rt.util;\n\n"
            "private fn alloc(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{\n  @Int.0 + 200\n}\n\n"
            "public fn y(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{\n  alloc(@Int.0) + string_length("
            "string_concat(\"a\", \"b\"))\n}\n",
            "main.vera": "import rt.util(y);\n\n"
            "public fn mod(@Int -> @Int)\n  requires(true)\n  ensures(true)\n"
            "  effects(pure)\n{\n  @Int.0 + 100\n}\n\n" + _MAIN_TAIL,
        },
    }


_EXPECTED = {"module-helper": 101201, "entry-helper": 101201, "rt-path": 101203}


@pytest.mark.parametrize("case", sorted(_corpus()))
def test_each_declaration_runs_its_own_body(case: str, tmp_path: Path) -> None:
    files = _corpus()[case]
    for rel in list(files):
        (tmp_path / rel).parent.mkdir(parents=True, exist_ok=True)
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, cg_errors
    assert not verify_errors, verify_errors
    assert module_value(result, "main") == ("ok", _EXPECTED[case])


@pytest.mark.parametrize("case", sorted(_corpus()))
def test_every_emitted_symbol_decodes_to_one_declaration(
    case: str, tmp_path: Path,
) -> None:
    """Pairwise uniqueness over the corpus, read off the module: every
    function symbol decodes, re-encodes to itself, and names one owner's one
    declaration — two decoded identities never share a symbol."""
    files = _corpus()[case]
    for rel in list(files):
        (tmp_path / rel).parent.mkdir(parents=True, exist_ok=True)
    _, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, cg_errors
    names = wat_fn_names(result.wat)
    assert len(names) == len(set(names)), names
    decoded = {name: symbols.decode(name) for name in names}
    assert all(symbols.encode(d) == n for n, d in decoded.items()), decoded
    # Both `h`s are emitted, each under its own owner's symbol.
    hs = sorted(
        n for n, d in decoded.items()
        if d.base == "h" or any(s.text == "h" for s in d.steps)
    )
    if case != "rt-path":
        assert len(hs) == 2, (hs, names)
        assert {decoded[n].owner for n in hs} >= {symbols.MODULE}, hs


def test_a_module_path_beginning_rt_is_the_programs(tmp_path: Path) -> None:
    """``rt.util::alloc`` is the program's, not the runtime's, though its
    text begins ``rt.``: the resolver decodes, it does not prefix-test."""
    assert symbols.decode("rt.util::alloc").owner == symbols.MODULE
    assert not symbols.is_runtime("rt.util::alloc")
    assert symbols.is_runtime("rt.alloc")
    assert re.fullmatch(r"[a-z.]+::[a-z_]+", "rt.util::alloc")
