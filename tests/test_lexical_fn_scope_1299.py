"""#1299: codegen's bare-call ownership table must be the CALL SITE's scope.

The #1284 ownership predicate (:func:`vera.slots.bare_call_denotes_user_fn`)
is one rule read over two tables.  The checker's table is a lexical scope
walk; codegen's was ``set(self._fn_sigs.keys())`` — a FLAT mirror of every
symbol the whole compilation absorbed, including names the compiling body
cannot see.  Where the two disagree, codegen lowers a bare ``get(())`` the
checker resolved to a ``State`` operation as a call to some other
declaration entirely.

Three routes put an invisible name in that flat table, and all three are
check-green:

* an imported module's **private** ``fn get`` — still compiled in, because
  the module's own bodies call it (#1008-class reachability);
* an imported module's **public** ``fn get`` that the importer's selective
  import filter excludes;
* a ``where`` helper of a **``forall<T>`` parent**, which keeps a bare
  ``_fn_sigs`` key beside its clone-qualified one where a non-generic
  parent's helper does not (#991 / #1015 hoist it out of the bare
  namespace; the hoist skips generic subtrees).

How each lands depends on the widths, not on the route: where the invisible
declaration and the cell share a WAT type the module loads and answers the
WRONG value; where they differ it fails to load.  The generic-``where``
route is always loud, for a reason worth keeping — the bare key exists in
the signature table while no bare SYMBOL is emitted (the helper is only ever
``holder$Bool$where$get``), so the call dies at WAT assembly.

**Every expected value below is the CHECKER's answer**, and the checker's
answer is *proven* rather than assumed: the invisible ``get`` returns
``@Bool`` in the oracle fixtures while the caller returns ``@Int`` from
``get(())`` and checks green, which is only possible if the checker typed
the call from the ``State<Int>`` cell.  Each route also carries a rename
control — the same program with the invisible declaration renamed — which
must produce the identical answer, so a case that stops distinguishing the
two tables fails loudly instead of passing vacuously.

The controls in the other direction matter as much: a VISIBLE imported
``get`` (public, in-filter, direct) still owns the bare name, and a LOCAL
``fn get`` still shadows the operation — that is #1284, and narrowing the
table must not undo it.
"""

from __future__ import annotations

import os
import traceback
from collections.abc import Callable
from pathlib import Path
from typing import Any, ClassVar

import pytest

from tests.codegen_helpers import wat_calls, wat_fn_body, wat_fn_names
from tests.module_fixture_helpers import build_multi_module, module_value
from vera import ast
from vera.codegen.core import CodeGenerator
from vera.monomorphize import MonoContext, Monomorphizer, NamespaceFnNames
from vera.parser import parse_to_ast
from vera.wasm import StringPool
from vera.wasm.context import WasmContext

# Three values that cannot coincide.  CELL is what the checker's answer is
# in every invisible-import cell; LIB is the invisible declaration's own
# answer (what the flat table produced pre-fix); LOCAL is the importer's own
# `fn get`, for the #1284 shadowing control.
CELL = 42007
LIB = 7007
LOCAL = 555

# Where one program's answer is the join of TWO measured values, the join is
# weighted rather than summed.  `a + b` is commutative, so it is satisfied by
# the two contributions swapping — which is the defect class these files
# exist to catch, not an unrelated one.  Scaling one past the other's
# magnitude keeps the pair recoverable from the total.
JOIN_SCALE = 1000


# ---------------------------------------------------------------------
# Fixture builders
# ---------------------------------------------------------------------

def _lib(vis: str, *, name: str = "get", ret: str = "Int") -> str:
    """A module declaring ``<vis> fn <name>`` plus a public caller of it.

    ``touch`` exists so the declaration is REACHABLE from the module's own
    body: that is what keeps a private one compiled into the importer's flat
    WASM module, which is the whole premise of the private route.
    """
    answer = {"Int": str(LIB), "Bool": "true", "Nat": "3"}[ret]
    return f"""\
module lib;

{vis} fn {name}(@Unit -> @{ret})
  requires(true)
  ensures(true)
  effects(pure)
{{ {answer} }}

public fn touch(@Unit -> @{ret})
  requires(true)
  ensures(true)
  effects(pure)
{{ {name}(()) }}
"""


_LOCAL_GET = f"""\
private fn get(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {LOCAL} }}
"""


def _importer(import_lines: str, *, local_get: bool = False) -> str:
    """An importer whose ``main`` reads a ``State<Int>`` cell by bare ``get``.

    *import_lines* is the whole import block (possibly empty).  Imports must
    precede every declaration, so it is threaded rather than spliced in by a
    caller — a fixture that produced an unparseable program would fail for a
    reason that has nothing to do with the table under test.
    """
    local = _LOCAL_GET + "\n" if local_get else ""
    return f"""\
{import_lines}{local}public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = {CELL}) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}
"""


def _main(imports: str | None, *, local_get: bool = False) -> str:
    """:func:`_importer` importing ``lib`` under the given filter suffix.

    ``None`` means no import at all — the standalone oracle.
    """
    return _importer(
        "" if imports is None else f"import lib{imports};\n\n",
        local_get=local_get,
    )


# The oracle: `main` with no import at all.  Whatever an import shape does to
# the flat namespace, this is the answer the source commits to — the cell's.
_STANDALONE = _main(None)
_STANDALONE_SHADOWED = _main(None, local_get=True)


def _answer(
    tmp_path: Path, files: dict[str, str], fn: str = "main",
) -> object:
    """Verify + compile + run in one call, asserting the two agree.

    Returns the runtime value.  A clean verify beside a trap or a wrong value
    is the divergence this issue is about, so both halves are asserted here
    rather than in sibling tests that could pass independently.
    """
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    kind, payload = module_value(result, fn)
    assert kind == "ok", f"module did not load/run: {payload}"
    return payload


# ---------------------------------------------------------------------
# The oracle
# ---------------------------------------------------------------------

class TestStandaloneOracle:
    """What the importer's own source commits to, with no module in view."""

    def test_no_import_answers_the_cell(self, tmp_path: Path) -> None:
        assert _answer(tmp_path, {"main.vera": _STANDALONE}) == CELL

    def test_local_get_shadows_the_operation(self, tmp_path: Path) -> None:
        """#1284, restated as this fix's floor: a LOCAL declaration owns the
        bare name, and narrowing the table must not take that away."""
        assert _answer(
            tmp_path, {"main.vera": _STANDALONE_SHADOWED},
        ) == LOCAL


# ---------------------------------------------------------------------
# Route 1 — a private declaration in an imported module
# ---------------------------------------------------------------------

class TestPrivateImportRoute:
    """``private fn get`` in an imported module: invisible to the importer,
    still compiled in, and bare-keyed in ``_fn_sigs``."""

    def test_checker_types_the_call_from_the_cell(
        self, tmp_path: Path,
    ) -> None:
        """The TYPE ORACLE, and the reason every expected value below is CELL.

        The module's invisible ``get`` returns ``@Bool``; ``main`` returns
        ``@Int`` from ``get(())``.  A program in which the checker had
        resolved the call to that declaration could not type-check, so a
        clean check is a proof the checker typed the call from the
        ``State<Int>`` cell — not an assumption about it.
        """
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path,
            {"lib.vera": _lib("private", ret="Bool"),
             "main.vera": _main("(touch)")},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"

    def test_answers_the_cell(self, tmp_path: Path) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("private"), "main.vera": _main("(touch)")},
        ) == CELL

    def test_lowers_to_the_state_import_not_the_module_body(
        self, tmp_path: Path,
    ) -> None:
        """The dispatch itself, so a value that happened to coincide could
        not carry the assertion.

        Asserted on ``main``'s body ALONE, because the module's own ``touch``
        legitimately calls its private ``get`` in the same WAT — the
        narrowing is per-namespace, not a deletion, and a module-wide
        assertion could not tell those two apart.
        """
        _, result, _ = build_multi_module(
            tmp_path,
            {"lib.vera": _lib("private"), "main.vera": _main("(touch)")},
        )
        main_body = wat_fn_body(result.wat, "main")
        assert wat_calls(main_body, "vera.state_get_Int")
        assert not wat_calls(main_body, "get")
        # The module's own body is the control: its private helper is still
        # in ITS scope, so that call must survive — to the helper's own
        # symbol, `mod$lib$get`, since a private declaration does not own the
        # entry's bare name (#1498).
        assert wat_calls(wat_fn_body(result.wat, "touch"), "mod$lib$get")

    def test_rename_control_answers_the_same(self, tmp_path: Path) -> None:
        """The same program with the invisible declaration renamed.  It must
        answer identically; if it does not, the fixture stopped isolating the
        name collision and every cell above is measuring something else."""
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("private", name="gettt"),
             "main.vera": _main("(touch)")},
        ) == CELL

    def test_wildcard_import_does_not_expose_a_private_name(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("private"), "main.vera": _main("")},
        ) == CELL


# ---------------------------------------------------------------------
# Route 2 — a public declaration the import filter excludes
# ---------------------------------------------------------------------

class TestSelectiveImportRoute:
    """``public fn get`` that the importer's filter does not name."""

    def test_checker_types_the_call_from_the_cell(
        self, tmp_path: Path,
    ) -> None:
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path,
            {"lib.vera": _lib("public", ret="Bool"),
             "main.vera": _main("(touch)")},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert not verify_errors, f"verify errors: {verify_errors}"

    def test_excluded_public_name_answers_the_cell(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("public"), "main.vera": _main("(touch)")},
        ) == CELL

    def test_included_public_name_still_owns_the_bare_call(
        self, tmp_path: Path,
    ) -> None:
        """The control in the other direction: name it in the filter and it
        IS visible, so the checker resolves the import and codegen must
        follow.  This cell must stay LIB — the fix narrows the table to the
        call site's scope, it does not empty it."""
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("public"),
             "main.vera": _main("(touch, get)")},
        ) == LIB

    def test_wildcard_import_exposes_a_public_name(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("public"), "main.vera": _main("")},
        ) == LIB


# ---------------------------------------------------------------------
# Route 3 — a `where` helper of a generic parent
# ---------------------------------------------------------------------

_GENERIC_WHERE = f"""\
private forall<T> fn holder(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {{HELPER}}(()) }}
where {{
  fn {{HELPER}}(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{ {LIB} }}
}}

public fn sibling(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = {CELL}) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    get(())
  }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ holder(true) * {JOIN_SCALE} + sibling(()) }}
"""


def _generic_where(helper: str) -> str:
    return _GENERIC_WHERE.replace("{HELPER}", helper)


class TestGenericWhereHelperRoute:
    """No imports at all: a ``forall<T>`` parent's helper named ``get`` is in
    the MODULE but not in a sibling's lexical scope, so "names visible at
    module scope" would not close this route — only the lexical rule does.

    ``main`` calls BOTH, so the generic's clone is instantiated: the two
    directions of the narrowing (the sibling must lose the name, the parent
    must keep it) are exercised by one compilation.
    """

    def test_sibling_answers_the_cell(self, tmp_path: Path) -> None:
        assert _answer(
            tmp_path, {"main.vera": _generic_where("get")}, "sibling",
        ) == CELL

    def test_rename_control_answers_the_same(self, tmp_path: Path) -> None:
        assert _answer(
            tmp_path, {"main.vera": _generic_where("gettt")}, "sibling",
        ) == CELL

    def test_the_generic_still_reaches_its_own_helper(
        self, tmp_path: Path,
    ) -> None:
        """The parent's own body is the case the narrowing must NOT break:
        the helper IS in ``holder``'s scope, so its clone keeps calling the
        per-clone symbol — and ``main``'s sum separates the two answers."""
        _, result, cg_errors = build_multi_module(
            tmp_path, {"main.vera": _generic_where("get")},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        assert wat_calls(result.wat, "holder$Bool$where$get")
        assert module_value(result) == ("ok", LIB * JOIN_SCALE + CELL)


# ---------------------------------------------------------------------
# The same table, read by MONOMORPHIZATION DISCOVERY
# ---------------------------------------------------------------------

def _generic_wrapped(imports: str, cell: int = CELL) -> str:
    """An importer whose bare ``get(())`` is an ARGUMENT to a local generic.

    The wrapping is what reaches the third consumer.  A bare ``get(())`` in
    value position is typed by ``_translate_call``'s dispatch, which the
    scoped table already gates; as a generic's argument it is ALSO typed by
    instantiation discovery, to name the clone — and discovery's table is
    program-wide, so it kept claiming the invisible declaration.
    """
    return f"""\
import lib{imports};

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{ @T.0 }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = {cell}) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    idg(get(()))
  }}
}}
"""


class TestDiscoveryLeg:
    """The fifth consumer: ``MonoContext.fn_names``, read by the
    monomorphizer's instantiation-discovery walk.

    The two dispatch gates read a per-declaration scope; discovery read
    ``frozenset(_fn_sigs)`` — the flat registry, which the guard rail needs
    complete and which therefore still holds an imported module's private
    ``get``.  Wrapping the call in a local generic makes discovery name the
    clone: from the invisible declaration's declared return (``idg$Bool``)
    where the checker had typed the ``State<Int>`` cell (``idg$Int``).

    Two tables had to move for this, and the second is the one that bites
    after the first: with discovery corrected, the WASM call-rewrite's
    clone-naming override (``_declared_return_clone_name``, which BEATS the
    general inference for #899's benefit) still read the invisible
    declaration's return and named ``idg$Bool`` at a call site whose clone
    was now ``idg$Int`` — the module compiled with ``main`` dropped [E620]
    instead of failing to load.  Both are gated on the same predicate over
    the same scope.

    How each landed before is a property of the widths, as everywhere else in
    this file: ``@Bool`` against an ``Int`` cell fails to load, ``@Nat``
    reaches a live clone of the wrong signedness and traps.
    """

    def test_private_import_does_not_name_the_clone(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("private", ret="Bool"),
             "main.vera": _generic_wrapped("(touch)")},
        ) == CELL

    def test_excluded_public_import_does_not_name_the_clone(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("public", ret="Bool"),
             "main.vera": _generic_wrapped("(touch)")},
        ) == CELL

    def test_nat_variant_reaches_the_cell_rather_than_trapping(
        self, tmp_path: Path,
    ) -> None:
        """``@Nat`` and ``Int`` share a machine width, so this shape does not
        fail to load — pre-fix it named a live clone of the wrong signedness
        and the negative cell value reached it.  A negative cell is the whole
        point: a non-negative one could not tell the two clones apart."""
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("private", ret="Nat"),
             "main.vera": _generic_wrapped("(touch)", cell=-5)},
        ) == -5

    def test_rename_control_answers_the_same(self, tmp_path: Path) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": _lib("private", name="gettt", ret="Bool"),
             "main.vera": _generic_wrapped("(touch)")},
        ) == CELL

    def test_a_visible_import_still_names_the_clone(
        self, tmp_path: Path,
    ) -> None:
        """The control in the other direction: name it in the filter and the
        call IS that declaration, so its return type must keep naming the
        clone.  ``string_length`` of it pins the clone that ran — the
        ``@String`` instantiation, which the operation's ``Int`` could not
        produce."""
        lib = """\
module lib;

public fn get(@Unit -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ "abcd" }
"""
        main = f"""\
import lib(get);

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{{ @T.0 }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = {CELL}) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    string_length(idg(get(())))
  }}
}}
"""
        assert _answer(tmp_path, {"lib.vera": lib, "main.vera": main}) == 4


# ---------------------------------------------------------------------
# The same table, read at the INTRINSIC gate
# ---------------------------------------------------------------------

_SHOW_LIB = f"""\
module lib;

private fn show(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {LIB} }}

public fn touch(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ show(1) }}
"""

_SHOW_MAIN = """\
import lib(touch);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ string_length(show(42)) }
"""


class TestAbilityOpRoute:
    """``_translate_call``'s FIRST use of the table is the intrinsic gate,
    not the effect-op dispatch — and it is reachable independently.

    ``show`` / ``hash`` are the ability operations E151 does NOT reserve
    (#908), so a module may declare ``fn show`` where it may not declare
    ``fn array_length``.  A private one bare-keyed the flat table, and the
    importer's ``show(42)`` — which the checker resolved to the ability
    operation, since the module's declaration is not in its scope — skipped
    the ability dispatch and lowered as a call to the module's ``@Int``
    function instead.  ``string_length`` of the result then received an i64
    and the module failed to load.

    One rule, one table: narrowing it closes the intrinsic gate and the op
    gate together, which is why the predicate is shared rather than
    reimplemented at each.
    """

    def test_show_reaches_the_ability_operation(
        self, tmp_path: Path,
    ) -> None:
        # `show(42)` is the String "42", whose length is 2 — a value the
        # module's `show` (an @Int) could not produce in this position at
        # all, which is what makes the load failure the pre-fix symptom.
        assert _answer(
            tmp_path,
            {"lib.vera": _SHOW_LIB, "main.vera": _SHOW_MAIN},
        ) == 2

    def test_show_inside_a_lifted_closure_reaches_it_too(
        self, tmp_path: Path,
    ) -> None:
        """A closure body is lexically inside its enclosing function, and is
        compiled through a SEPARATE ``WasmContext`` built by the lift.

        That context gets its own copy of the tables, so the scope has to be
        carried across the lift or the closure body silently reverts to the
        flat one.  Reachable through ``show`` and not through ``get``: an
        anonymous function's effect clause admits no row, so a closure body
        cannot perform an effect operation at all — the ability ops are the
        one shadowable name that survives the boundary.
        """
        closure_main = """\
import lib(touch);

type IntToInt = fn(Int -> Int) effects(pure);

private fn make(@Unit -> @IntToInt)
  requires(true)
  ensures(true)
  effects(pure)
{ fn(@Int -> @Int) effects(pure) { string_length(show(@Int.0)) } }

private fn drive(@IntToInt -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ apply_fn(@IntToInt.0, 42) }

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ drive(make(())) }
"""
        assert _answer(
            tmp_path,
            {"lib.vera": _SHOW_LIB, "main.vera": closure_main},
        ) == 2


# ---------------------------------------------------------------------
# The visibility matrix
# ---------------------------------------------------------------------

_TRANSITIVE_MID = """\
module mid;

import deep(touch);

public fn door(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ touch(()) }
"""


def _deep(vis: str) -> str:
    return _lib(vis).replace("module lib;", "module deep;")


class TestVisibilityMatrix:
    """visibility x filter x shadowing x reach, every cell asserting the
    verify verdict and the runtime value together.

    The expected value is a function of the LANGUAGE rule, never of what
    codegen emits: a local declaration wins outright (#1284); otherwise a
    module declaration wins exactly when the importer can SEE it — public,
    named by the filter (or a wildcard), and reached by a DIRECT import
    (spec §8.6.4); otherwise the bare call is the ``State`` operation.
    """

    @pytest.mark.parametrize("local_get", [False, True], ids=["plain", "shadowed"])
    @pytest.mark.parametrize(
        ("vis", "imports"),
        [
            ("private", "(touch)"),
            ("private", ""),
            ("public", "(touch)"),
            ("public", "(touch, get)"),
            ("public", ""),
        ],
        ids=["priv_filtered", "priv_wildcard", "pub_excluded",
             "pub_in_filter", "pub_wildcard"],
    )
    def test_direct(
        self, tmp_path: Path, vis: str, imports: str, local_get: bool,
    ) -> None:
        visible = vis == "public" and (imports == "" or "get" in imports)
        expected = LOCAL if local_get else (LIB if visible else CELL)
        assert _answer(
            tmp_path,
            {"lib.vera": _lib(vis),
             "main.vera": _main(imports, local_get=local_get)},
        ) == expected

    @pytest.mark.parametrize("local_get", [False, True], ids=["plain", "shadowed"])
    @pytest.mark.parametrize("vis", ["private", "public"])
    def test_transitive(
        self, tmp_path: Path, vis: str, local_get: bool,
    ) -> None:
        """A transitive module contributes NOTHING to the importer's
        namespace (spec §8.6.4), so even a public ``get`` two hops away
        leaves the bare call as the operation."""
        main = _importer("import mid(door);\n\n", local_get=local_get)
        assert _answer(
            tmp_path,
            {"deep.vera": _deep(vis), "mid.vera": _TRANSITIVE_MID,
             "main.vera": main},
        ) == (LOCAL if local_get else CELL)


# ---------------------------------------------------------------------
# The two tables, as structures
# ---------------------------------------------------------------------

_NESTED_HELPERS = """\
private forall<T> fn top(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ a(()) }
where {
  fn a(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  { b(()) }
  where {
    fn b(@Unit -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    { 1 }
  }

  fn c(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  { 2 }
}
"""


def _top_decl(source: str, name: str) -> ast.FnDecl:
    """The named top-level ``FnDecl`` of *source*."""
    for tld in parse_to_ast(source).declarations:
        decl = tld.decl
        if isinstance(decl, ast.FnDecl) and decl.name == name:
            return decl
    raise AssertionError(f"no top-level fn {name!r} in the fixture")


class TestTableInvariants:
    """Properties of the two tables the split created, asserted directly.

    Each is claimed in a docstring in ``vera/codegen/core.py``; a claim in a
    docstring is not an assertion, and both of these fail SILENTLY — a scope
    admitting a name with no signature, or a helper the scope walk skipped,
    changes an answer without changing a symbol.
    """

    def test_scoped_names_never_exceed_the_registry(
        self, tmp_path: Path,
    ) -> None:
        """``_scoped_fn_names`` returns a subset of ``_fn_sigs``.

        The whole change is a NARROWING: it may withdraw a name the flat
        table wrongly claimed, never introduce one with no signature behind
        it.  Asserted over every call made during a compilation that
        exercises the routes together — an import, a filter, and a generic
        parent's nested helpers — rather than on a constructed input.
        """
        seen: list[tuple[set[str], set[str]]] = []
        original = CodeGenerator._scoped_fn_names

        def recording(
            gen: CodeGenerator, where_scope: frozenset[str], own_name: str,
        ) -> set[str]:
            out = original(gen, where_scope, own_name)
            seen.append((set(out), set(gen._fn_sigs)))
            return out

        CodeGenerator._scoped_fn_names = recording  # type: ignore[method-assign,assignment]
        try:
            build_multi_module(
                tmp_path,
                {"lib.vera": _lib("private"),
                 "main.vera": (
                     _importer("import lib(touch);\n\n") + "\n"
                     + _NESTED_HELPERS)},
            )
        finally:
            CodeGenerator._scoped_fn_names = original  # type: ignore[method-assign]

        assert seen, "no function was compiled — the assertion is vacuous"
        for scoped, registry in seen:
            assert scoped <= registry, (
                f"scoped names outside the registry: {scoped - registry}"
            )

    def test_prelude_names_stay_in_every_scope(
        self, tmp_path: Path,
    ) -> None:
        """The prelude combinators are declarations too, visible everywhere.

        Inert as behaviour today — none of them is named like an operation
        or an intrinsic, so withdrawing them changes no emitted call — which
        is exactly why the membership is asserted rather than left to a
        behaviour test that would be green either way.  A prelude addition
        that DID collide would otherwise land silently.
        """
        seen: list[tuple[set[str], set[str], set[str]]] = []
        original = CodeGenerator._scoped_fn_names

        def recording(
            gen: CodeGenerator, where_scope: frozenset[str], own_name: str,
        ) -> set[str]:
            out = original(gen, where_scope, own_name)
            seen.append(
                (set(out), set(gen._fn_sigs), set(gen._prelude_fn_names)),
            )
            return out

        CodeGenerator._scoped_fn_names = recording  # type: ignore[method-assign,assignment]
        try:
            build_multi_module(
                tmp_path,
                {"lib.vera": _lib("private"), "main.vera": _main("(touch)")},
            )
        finally:
            CodeGenerator._scoped_fn_names = original  # type: ignore[method-assign]

        assert any(prelude for _, _, prelude in seen), (
            "the prelude registered no function — the assertion is vacuous"
        )
        for scoped, registry, prelude in seen:
            missing = (prelude & registry) - scoped
            assert not missing, f"prelude names withdrawn: {missing}"

    def test_where_scopes_enumerate_the_flatten_walk(self) -> None:
        """``_where_fn_scopes`` visits exactly ``_flatten_where_fns``'s
        helpers, in the same order.

        Two walks over one tree with one skip rule between them.  A helper
        only one of them reaches would be compiled against a scope built for
        a different function — or not paired at all — so they are compared
        rather than read side by side.
        """
        top = _top_decl(_NESTED_HELPERS, "top")
        flat = CodeGenerator._flatten_where_fns(top)
        paired = CodeGenerator._where_fn_scopes(top)
        assert [id(f) for f in flat] == [id(w) for w, _ in paired]
        assert len(flat) == 3, (
            "the fixture must carry a helper, a NESTED helper, and a "
            "sibling, or the walk comparison proves nothing about nesting"
        )

    def test_every_mangled_registry_key_stays_in_scope(
        self, tmp_path: Path,
    ) -> None:
        """The narrowing touches only names a source program can SPELL.

        ``$`` is outside ``LOWER_IDENT``, so a ``$``-bearing registry key is
        compiler-minted — a mono clone, a ``mod$…`` reroute, a hoisted
        helper — and is never what a bare call in the source wrote.  Every
        one is admitted unconditionally, so the ownership predicate keeps
        answering "user-owned" at the sites that see a name the rewrite
        already resolved, and the change is provably confined to the
        source-spellable half of the table.

        Asserted directly rather than through behaviour: nothing downstream
        currently DEPENDS on a mangled name answering user-owned (the
        intrinsic and op branches are all exact-name matches), so a
        behaviour test would be green either way and prove nothing.
        """
        seen: list[tuple[set[str], set[str]]] = []
        original = CodeGenerator._scoped_fn_names

        def recording(
            gen: CodeGenerator, where_scope: frozenset[str], own_name: str,
        ) -> set[str]:
            out = original(gen, where_scope, own_name)
            seen.append((set(out), set(gen._fn_sigs)))
            return out

        CodeGenerator._scoped_fn_names = recording  # type: ignore[method-assign,assignment]
        try:
            build_multi_module(
                tmp_path, {"main.vera": _generic_where("get")},
            )
        finally:
            CodeGenerator._scoped_fn_names = original  # type: ignore[method-assign]

        mangled = {n for _, reg in seen for n in reg if "$" in n}
        assert mangled, (
            "the fixture emitted no mangled symbol — it must monomorphize "
            "and hoist, or this assertion is vacuous"
        )
        for scoped, registry in seen:
            missing = {n for n in registry if "$" in n} - scoped
            assert not missing, f"mangled keys withdrawn from scope: {missing}"

    def test_every_emission_door_supplies_the_decl_its_own_helpers(
        self, tmp_path: Path,
    ) -> None:
        """The DOOR invariant, over all four emission sites at once.

        Whatever a declaration's own direct ``where`` helpers are named, the
        scope it is compiled under must contain them — a body that cannot
        see its own helper is the mirror image of #1299.

        Only Pass 2's top-level loop supplies a non-empty scope today, and
        that is not an oversight at the other three: ``_hoist_clone_where_fns``
        strips every clone's helpers into standalone clone-qualified decls,
        and ``_register_modules`` runs the #991 hoist and #1014 qualification
        over every module AST, so the mono, Pass-2.5 and Pass-2.6 doors
        receive declarations whose remaining helpers are all ``$``-qualified
        (or absent).  Stated as an invariant rather than as three dead
        arguments: this goes red the moment any door starts receiving a
        declaration with a BARE helper and no scope to match.

        The fixture set covers all four doors — a local generic template
        with a nested helper tree, a monomorphized clone, an imported body,
        and a ``mod$…``-renamed shadowed one.
        """
        seen: list[tuple[str, frozenset[str], frozenset[str]]] = []
        original = CodeGenerator._compile_fn_tracked

        def recording(
            gen: CodeGenerator, decl: ast.FnDecl, **kw: Any
        ) -> str | None:
            seen.append((
                decl.name,
                frozenset(
                    w.name for w in decl.where_fns or () if "$" not in w.name
                ),
                frozenset(kw.get("where_scope", frozenset())),
            ))
            return original(gen, decl, **kw)

        CodeGenerator._compile_fn_tracked = recording  # type: ignore[method-assign,assignment]
        try:
            build_multi_module(
                tmp_path,
                {"lib.vera": _lib("public"),
                 "main.vera": (
                     "import lib(touch);\n\n"
                     + f"private fn touch(@Unit -> @Int)\n"
                       f"  requires(true)\n  ensures(true)\n"
                       f"  effects(pure)\n{{ {LOCAL} }}\n\n"
                     + _t_unused_holder("private") + "\n"
                     + _NESTED_HELPERS + "\n"
                     + "public fn main(@Unit -> @Int)\n"
                       "  requires(true)\n  ensures(true)\n"
                       "  effects(pure)\n"
                       "{ top(true) + touch(()) + lib::touch(()) }\n")},
            )
        finally:
            CodeGenerator._compile_fn_tracked = original  # type: ignore[method-assign]

        assert any("$" in name for name, _, _ in seen), (
            "no mangled symbol was compiled — the mono / mod$ doors were "
            "never reached and the invariant is vacuous there"
        )
        assert any(scope for _, _, scope in seen), (
            "no declaration got a non-empty scope — the Pass-2 door was "
            "never reached with a helper-bearing declaration"
        )
        for name, own, scope in seen:
            assert own <= scope, (
                f"{name} compiled without its own helpers in scope: "
                f"{own - scope}"
            )

    def test_a_grandchild_helper_is_not_in_its_grandparents_scope(
        self,
    ) -> None:
        """The nesting rule, at the one place it differs from a flat union.

        ``b`` is a helper of ``a``, which is a helper of ``top``.  The
        checker's ``_lookup_function_scoped`` reads each frame's DIRECT
        helpers, so ``b`` is in ``a``'s scope and in its own, and in neither
        ``top``'s nor its uncle ``c``'s.  A scope built as "every helper
        anywhere under the top-level declaration" would pass every other
        test in this file and reopen #1299 one level down.
        """
        top = _top_decl(_NESTED_HELPERS, "top")
        scopes = {w.name: s for w, s in CodeGenerator._where_fn_scopes(top)}
        assert scopes["a"] == frozenset({"a", "c", "b"})
        assert scopes["b"] == frozenset({"a", "c", "b"})
        assert scopes["c"] == frozenset({"a", "c"})


def _t_unused_holder(vis: str) -> str:
    """A ``forall<T>`` whose T is unused, declaring a ``State<Int>`` row.

    T-unused so the TEMPLATE compiles as written — a ``@T`` parameter has no
    monomorphic WASM type, so such a template is skipped and only clones are
    emitted, and clones no longer carry their helpers.  The declared row is
    what makes the scope OBSERVABLE: under ``effects(pure)`` the op registry
    is empty, so a bare ``get`` withdrawn from scope has nothing to divert
    to and falls through to the same ordinary call — green either way, and
    proving nothing.
    """
    return f"""\
{vis} forall<T> fn holder(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{{ get(()) }}
where {{
  fn get(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{ {LIB} }}
}}
"""


def _holder_driver(import_lines: str, call: str) -> str:
    """An importer whose handled body calls *call* instead of ``get(())``."""
    return _importer(import_lines).replace("get(())", call, 1)


class TestGenericTemplateKeepsItsOwnHelper:
    """The other direction of route three, at the TEMPLATE rather than a
    clone — and the case that makes the ``where_scope`` argument load-bearing.

    A ``forall<T>`` whose T appears in no parameter is compilable as written,
    so its template is emitted, un-monomorphized, with its body's bare call
    to its own ``where`` helper intact.  That helper IS in the template's
    lexical scope; drop the scope and the same narrowing that rescues the
    sibling reroutes the parent's own call to the ``State`` operation —
    the identical defect, mirrored, and returning the cell's value where the
    source calls a function that cannot produce it.

    Asserted on the emitted TEMPLATE body, not only on the runtime value.
    Monomorphization supersedes the template at every call site — the clone
    carries its own per-instantiation copy of the helper, so the template's
    WAT is emitted and never reached — and a value assertion alone is
    therefore green whatever the template contains.  The instruction stream
    is where a template compiled against the wrong scope is visible.

    A template is a LOCAL phenomenon: an imported module's generic is
    registered per-owner and emitted only as clones, so no imported template
    body is ever compiled.  That is asserted below rather than assumed,
    because it is the reason the Pass-2.5 door needs no scope at all.
    """

    _LIB = "module lib;\n\n" + _t_unused_holder("public") + """
public fn touch(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{ holder(()) }
"""

    def test_local_template_calls_its_helper(self, tmp_path: Path) -> None:
        source = _t_unused_holder("private") + "\n" + _holder_driver(
            "", "holder(())",
        )
        _, result, cg_errors = build_multi_module(
            tmp_path, {"main.vera": source},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        template = wat_fn_body(result.wat, "holder")
        assert wat_calls(template, "get")
        assert not wat_calls(template, "vera.state_get_Int")
        # And the clone the call site actually reaches answers the same.
        assert module_value(result) == ("ok", LIB)

    def test_a_template_helper_sees_its_own_siblings(
        self, tmp_path: Path,
    ) -> None:
        """The same claim one level in: a helper's body resolves against its
        SIBLINGS, so the sweep that emits the template's helpers has to give
        each one the scope of its ancestors' ``where`` blocks, not an empty
        one.  ``a`` calls ``get``; both are helpers of the same generic."""
        source = f"""\
private forall<T> fn holder(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{{ a(()) }}
where {{
  fn a(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(<State<Int>>)
  {{ get(()) }}

  fn get(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{ {LIB} }}
}}

""" + _holder_driver("", "holder(())")
        _, result, cg_errors = build_multi_module(
            tmp_path, {"main.vera": source},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        helper = wat_fn_body(result.wat, "a")
        assert wat_calls(helper, "get")
        assert not wat_calls(helper, "vera.state_get_Int")
        assert module_value(result) == ("ok", LIB)

    def test_an_imported_generic_is_emitted_only_as_clones(
        self, tmp_path: Path,
    ) -> None:
        _, result, cg_errors = build_multi_module(
            tmp_path,
            {"lib.vera": self._LIB,
             "main.vera": _holder_driver(
                 "import lib(touch);\n\n", "touch(())")},
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        emitted = wat_fn_names(result.wat)
        assert "holder" not in emitted, (
            f"an imported generic template was emitted under its bare name — "
            f"the Pass-2.5 door would then need the scope the mono door does "
            f"not; emitted: {emitted}"
        )
        clone = wat_fn_body(result.wat, "mod$lib$holder$Bool")
        assert wat_calls(clone, "mod$lib$holder$Bool$where$get")
        assert not wat_calls(clone, "vera.state_get_Int")
        assert module_value(result) == ("ok", LIB)

    def test_importer_bare_get_is_still_the_cell(
        self, tmp_path: Path,
    ) -> None:
        """The same module, with the importer keeping its own ``get(())``.

        Neither the module's helper nor its ``holder`` is in the importer's
        scope, so this half must stay the operation — the two directions
        hold at once, which is the whole claim.
        """
        assert _answer(
            tmp_path,
            {"lib.vera": self._LIB, "main.vera": _main("(touch)")},
        ) == CELL


class TestUnscopedContextDefault:
    """A ``WasmContext`` built with no ``scoped_fns`` keeps the FLAT answer.

    Every production caller supplies one — ``_compile_fn`` computes it, and
    the closure lift carries its parent's — so the default is reached only by
    a context constructed directly.  It still has to be the right default,
    and the two candidates differ in kind rather than in degree: falling back
    to ``known_fns`` reproduces the pre-#1299 behaviour, while falling back
    to an empty set would say NO name is user-owned and route every bare
    ``get`` in such a context to the operation registries — the opposite
    error, and one that turns a working program into an unresolved cell
    rather than a subtly wrong value.

    Asserted directly on the context, because the distinguishing input is a
    construction that no compilation performs.
    """

    def test_default_scope_is_the_flat_registry_not_empty(self) -> None:
        ctx = WasmContext(StringPool(), known_fns={"get"})
        assert ctx._scoped_fns == {"get"}
        # `known_fns` fallback → the user's declaration owns the name.
        # An empty fallback would answer True here.
        assert not ctx._bare_call_denotes_op("get")

    def test_an_explicit_scope_still_wins(self) -> None:
        ctx = WasmContext(
            StringPool(), known_fns={"get", "other"}, scoped_fns={"other"},
        )
        assert ctx._bare_call_denotes_op("get")
        assert not ctx._bare_call_denotes_op("other")

    def test_an_explicitly_empty_scope_is_not_confused_with_absent(
        self,
    ) -> None:
        """``scoped_fns=set()`` is a real answer — "this body owns nothing" —
        and must not be read as "no scope supplied"; a truthiness test would
        collapse the two and hand such a context the flat table."""
        ctx = WasmContext(StringPool(), known_fns={"get"}, scoped_fns=set())
        assert ctx._scoped_fns == set()
        assert ctx._bare_call_denotes_op("get")


class TestGuardRailKeepsTheFlatTable:
    """The other half of the split: ``_known_fns`` must stay flat.

    ``_translate_call``'s guard rail asks whether a RESOLVED target has a
    symbol — after mono mangling and ``mod$…`` rerouting — which is a
    question about the whole emitted module, not about one namespace.
    Narrowing that set too would turn a cross-module call into a
    ``CodegenSkip``, so a module-qualified call through a SHADOWED name is
    kept here as the live proof it did not happen: the module's body is
    emitted as ``mod$lib$touch``, a name in no namespace's source scope.
    """

    _SHADOWED_LIB = f"""\
module lib;

public fn touch(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {LIB} }}
"""

    _QUALIFIED_MAIN = f"""\
import lib(touch);

private fn touch(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ {LOCAL} }}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ lib::touch(()) * {JOIN_SCALE} + touch(()) }}
"""

    def test_qualified_call_still_reaches_the_shadowed_module_body(
        self, tmp_path: Path,
    ) -> None:
        assert _answer(
            tmp_path,
            {"lib.vera": self._SHADOWED_LIB,
             "main.vera": self._QUALIFIED_MAIN},
        ) == LIB * JOIN_SCALE + LOCAL


class TestDiscoveryScopeIsPerNamespace:
    """Discovery enters the namespace of the declaration it is WALKING.

    The seed walk covers the entry program's bodies and every module's, and
    they resolve bare names in different scopes.  Handing a module's body the
    ENTRY's scope is the mirror of the bug this issue is about: the module's
    own private declaration becomes invisible to its own code, and discovery
    names the clone from the effect operation instead.

    ``idg`` is deliberately PUBLIC and in the importer's filter.  A
    qualified-only generic's instantiations are re-discovered by the
    shadowed-module worklist, which enters the module's namespace by its own
    route — so a bare-name-owning generic is the one shape whose clone is
    named by the SEED walk alone, and the only one that can tell whether the
    seed entered the right namespace.
    """

    _LIB = """\
module lib;

private fn get(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ true }

public forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }

public fn touch(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(<State<Int>>)
{ idg(get(())) }
"""

    _MAIN = f"""\
import lib(touch, idg);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{
  handle[State<Int>](@Int = {CELL}) {{
    get(@Unit) -> {{ resume(@Int.0) }},
    put(@Int) -> {{ resume(()) }}
  }} in {{
    if touch(()) then {{ 1 }} else {{ 0 }}
  }}
}}
"""

    def test_a_module_body_resolves_in_its_own_namespace(
        self, tmp_path: Path,
    ) -> None:
        """``lib``'s ``get`` IS in ``lib``'s scope, so ``idg(get(()))`` there
        instantiates at ``Bool`` — the declaration's type, not the cell's.

        ``touch`` returns ``@Bool`` and the importer branches on it, so the
        answer distinguishes the two clones: an ``Int`` instantiation could
        not have produced a Bool for the ``if`` at all.
        """
        assert _answer(
            tmp_path, {"lib.vera": self._LIB, "main.vera": self._MAIN},
        ) == 1


class TestDiscoveryWalkContract:
    """Two properties of the discovery walk asserted on the walk itself.

    Neither is reachable from a compilation today — every declaration that
    reaches ``collect_calls_in_node`` has had its bare helper names hoisted
    or stripped, and a ``$``-bearing call name is never an operation's — so a
    behaviour test would be green either way and prove nothing.  They are the
    walk's contract all the same, and they mirror ``_scoped_fn_names``'s two
    on the codegen side, so they are asserted where they live.
    """

    @staticmethod
    def _mono(scope: frozenset[str]) -> Monomorphizer:
        ctx = MonoContext(
            generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
            adt_tp_counts={}, type_aliases={}, type_alias_params={},
            fn_ret_types={},
            fn_names=frozenset({"get", "holder", "holder$Bool$where$get"}),
            namespace_fn_names=NamespaceFnNames({None: scope}, frozenset()),
        )
        return Monomorphizer(ctx)

    def test_a_mangled_name_stays_user_owned_in_any_scope(self) -> None:
        mono = self._mono(frozenset({"holder"}))
        with mono.namespace_scope(None):
            assert mono._bare_call_is_user_fn("holder$Bool$where$get")
            # …while the bare spelling of the same helper does not.
            assert not mono._bare_call_is_user_fn("get")

    def test_a_walked_declarations_own_helpers_join_its_scope(self) -> None:
        """A bare helper name is in its parent's scope while that parent's
        body is being walked, and out of it again afterwards."""
        source = """\
private fn holder(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ get(()) }
where {
  fn get(@Unit -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  { 1 }
}
"""
        holder = _top_decl(source, "holder")
        mono = self._mono(frozenset({"holder"}))
        seen: list[bool] = []
        original = Monomorphizer._collect_calls_in_node_scoped

        def recording(inner: Monomorphizer, fn: ast.FnDecl, *a: Any) -> None:
            seen.append(inner._bare_call_is_user_fn("get"))
            return original(inner, fn, *a)

        Monomorphizer._collect_calls_in_node_scoped = recording  # type: ignore[method-assign,assignment]
        try:
            with mono.namespace_scope(None):
                assert not mono._bare_call_is_user_fn("get")
                mono.collect_calls_in_node(holder, {}, {}, {})
                assert not mono._bare_call_is_user_fn("get")
        finally:
            Monomorphizer._collect_calls_in_node_scoped = original  # type: ignore[method-assign]

        assert seen and seen[0], (
            "the helper was not in its own parent's walk scope"
        )


# ---------------------------------------------------------------------
# The helper-family leaf — the walk BOTH sides drive directly
# ---------------------------------------------------------------------

_HELPER_FAMILY_LIB = """\
module lib;

private fn get(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ true }

public fn touch(@Unit -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{ get(()) }
"""

_HELPER_FAMILY_MAIN = f"""\
import lib(touch);

private forall<T> fn outer(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ ginner(@T.0) }}
where {{
  forall<U> fn ginner(@U -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{
    handle[State<Int>](@Int = {CELL}) {{
      get(@Unit) -> {{ resume(@Int.0) }},
      put(@Int) -> {{ resume(()) }}
    }} in {{
      gsib(get(()))
    }}
  }}

  forall<V> fn gsib(@V -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {{ 7 }}
}}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{{ outer(1) }}
"""


class TestNestedHelperFamilyLeaf:
    """``collect_generic_helper_instances`` — the discovery leaf under a
    generic parent's ``where`` family, and the one walk BOTH sides drive
    directly rather than through their own loops.

    Left unscoped it fell back to the flat table on codegen AND the verifier
    at once, so the two AGREED — and a differential cannot see two sides
    being wrong together.  What it produced was a regression this branch
    introduced: ``gsib(get(()))`` inside the helper typed its argument from
    the invisible module's ``@Bool`` return, discovering ``gsib<Bool>``,
    while the (already scoped) WASM rewrite named ``gsib$Int`` from the
    ``State<Int>`` cell.  Nothing emitted matched, ``ginner``'s clone was
    skipped [E602], and ``main`` was dropped from a program that
    ``vera check`` and ``vera verify`` both passed — 8 obligations verified
    against a module with no ``main`` in it.

    So the pin is anchored on the CHECKER, not on the other side: the
    checker resolves that bare ``get(())`` to the ``State<Int>``
    operation, so ``Int`` is the type argument, and the emitted clone must
    be the one the checker's answer names.
    """

    _FILES: ClassVar[dict[str, str]] = {
        "lib.vera": _HELPER_FAMILY_LIB, "main.vera": _HELPER_FAMILY_MAIN,
    }

    def test_the_helper_family_instantiates_at_the_checkers_type(
        self, tmp_path: Path,
    ) -> None:
        """``gsib`` is cloned at ``Int`` — the cell's type — not ``Bool``.

        The assertion is on the emitted SYMBOL rather than only on the
        value, because the value alone cannot distinguish "named the right
        clone" from "named the wrong one and got dropped": a dropped `main`
        has no value at all.
        """
        _, result, cg_errors = build_multi_module(
            tmp_path, dict(self._FILES),
        )
        assert not cg_errors, f"codegen errors: {cg_errors}"
        emitted = wat_fn_names(result.wat)
        assert "outer$Int$where$gsib$Int" in emitted, (
            f"the helper family was instantiated at the wrong type; "
            f"emitted symbols: {emitted}"
        )
        # Left as an unbounded substring on purpose: this asserts ABSENCE, so
        # matching any symbol that merely contains the wrong instantiation is
        # the conservative direction.
        assert "$where$gsib$Bool" not in result.wat, (
            "a clone was named from the invisible module declaration's "
            "return type"
        )

    def test_it_runs_and_answers_the_helper(self, tmp_path: Path) -> None:
        assert _answer(tmp_path, dict(self._FILES)) == 7

    def test_rename_control_answers_the_same(self, tmp_path: Path) -> None:
        """The identical importer with only the module's declaration renamed.

        Base compiles and runs BOTH spellings; the op spelling is what this
        branch broke, so the control is what proves the fixture isolates the
        name collision rather than the helper family itself.
        """
        assert _answer(tmp_path, {
            "lib.vera": _HELPER_FAMILY_LIB.replace("get", "gettt"),
            "main.vera": _HELPER_FAMILY_MAIN,
        }) == 7

    def test_no_discovery_walk_runs_without_a_namespace_scope(
        self, tmp_path: Path,
    ) -> None:
        """The door invariant, over every walk this compilation enters.

        The equality differential compares the two sides against each other,
        so a walk both sides leave unscoped is invisible to it.  This asks a
        question neither side can answer wrongly in agreement: while the
        context carries visibility tables, no entry into the scoped region
        may run with no scope entered.  A future walk added without one
        fails here, naming its call site.
        """
        unscoped: dict[str, int] = {}
        originals = {
            name: getattr(Monomorphizer, name)
            for name in (
                "collect_calls_in_node",
                "collect_calls_in_expr",
                "collect_generic_helper_instances",
            )
        }

        # `Callable[..., Any]`, not a precise signature: `probe` stands in
        # for three DIFFERENT methods whose parameters it never inspects, so
        # the honest type is "forwards whatever it was given".  A ParamSpec
        # would say the same thing at more cost, and nothing in this repo
        # uses one.
        def wrap(original: Callable[..., Any]) -> Callable[..., Any]:
            def probe(inner: Monomorphizer, *a: Any, **kw: Any) -> Any:
                if (inner.ctx.namespace_fn_names is not None
                        and inner._scope_fn_names is None):
                    site = "?"
                    for frame in reversed(traceback.extract_stack()[:-2]):
                        if frame.filename.endswith(
                            f"vera{os.sep}monomorphize.py",
                        ):
                            continue
                        site = f"{Path(frame.filename).name}:{frame.lineno}"
                        break
                    unscoped[site] = unscoped.get(site, 0) + 1
                return original(inner, *a, **kw)
            return probe

        for name, original in originals.items():
            setattr(Monomorphizer, name, wrap(original))
        try:
            build_multi_module(tmp_path, dict(self._FILES))
        finally:
            for name, original in originals.items():
                setattr(Monomorphizer, name, original)

        assert not unscoped, (
            f"discovery walks ran with no namespace scope entered: "
            f"{sorted(unscoped)}"
        )
