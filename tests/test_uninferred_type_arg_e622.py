"""#1327/#1366: a type argument the walker cannot name must FAIL CLOSED [E622].

Monomorphization discovery infers a generic's type arguments by naming each
call argument with its own hand-maintained walker
(``Monomorphizer._infer_vera_type_name``).  When no arm names an argument, the
type variable stays unbound — and every unbound variable was silently
substituted with the phantom-var default ``Bool``.

For a variable no parameter position determines that default is sound by
construction: ``E`` in ``result_unwrap_or(Ok(x), d)`` is not derivable from any
argument, and the emitted WASM is identical whatever it is called.  For a
variable a parameter binds DIRECTLY (``fn idg(@T -> @T)``) it is a guess, and
the guess is wrong the moment the WASM call-site rewrite — a SECOND, separately
maintained walker (``InferenceMixin._infer_vera_type``) — happens to have the
arm discovery lacks.  Discovery then registers ``idg$Bool`` while the rewrite
emits a call to ``idg$Int``: check-green, verify-clean, and the caller silently
dropped at codegen ([E602], cascading to [E620]).

Two live shapes:

* **#1327** — no ``IndexExpr`` arm on the discovery side.  ``idg(@Array<Int>.0[1])``
  discovers ``idg$Bool``; the rewrite (which resolves indexing through
  ``_infer_index_element_type``) emits ``idg$Int``.
* **#1366** — no ``ModuleCall`` arm on the discovery side.
  ``plib::gen2(plib::gen(get(())))`` discovers ``gen2$Bool``; the rewrite
  (which HAS the arm) emits ``gen2$Int``.

The fail-closed rule under test is exactly that discriminator, and its two
sides are asserted separately: a variable a direct ``@T`` parameter determines
but whose argument no arm named is [E622]; a variable no parameter determines
keeps the documented default and still compiles and runs.  A test that pinned
only the error would go green on a rule that rejected every generic call.

Not covered here, and deliberately: the walker answering the WRONG name
confidently.  #1365's type-changing pipe chain (``x |> to_b() |> gid()``) is
named ``Int`` by BOTH walkers from the pipe's left operand, so nothing is
unbound and no default is reached — fail-closed cannot see it.  That one needs
the type to come from the checker rather than from a re-inference, which is the
root fix; the cell below pins the negative so a later change that DOES make it
loud is noticed here rather than discovered downstream.

Every witness passes an ``Int``-typed argument.  ``Bool`` is the value the
phantom default supplies, so a ``Bool`` witness cannot tell a resolved
instantiation from a guessed one (TESTING.md, "inputs that cannot coincide
with a fallback value").
"""

from __future__ import annotations

from pathlib import Path

import pytest

from tests.codegen_helpers import _compile, _run
from tests.module_fixture_helpers import build_multi_module, module_value
from tests.verifier_helpers import _verify

# ---------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------

# #1327: an INDEX expression as the argument that fixes `T`.  The element type
# is `Int`, never `Bool`, so a discovered `idg$Bool` is unambiguously the
# phantom default rather than a correct answer.
_INDEX_ARG = """\
private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [7, 8, 9];
  idg(@Array<Int>.0[1])
}
"""

# The genuine phantom, which must keep compiling and running: `E` appears only
# inside `Result<T, E>` and no argument determines it.  `option_unwrap_or`'s
# sibling shape over a user ADT keeps the witness free of builtin special-casing.
_GENUINE_PHANTOM = """\
private data Res<A, B> {
  MkOk(A),
  MkErr(B)
}

private forall<T, E> fn take_ok(@Res<T, E>, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  match @Res<T, E>.0 {
    MkOk(@T) -> {
      @T.0
    },
    MkErr(@E) -> {
      @T.0
    }
  }
}

public fn main(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  take_ok(MkOk(@Int.0), 7)
}
"""

# A second parameter DOES bind the variable the first could not name.  The
# instantiation is determined, so the un-nameable sibling is not a failure and
# must not be reported.
_SIBLING_BINDS = """\
private forall<T> fn pick(@T, @T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [7, 8, 9];
  pick(@Array<Int>.0[1], 5)
}
"""

# A generic `where` helper reached ONLY through the postcondition, with
# `@Int.result` as the argument that fixes `T`.  Discovery had no `ResultRef`
# arm at all while its WASM twin has read one since #912, so `T` fell to the
# phantom default and `gok$Bool` was registered against the rewrite's
# `gok$Int` — the caller dropped at [E602], cascading to [E620].
_RESULT_REF_ONLY = """\
private fn parent(@Int -> @Int)
  requires(@Int.0 > 0)
  ensures(gok(@Int.result))
  effects(pure)
{
  @Int.0 + 5
}
where {
  forall<T> fn gok(@T -> @Bool)
    requires(true)
    ensures(true)
    effects(pure)
  {
    true
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  parent(10)
}
"""

# The same helper reached from BOTH clauses.  This one runs on the base — the
# `requires` call's slot-reference argument registers the `$Int` clone the
# postcondition's call also needs — so the defect shows there only as a WASTED
# `$Bool` clone beside it.  Kept as a distinct cell because "it runs" is
# exactly what made the gap invisible.
_RESULT_REF_WITH_SLOT_SIBLING = """\
private fn parent(@Int -> @Int)
  requires(gok(@Int.0))
  ensures(gok(@Int.result))
  effects(pure)
{
  @Int.0 + 5
}
where {
  forall<T> fn gok(@T -> @Bool)
    requires(true)
    ensures(true)
    effects(pure)
  {
    true
  }
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 15)
  effects(pure)
{
  parent(10)
}
"""

# #1365's shape, which fail-closed does NOT catch (see the module docstring).
_TYPE_CHANGING_PIPE = """\
private forall<T> fn gid(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

private fn to_b(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 > 0
}

public fn piped(@Int -> @Bool)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 |> to_b() |> gid()
}
"""

# #1366: a nested DIRECT module-generic call as the argument.
_MODULE_NESTED = {
    "plib.vera": """\
module plib;

public forall<T> fn gen(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public forall<T> fn gen2(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}
""",
    "main.vera": """\
import plib;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> {
      resume(@Int.0)
    },
    put(@Int) -> {
      resume(())
    }
  } in {
    plib::gen2(plib::gen(get(())))
  }
}
""",
}

# The SHADOWED/qualified spelling of the same shape: a local non-generic owns
# the bare `gen2`, so the module's generic is reachable only as `plib::gen2` and
# is discovered by a DIFFERENT walk (`_mono_infer_shadowed`, which builds a
# throwaway `Monomorphizer` per call).  The base drops the caller naming
# `mod$plib$gen2$Int`.  A fail-closed record that did not travel out of that
# throwaway would leave this spelling still guessing while the unshadowed one
# refused, so the cell is the reach check on the accumulator rather than a
# restatement of the cell above.
_MODULE_NESTED_SHADOWED = {
    "plib.vera": _MODULE_NESTED["plib.vera"],
    "main.vera": """\
import plib;

private fn gen2(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Int.0 + 1
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> {
      resume(@Int.0)
    },
    put(@Int) -> {
      resume(())
    }
  } in {
    plib::gen2(plib::gen(get(())))
  }
}
""",
}

# The single-level control for the module fixture: the SAME import, the same
# handler, one generic call.  It runs correctly today, so a cell that only
# asserted "the nested form errors" could not tell a targeted refusal from one
# that rejects every module generic.
_MODULE_SINGLE = {
    "plib.vera": _MODULE_NESTED["plib.vera"],
    "main.vera": """\
import plib;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  handle[State<Int>](@Int = 42007) {
    get(@Unit) -> {
      resume(@Int.0)
    },
    put(@Int) -> {
      resume(())
    }
  } in {
    plib::gen(get(()))
  }
}
""",
}


def _errors(diagnostics: object) -> list[tuple[str, str]]:
    return [
        (d.error_code, d.description)
        for d in diagnostics  # type: ignore[attr-defined]
        if d.severity == "error"
    ]


# ---------------------------------------------------------------------
# #1327 — the IndexExpr argument
# ---------------------------------------------------------------------


class TestIndexArgumentFailsClosed1327:
    """An indexed generic argument is refused, not guessed."""

    def test_compile_reports_e622(self) -> None:
        result = _compile(_INDEX_ARG)
        errs = _errors(result.diagnostics)
        assert [c for c, _ in errs] == ["E622"], errs
        # The diagnostic names the variable, the callee, and the shape whose
        # arm is missing — the three facts that distinguish this from every
        # other codegen refusal.
        desc = errs[0][1]
        assert "'T'" in desc and "'idg'" in desc and "IndexExpr" in desc, desc

    def test_compile_does_not_emit_the_guessed_clone(self) -> None:
        # Before the fix the module carried `idg$Bool` (discovery's guess) and
        # a call to `idg$Int` (the rewrite's answer).  Neither may survive a
        # refusal: an emitted clone would mean the guess still reached WAT.
        result = _compile(_INDEX_ARG)
        assert "idg$Bool" not in result.wat
        assert "$idg$Int" not in result.wat

    def test_verify_reports_e622(self) -> None:
        # The verifier discovers instantiations through the SAME walker, so a
        # guess there reports a tier for a clone codegen never emits — a false
        # Tier 1.  It must refuse for the same reason and with the same code.
        vres = _verify(_INDEX_ARG)
        errs = _errors(vres.diagnostics)
        assert "E622" in [c for c, _ in errs], errs

    def test_diagnostic_locates_the_argument_not_the_function(self) -> None:
        result = _compile(_INDEX_ARG)
        e622 = [d for d in result.diagnostics if d.error_code == "E622"]
        assert len(e622) == 1, e622
        # `idg(@Array<Int>.0[1])` is the last line of the source; the caret
        # must sit on the argument, not on `public fn main`.
        body_line = _INDEX_ARG.splitlines().index(
            "  idg(@Array<Int>.0[1])") + 1
        assert e622[0].location.line == body_line, e622[0].location
        assert "idg(" in e622[0].source_line, e622[0].source_line


# ---------------------------------------------------------------------
# #1366 — the nested module-generic argument
# ---------------------------------------------------------------------


class TestNestedModuleCallFailsClosed1366:
    """A nested direct module-generic call is refused, not guessed."""

    def test_nested_call_reports_e622(self, tmp_path: Path) -> None:
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "nested", _MODULE_NESTED,
        )
        assert "E622" in [c for c, _ in cg_errors], cg_errors
        assert "E622" in [c for c, _ in verify_errors], verify_errors
        desc = [d for c, d in cg_errors if c == "E622"][0]
        assert "'gen2'" in desc and "ModuleCall" in desc, desc

    def test_shadowed_qualified_spelling_reports_e622(
        self, tmp_path: Path,
    ) -> None:
        # Discovered by the throwaway-walker path, so this pins that the
        # record reaches the drain rather than dying with the walker.
        _verify_errors, _result, cg_errors = build_multi_module(
            tmp_path / "shadowed", _MODULE_NESTED_SHADOWED,
        )
        assert "E622" in [c for c, _ in cg_errors], cg_errors

    def test_single_level_call_still_runs(self, tmp_path: Path) -> None:
        # The control: same import, same handler, one call.  A refusal here
        # would mean the rule rejects module generics wholesale.
        verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "single", _MODULE_SINGLE,
        )
        assert verify_errors == [], verify_errors
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 42007)


# ---------------------------------------------------------------------
# The third family member the fail-closed default surfaced
# ---------------------------------------------------------------------


class TestResultRefArgumentIsNamed:
    """`@T.result` in a contract names its declared type, as the twin does.

    Found by this change rather than reported: making the default loud turned
    a silent guess into a refusal, and the refusal landed on a program the
    suite already had.  The repair is the arm, not the refusal — the walker
    CAN name a `ResultRef`, it simply had no branch for one, so mirroring the
    twin removes the guess instead of reporting it.
    """

    def test_postcondition_only_helper_runs(self) -> None:
        # Red on the base with `[E602] call target 'parent$where$gok$Int' not
        # registered`, cascading to `[E620]` and no `main` in the exports.
        result = _compile(_RESULT_REF_ONLY)
        assert _errors(result.diagnostics) == []
        assert _run(_RESULT_REF_ONLY, fn="main") == 15

    def test_no_phantom_clone_beside_the_real_one(self) -> None:
        # The sibling shape runs on the base, so a value assertion cannot see
        # the defect: what it emitted was `$gok$Int` AND a wasted `$gok$Bool`.
        from tests.codegen_helpers import wat_fn_names

        names = wat_fn_names(_compile(_RESULT_REF_WITH_SLOT_SIBLING).wat)
        gok = sorted(n for n in names if "gok$" in n)
        assert gok == ["parent$where$gok$Int"], gok
        assert _run(_RESULT_REF_WITH_SLOT_SIBLING, fn="main") == 15


# ---------------------------------------------------------------------
# The other side of the discriminator — what must STILL compile
# ---------------------------------------------------------------------


class TestGenuinePhantomStillDefaults:
    """A variable no parameter determines keeps the documented default."""

    def test_phantom_var_compiles_and_runs(self) -> None:
        # `E` is reachable only through `Res<T, E>` and `MkOk(@Int.0)` fixes
        # only `T`.  Nothing can name it, and nothing needs to: the emitted
        # WASM is identical whatever it is called.
        assert _run(_GENUINE_PHANTOM, fn="main", args=[11]) == 11

    def test_phantom_var_verifies_clean(self) -> None:
        vres = _verify(_GENUINE_PHANTOM)
        assert _errors(vres.diagnostics) == []

    def test_sibling_parameter_binding_is_not_a_failure(self) -> None:
        # `pick(@Array<Int>.0[1], 5)` — argument 0 is the un-nameable
        # `IndexExpr`, argument 1 binds `T = Int`.  The instantiation IS
        # determined, so no diagnostic and the program runs.  `pick` returns
        # `@T.1`, the FIRST parameter (De Bruijn: `.0` is the most recent),
        # so the answer is the indexed element — which also shows the value
        # of the un-nameable argument really flows through the clone rather
        # than the literal sibling standing in for it.
        result = _compile(_SIBLING_BINDS)
        assert _errors(result.diagnostics) == []
        assert _run(_SIBLING_BINDS, fn="main") == 8


# ---------------------------------------------------------------------
# The boundary: what fail-closed CANNOT see
# ---------------------------------------------------------------------


class TestConfidentlyWrongIsNotFailClosed1365:
    """#1365 is a wrong ANSWER, not an absent one, so [E622] cannot fire."""

    def test_type_changing_pipe_reaches_no_default(self) -> None:
        # Both walkers name the pipe from its LEFT operand, so `T` binds to
        # `Int` and no default is reached.  The module still compiles, and
        # still fails to load — pinned here as the boundary of this fix so a
        # later change that makes it loud is caught by this file rather than
        # by a downstream surprise.
        result = _compile(_TYPE_CHANGING_PIPE)
        assert _errors(result.diagnostics) == []
        assert "$gid$Int" in result.wat

    @pytest.mark.parametrize("fn_name", ["piped"])
    def test_type_changing_pipe_still_fails_at_load(
        self, fn_name: str,
    ) -> None:
        import wasmtime

        from vera.codegen import execute
        from vera.runtime.traps import WasmTrapError

        result = _compile(_TYPE_CHANGING_PIPE)
        with pytest.raises(
            (WasmTrapError, wasmtime.WasmtimeError, wasmtime.Trap),
        ):
            execute(result, fn_name=fn_name, args=[42])


# ---------------------------------------------------------------------
# The rewrite leg, driven directly
# ---------------------------------------------------------------------


class TestRewriteLegFailsClosed:
    """``_resolve_generic_call`` answers None rather than mangling a guess.

    Driven directly rather than through a source program on purpose.  The two
    walkers' arm sets overlap almost completely — the WASM one is today a
    superset of discovery's — so every shape that reaches the rewrite's default
    also reaches discovery's, where [E622] fires first and the compile stops
    before the rewrite runs.  A source-level witness would therefore be
    measuring discovery's refusal, not this one.  The leg still has to hold its
    own contract: the two consultors' agreement is what this whole family turns
    on, and an asymmetric default is how the family's bugs arrive.  So the
    contract is asserted where it lives.
    """

    def _stub(self) -> object:
        from vera.wasm.calls import CallsMixin
        from vera.wasm.inference import InferenceMixin

        class _Ctx(InferenceMixin, CallsMixin):  # type: ignore[misc]
            """The two mixins that own the leg, over the tables it reads."""

            def __init__(self) -> None:
                from vera import ast as a
                self._generic_fn_info = {
                    "idg": (("T",), (a.NamedType(name="T", type_args=None),)),
                }
                self._generic_constrained_vars: dict[str, frozenset[str]] = {}

        return _Ctx()

    def test_unnameable_direct_argument_yields_no_symbol(self) -> None:
        from vera import ast as a

        ctx = self._stub()
        # A `QualifiedCall` is one of the two shapes `_infer_vera_type`
        # deliberately answers None for (its `qualifier` cannot be threaded
        # through the bare-name dispatcher, so a synthesised `FnCall` could
        # match a same-named local instead).  Before the fix this returned the
        # mangled guess `idg$Bool`.
        call = a.FnCall(
            name="idg",
            args=(a.QualifiedCall(qualifier="IO", name="read_line", args=()),),
        )
        assert ctx._resolve_generic_call(call) is None  # type: ignore[attr-defined]

    def test_nameable_direct_argument_still_resolves(self) -> None:
        from vera import ast as a

        ctx = self._stub()
        call = a.FnCall(name="idg", args=(a.IntLit(value=7),))
        assert ctx._resolve_generic_call(call) == "idg$Int"  # type: ignore[attr-defined]
