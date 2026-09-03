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


from tests.codegen_helpers import _compile, _run
from tests.module_fixture_helpers import build_multi_module
from tests.verifier_helpers import _verify

# ---------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------


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




# The un-nameable argument written inside an IMPORTED module, so the [E622]
# must name THAT module's file and quote ITS line — not the entry program's.
_MODULE_OWNED_SITE = {
    "mlib.vera": """\
module mlib;

private forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn compute(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [7, 8, 9];
  idg(@Array<Int>.0[1])
}
""",
    "main.vera": """\
import mlib(compute);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  compute(())
}
""",
}


# The same un-nameable site, reached through the SHADOWED/qualified path: the
# entry program owns the bare name `idg`, so `slib`'s generic is reachable only
# as `slib::idg` and is discovered by a throwaway walker per qualified call.
_MODULE_OWNED_SHADOWED = {
    "slib.vera": """\
module slib;

public forall<T> fn idg(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{
  @T.0
}

public fn compute(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [7, 8, 9];
  idg(@Array<Int>.0[1])
}
""",
    "main.vera": """\
import slib(compute);

private fn idg(@Int -> @Int)
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
  compute(())
}
""",
}

# The argument shape that still reaches the fail-closed guard once the checker
# is the fallback: a closure literal.  The checker types it as a FUNCTION type,
# which has no clone-name spelling — a clone is named for the representation
# its parameter takes, and "a function" is not one — so both the walker and the
# checker answer nothing and the guard is what stands between the call and a
# guess.  On the base it emits `idg$Bool` and returns 42 anyway, because a
# closure handle is an i32 exactly as `Bool` is: the guess is invisible until
# the day a clone reads its type parameter.
_ANON_FN_ARG = """\
type IntToInt = fn(Int -> Int) effects(pure);

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
  let @IntToInt = idg(fn(@Int -> @Int) effects(pure) { @Int.0 * 2 });
  apply_fn(@IntToInt.0, 21)
}
"""

# [E622]'s `fix` applied literally to the above: bind the argument to a slot
# whose declared type is its own, then pass the slot reference.
_ANON_FN_ARG_FIX_APPLIED = """\
type IntToInt = fn(Int -> Int) effects(pure);

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
  let @IntToInt = fn(@Int -> @Int) effects(pure) { @Int.0 * 2 };
  let @IntToInt = idg(@IntToInt.0);
  apply_fn(@IntToInt.0, 21)
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



def _compile_checked(source: str) -> object:
    """Compile the way the CLI does — with the checker's artifacts threaded.

    ``tests.codegen_helpers._compile`` deliberately skips the type-check pass,
    so the span-keyed table [E622]'s ``fix`` reads is absent there and the
    diagnostic falls back to its shape-only wording.  The cells that assert
    the fix NAMES a type use this path, which is the one every real
    invocation takes.
    """
    from vera.checker import typecheck_with_artifacts
    from vera.codegen import compile as codegen_compile
    from vera.parser import parse_to_ast

    program = parse_to_ast(source)
    diags, arts = typecheck_with_artifacts(program, source)
    assert not [d for d in diags if d.severity == "error"], diags
    return codegen_compile(
        program, source=source,
        expr_semantic_types=arts.expr_semantic_types,
        expr_target_types=arts.expr_target_types,
    )


def _errors(diagnostics: object) -> list[tuple[str, str]]:
    return [
        (d.error_code, d.description)
        for d in diagnostics  # type: ignore[attr-defined]
        if d.severity == "error"
    ]


# ---------------------------------------------------------------------
# #1327 — the IndexExpr argument
# ---------------------------------------------------------------------


class TestUnnameableArgumentFailsClosed:
    """An argument NOTHING can name is refused, not guessed.

    The guard's reach narrowed when the checker became the fallback: an
    indexed argument (#1327) and a nested module call (#1366) are now NAMED,
    so they are inferred rather than refused, and their cells moved to
    tests/test_single_source_type_names.py.  What is left is the shape neither
    source can answer — a closure literal, whose checker type is a function
    type and so has no clone-name spelling.  The guard is therefore live, not
    vestigial: it is still the only thing between that call and a guess.
    """

    def test_compile_reports_e622(self) -> None:
        result = _compile_checked(_ANON_FN_ARG)
        errs = _errors(result.diagnostics)
        assert [c for c, _ in errs] == ["E622"], errs
        # The diagnostic names the variable, the callee, and the shape whose
        # arm is missing — the three facts that distinguish this from every
        # other codegen refusal.
        desc = errs[0][1]
        assert "'T'" in desc and "'idg'" in desc and "AnonFn" in desc, desc

    def test_compile_does_not_emit_the_guessed_clone(self) -> None:
        # Before the fix the module carried `idg$Bool` (discovery's guess) and
        # a call to `idg$Int` (the rewrite's answer).  Neither may survive a
        # refusal: an emitted clone would mean the guess still reached WAT.
        # Asserted as EXACT SETS through `wat_fn_names` / `wat_calls`, not as
        # substrings: `"idg$Bool" in wat` is a prefix test that `idg$BoolBox`
        # would satisfy, which is exactly how one clone impersonates another.
        from tests.codegen_helpers import wat_calls, wat_fn_names

        result = _compile_checked(_ANON_FN_ARG)
        emitted = sorted(n for n in wat_fn_names(result.wat) if "idg" in n)
        assert emitted == [], emitted
        for target in ("idg$Bool", "idg$IntToInt", "idg"):
            assert not wat_calls(result.wat, target), (
                f"module still calls {target!r}; emitted: {emitted}")

    def test_verify_reports_e622(self) -> None:
        # The verifier discovers instantiations through the SAME walker, so a
        # guess there reports a tier for a clone codegen never emits — a false
        # Tier 1.  It must refuse for the same reason and with the same code.
        vres = _verify(_ANON_FN_ARG)
        errs = _errors(vres.diagnostics)
        assert "E622" in [c for c, _ in errs], errs

    def test_diagnostic_locates_the_argument_not_the_function(self) -> None:
        result = _compile_checked(_ANON_FN_ARG)
        e622 = [d for d in result.diagnostics if d.error_code == "E622"]
        assert len(e622) == 1, e622
        # The caret must sit on the argument, not on `public fn main`.
        body_line = _ANON_FN_ARG.splitlines().index(
            "  let @IntToInt = idg(fn(@Int -> @Int) effects(pure) "
            "{ @Int.0 * 2 });") + 1
        assert e622[0].location.line == body_line, e622[0].location
        assert "idg(" in e622[0].source_line, e622[0].source_line


# ---------------------------------------------------------------------
# The diagnostic's own quality
# ---------------------------------------------------------------------


class TestDiagnosticIsActionable:
    """[E622]'s `fix` is applicable, and never names the type VARIABLE."""

    def test_fix_never_names_the_generic_type_variable(self) -> None:
        result = _compile_checked(_ANON_FN_ARG)
        e622 = [d for d in result.diagnostics  # type: ignore[attr-defined]
                if d.error_code == "E622"][0]
        # `let @T = …` would not compile: `T` is the generic's own variable,
        # out of scope at the call site (E170, then E121 on the reference).
        # For a closure argument nothing can name the type — a function type
        # has no clone-name spelling — so the fix takes its documented
        # shape-only form, which is still literally applicable.
        assert "let @T =" not in e622.fix, e622.fix
        assert "let @<Type> =" in e622.fix, e622.fix
        assert "'idg'" in e622.fix, e622.fix

    def test_applying_the_fix_verbatim_checks_verifies_and_runs(self) -> None:
        # The cell that makes the assertion above mean something: the program
        # the `fix` describes — bind the argument to a slot whose declared
        # type is its own, pass the slot reference — is built and driven end
        # to end.
        from tests.verifier_helpers import _verify

        result = _compile(_ANON_FN_ARG_FIX_APPLIED)
        assert _errors(result.diagnostics) == []
        assert _errors(_verify(_ANON_FN_ARG_FIX_APPLIED).diagnostics) == []
        assert _run(_ANON_FN_ARG_FIX_APPLIED, fn="main") == 42

    def test_module_owned_site_names_the_module_file(
        self, tmp_path: Path,
    ) -> None:
        # The record carries the namespace the walk was in; without it the
        # verifier pairs this module's line number with the ENTRY file's name
        # and source buffer, so the reader is sent to another file's line and
        # shown another file's text.
        from vera.verifier import verify

        from tests.module_fixture_helpers import _resolve_and_check

        program, source, main_path, resolved, _arts, check_errors = (
            _resolve_and_check(
                tmp_path / "owned", _MODULE_OWNED_SITE, "main.vera")
        )
        assert not check_errors, check_errors
        vres = verify(program, source, file=str(main_path),
                      resolved_modules=resolved)
        e622 = [d for d in vres.diagnostics if d.error_code == "E622"]
        assert len(e622) == 1, [d.description for d in vres.diagnostics]
        assert e622[0].location.file is not None
        assert e622[0].location.file.endswith("mlib.vera"), (
            e622[0].location.file)
        assert "idg(" in e622[0].source_line, e622[0].source_line

    def test_module_owned_site_names_the_module_file_at_codegen(
        self, tmp_path: Path,
    ) -> None:
        # Codegen emits E622 through its OWN path, with its own location
        # resolution: `_diag_location` reads the ENTRY file and source unless
        # the module scope is entered.  Asserting only the verifier's leg
        # would pass while codegen quoted the importer's line.
        _verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "owned_cg", _MODULE_OWNED_SITE,
        )
        assert "E622" in [c for c, _ in cg_errors], cg_errors
        e622 = [d for d in result.diagnostics if d.error_code == "E622"]
        assert len(e622) == 1, [d.description for d in result.diagnostics]
        assert e622[0].location.file is not None
        assert e622[0].location.file.endswith("mlib.vera"), (
            e622[0].location.file)
        assert "idg(" in e622[0].source_line, e622[0].source_line

    def test_shadowed_module_site_names_the_module_file(
        self, tmp_path: Path,
    ) -> None:
        # The SHADOWED/qualified path builds a throwaway walker per qualified
        # call, which starts outside any namespace scope — so without the
        # origin threaded to it every record claims the entry program and the
        # diagnostic names `main.vera`.
        _verify_errors, result, cg_errors = build_multi_module(
            tmp_path / "owned_shadow", _MODULE_OWNED_SHADOWED,
        )
        assert "E622" in [c for c, _ in cg_errors], cg_errors
        e622 = [d for d in result.diagnostics if d.error_code == "E622"]
        assert e622[0].location.file is not None
        assert e622[0].location.file.endswith("slib.vera"), (
            e622[0].location.file)

    def test_namespace_scope_restores_the_path_it_saved(self) -> None:
        # The context manager's visible-tables branch — the one every real
        # multi-module program takes — restored `_scope_fn_names` and not
        # `_namespace_path`, so the path stayed pinned after the block and a
        # later record outside any scope inherited a previously-walked
        # module's namespace.  Asserted directly: the leak is a property of
        # the manager, and a program-level cell would only see it through
        # whichever diagnostic happened to be misattributed.
        from vera.monomorphize import (
            MonoContext,
            Monomorphizer,
            NamespaceFnNames,
        )

        ctx = MonoContext(
            generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
            adt_tp_counts={}, type_aliases={}, type_alias_params={},
            fn_ret_types={},
            # A non-None table is what puts the manager on its COMMON branch —
            # the one that leaked.  Its contents are irrelevant here.
            namespace_fn_names=NamespaceFnNames({}, frozenset(), {}),
        )
        mono = Monomorphizer(ctx)
        assert mono._namespace_path is None
        with mono.namespace_scope(("outer",)):
            assert mono._namespace_path == ("outer",)
            with mono.namespace_scope(("inner",)):
                assert mono._namespace_path == ("inner",)
            assert mono._namespace_path == ("outer",), (
                "inner scope did not restore the enclosing namespace")
        assert mono._namespace_path is None, (
            "namespace_scope left the path pinned after the block")


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
                # No checker table: this drives the WALKER's own leg, which is
                # what the fail-closed contract is about.  A real context
                # always has the attribute, so its absence would be a
                # fixture artefact rather than a measurement.
                self._expr_semantic_types = None

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
