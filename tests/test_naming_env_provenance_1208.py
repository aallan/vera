"""Every consumer renders against the env the CHECKER rendered under (#1208).

The naming consolidation gave the whole toolchain one renderer; these tests pin
the other half of the contract — the ENVIRONMENT it is handed.  A renderer fed a
neighbouring module's namespace, or a module env where the checker had a
``forall`` variable in scope, produces names nobody looks up, and the miss is
silent: an obligation attaches to the wrong parameter, or vanishes.

Four provenance failures, each with the adversarial probe that exhibited it:

* the verifier + SMT layer rendered an IMPORTED callee's contract slots with the
  IMPORTER's alias env (``reviewA2`` p10 / p11 / p8q);
* the verifier monomorphized an IMPORTED generic under the importer's env while
  codegen used the defining module's, so the two proved and emitted DIFFERENT
  bodies (``reviewA2`` p3 + ``pin_clone.py``);
* the monomorphizer's De Bruijn recount, the verifier's parameter declaration
  and codegen's template emission all rendered a generic's signature WITHOUT its
  ``forall`` variables, so a same-named module alias resolved through where the
  checker had a type variable (``reviewA1`` m01 / m03 / v01);
* the tester handed ``SmtContext`` the un-narrowed env while keying its own slot
  names in the narrowed one (``reviewA1`` finding 4).
"""
from __future__ import annotations

import os
import re
import tempfile

import pytest

from vera import ast, naming
from vera.checker import typecheck
from vera.codegen import compile, execute
from vera.monomorphize import Monomorphizer
from vera.parser import parse_file, parse_to_ast
from vera.resolver import ResolvedModule
from vera.runtime.traps import WasmTrapError
from vera.transform import transform
from vera.verifier import ContractVerifier, VerifyResult, verify

from tests.codegen_helpers import _compile_ok, _run
from tests.module_fixture_helpers import resolved_module as _resolved


# =====================================================================
# Helpers
# =====================================================================


def _verify_mod(source: str, modules: list[ResolvedModule]) -> VerifyResult:
    """Type-check and verify *source* against *modules*, asserting check-clean.

    Check-clean is the premise of every provenance test here: a fixture that
    fails to type-check would pass an ``errors == []`` assertion trivially.
    """
    prog = parse_to_ast(source)
    diags = typecheck(prog, source, resolved_modules=modules)
    check_errors = [d for d in diags if d.severity == "error"]
    assert not check_errors, (
        "fixture must type-check cleanly, got: "
        f"{[(d.error_code, d.description[:70]) for d in check_errors]}"
    )
    return verify(prog, source, resolved_modules=modules)


def _codes(result: VerifyResult) -> set[str]:
    return {d.error_code for d in result.diagnostics if d.severity == "error"}


def _call_pre(result: VerifyResult) -> list[object]:
    """The reified call-precondition obligations, in stream order.

    Asserting on these rather than only on the diagnostic CODE pins which
    obligation was raised and where — a code-only assertion is satisfied by
    any E501 anywhere in the program.
    """
    return [o for o in result.obligations if o.kind == "call_pre"]


def _line_of(source: str, needle: str) -> int:
    """1-based line number of the (unique) line containing *needle*.

    Computed rather than hard-coded so editing a fixture cannot silently
    re-point a location assertion at a different statement.
    """
    hits = [i for i, line in enumerate(source.splitlines(), 1) if needle in line]
    assert len(hits) == 1, f"{needle!r} is not unique in the fixture: {hits}"
    return hits[0]


def _compile_mod(source: str, modules: list[ResolvedModule]) -> object:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".vera", delete=False, encoding="utf-8",
    ) as f:
        f.write(source)
        f.flush()
        fp = f.name
    try:
        return compile(
            transform(parse_file(fp)), source=source, file=fp,
            resolved_modules=modules,
        )
    finally:
        os.unlink(fp)


_LOCAL_GET_RE = re.compile(r"local\.get\s+(\d+)")


def _local_gets(body: str) -> set[int]:
    """Every ``local.get N`` operand in *body*, as integers.

    Substring matching is not boundary-safe (PR #1224 review): ``"local.get
    2"`` is a prefix of ``local.get 20``, so a positive assertion can pass on
    a local that was never read and a negative one can go red on an unrelated
    read.
    """
    return {int(m.group(1)) for m in _LOCAL_GET_RE.finditer(body)}


def _fn_body(wat: str, symbol: str) -> str:
    """The WAT body of ``(func $symbol …)``, matched on the WHOLE symbol.

    ``wat.split("(func $pick")`` also lands on ``(func $pick$Int`` — the
    mangled clone — and on any longer name sharing the prefix, so the split
    can silently return a different function's body (PR #1224 review).
    """
    m = re.search(r"\(func \$" + re.escape(symbol) + r"(?![\w$])", wat)
    if m is None:
        raise AssertionError(f"no `(func ${symbol}` in the emitted WAT:\n{wat}")
    rest = wat[m.end():]
    nxt = rest.find("(func ")
    return rest if nxt < 0 else rest[:nxt]


def _te_spelling(te: object) -> str:
    """A type expression's source spelling, RECURSIVELY (PR #1224 review).

    A one-level ``getattr(te, "name", "?")`` renders ``Array<Option<Int>>``
    and ``Array<Option<Bool>>`` identically (both ``Array<Option>``), so a
    recount that swapped one for the other would read as agreement.
    """
    name = getattr(te, "name", None)
    if name is None:
        return "?"
    args = getattr(te, "type_args", None)
    if not args:
        return str(name)
    return f"{name}<" + ", ".join(_te_spelling(a) for a in args) + ">"


def _slot_refs(node: object) -> list[str]:
    """Every ``@Type<args>.n`` in *node*, in walk order, as source spellings."""
    out: list[str] = []

    def walk(v: object) -> None:
        if isinstance(v, ast.SlotRef):
            args = (
                "<" + ", ".join(
                    _te_spelling(a) for a in v.type_args
                ) + ">" if v.type_args else ""
            )
            out.append(f"@{v.type_name}{args}.{v.index}")
            return
        if isinstance(v, ast.Node):
            for fld in v.__dataclass_fields__:
                if fld != "span":
                    walk(getattr(v, fld))
            return
        if isinstance(v, (tuple, list)):
            for item in v:
                walk(item)

    walk(node)
    return out


# =====================================================================
# Finding 1a — an imported callee's contract renders in ITS module
# =====================================================================

# `Cnt` names DIFFERENT bodies in the library and in the importer, so a
# contract rendered in the wrong namespace lands on the wrong parameter.
_CONFLICT_LIB = """\
module clib;

type Cnt = Nat;

public fn need3(@Option<Int>, @Option<Cnt> -> @Int)
  requires(@Option<Int>.0 == Some(3))
  ensures(true)
  effects(pure)
{
  0
}
"""

# The mirror: the constrained parameter is the one the correct call satisfies.
_PICK_LIB = """\
module clib;

type Cnt = Nat;

public fn pick(@Option<Int>, @Option<Cnt> -> @Int)
  requires(@Option<Int>.0 == Some(7))
  ensures(true)
  effects(pure)
{
  0
}
"""


class TestImportedCalleeContractEnv:
    """The call obligation is rendered in the CALLEE's namespace (#1208).

    Rendered in the importer's, ``@Option<Int>`` and ``@Option<Cnt>`` either
    merge into one stack (the precondition attaches to the wrong argument, and
    the obligation VANISHES) or split one the callee merged (a spurious E501).
    Reviewer probes ``reviewA2/p10*`` (the vanish) and ``reviewA2/p11*`` (the
    spurious error).

    The obligation is asserted, not just the CODE: which call site raised it,
    which callee it names, and — for the mirror — that it was raised at all
    and discharged, rather than never existing.  The ``Precondition:`` line
    quoted in the message body is asserted too, now that #1220 resolves an
    imported clause's span against the file that declared it;
    ``tests/test_callee_contract_scope_1220_1225_1226.py`` holds that
    rendering's own suite, including the misattribution direction.
    """

    def test_violated_precondition_still_reported_bare_import(self) -> None:
        """probe p10: the E501 must not vanish because the importer renames.

        The library's ``@Option<Cnt>`` is ``Option<Nat>``, so its
        ``@Option<Int>.0`` is parameter 1 and the call passes ``Some(9)`` —
        a violation.  Under the importer's ``type Cnt = Int`` both parameters
        render ``Option<Int>``, ``@Option<Int>.0`` resolves to parameter 2
        (``Some(3)``), and the precondition proves: a false Tier-1.
        """
        source = """\
import clib(need3);

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need3(Some(9), Some(3))
}
"""
        result = _verify_mod(source, [_resolved(("clib",), _CONFLICT_LIB)])
        assert "E501" in _codes(result), (
            "the callee's precondition obligation was lost to the importer's "
            f"alias namespace; got {_codes(result)}"
        )
        violated = [o for o in _call_pre(result) if o.status == "violated"]
        assert len(violated) == 1, _call_pre(result)
        obligation = violated[0]
        assert obligation.error_code == "E501"
        # The CALL SITE in the importer, not the callee's own contract line.
        assert obligation.fn_name == "main"
        assert obligation.line == _line_of(source, "need3(Some(9)")
        # The callee's precondition, resolved onto its FIRST `Option` slot —
        # the identity the naming env decides.  Under the importer's namespace
        # this obligation is about the other parameter, or absent.
        assert obligation.expr_text.startswith("@Option<"), obligation.expr_text
        assert ".0 ==" in obligation.expr_text, obligation.expr_text
        message = next(
            d.description for d in result.diagnostics
            if d.error_code == "E501" and d.severity == "error"
        )
        assert "'need3'" in message and "'main'" in message, message
        # #1220: and the clause it quotes is the CALLEE's, read out of the
        # module that declared it — not this file's line 6 (`ensures(true)`).
        assert "requires(@Option<Int>.0 == Some(3))" in message, message

    def test_violated_precondition_still_reported_qualified_call(self) -> None:
        """probe p8q: a ``mod::fn`` call takes the same registry, same fix."""
        source = """\
import clib;

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  clib::need3(Some(9), Some(3))
}
"""
        result = _verify_mod(source, [_resolved(("clib",), _CONFLICT_LIB)])
        assert "E501" in _codes(result), (
            f"qualified call lost its precondition obligation: {_codes(result)}"
        )
        violated = [o for o in _call_pre(result) if o.status == "violated"]
        assert len(violated) == 1, _call_pre(result)
        assert violated[0].fn_name == "main"
        assert violated[0].line == _line_of(source, "clib::need3(")
        assert "'need3'" in next(
            d.description for d in result.diagnostics
            if d.error_code == "E501" and d.severity == "error"
        )

    def test_satisfied_precondition_is_not_spuriously_reported(self) -> None:
        """probe p11: the mirror — a CORRECT program must stay clean.

        Same shape, but the argument the callee's contract names IS the one it
        constrains.  Under the importer's env the reference resolved onto the
        other parameter and the call E501'd for no reason.
        """
        source = """\
import clib(pick);

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Some(7), Some(3))
}
"""
        result = _verify_mod(source, [_resolved(("clib",), _PICK_LIB)])
        assert not _codes(result), (
            f"correct cross-module call spuriously rejected: {_codes(result)}"
        )
        # A DISCHARGED call precondition is reified as nothing at all (only
        # violations and Tier-3 demotions become `call_pre` obligations), so
        # "clean" has to be read two ways: nothing failed, and nothing was
        # quietly demoted to a runtime check either.
        assert not _call_pre(result), _call_pre(result)
        # And the obligation is still LIVE on this call — swap the arguments
        # so the parameter the callee constrains is the wrong one, and the
        # same program must be rejected.  Without this, a verifier that had
        # stopped checking imported preconditions altogether would pass above.
        swapped = source.replace("pick(Some(7), Some(3))", "pick(Some(3), Some(7))")
        control = _verify_mod(swapped, [_resolved(("clib",), _PICK_LIB)])
        assert "E501" in _codes(control), (
            "the imported callee's precondition is not being checked at all: "
            f"{_codes(control)}"
        )
        violated = [o for o in _call_pre(control) if o.status == "violated"]
        assert len(violated) == 1, _call_pre(control)
        assert violated[0].line == _line_of(swapped, "pick(Some(3)")

    def test_control_no_alias_conflict_still_reports(self) -> None:
        """Control: with no same-named alias the two envs agree, and always did.

        Present so a fix that merely disabled the cross-module obligation would
        fail here rather than pass the two probes above by omission.
        """
        result = _verify_mod("""\
import dlib(need3);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need3(Some(9), Some(3))
}
""", [_resolved(("dlib",), """\
module dlib;

public fn need3(@Option<Int>, @Option<Nat> -> @Int)
  requires(@Option<Int>.0 == Some(3))
  ensures(true)
  effects(pure)
{
  0
}
""")])
        assert "E501" in _codes(result)


# =====================================================================
# Finding 1b — an imported generic clones in ITS module's namespace
# =====================================================================

_GENERIC_LIB = """\
module blib;

type Cnt = Int;

public forall<T> fn twolen(@Array<Cnt>, @Array<T> -> @Nat)
  requires(array_length(@Array<T>.0) == 2)
  ensures(@Nat.result == 2)
  effects(pure)
{
  array_length(@Array<Int>.0)
}
"""

_GENERIC_MAIN = """\
import blib(twolen);

type Cnt = Nat;

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  twolen(array_range(0, 5), array_range(0, 2))
}
"""


class TestImportedGenericCloneEnv:
    """The verifier clones an imported generic in the DEFINING module's env.

    Codegen already does (``_clone_alias_env``, #1208).  While the verifier did
    not, the two sides monomorphized the same template into different functions
    — the De Bruijn recount permutes the parameters — so the verifier proved a
    body codegen never emitted.  Reviewer probes ``reviewA2/p3*`` (verify green,
    trap at run) and ``reviewA2/pin_clone.py`` (the recount itself).
    """

    def test_lying_imported_generic_contract_is_an_honest_e500(self) -> None:
        """The false Tier-1 this gap produced, in its smallest form.

        In ``blib``'s namespace ``@Array<Cnt>`` is ``Array<Int>`` and
        ``@Array<T>`` is not, so ``requires`` constrains parameter 2 while the
        body reads parameter 1 — the ``ensures`` is FALSE.  In the importer's
        (``type Cnt = Nat``) the recount merges both references onto one slot,
        the contract looks self-consistent, and it verifies clean while the
        emitted clone violates its postcondition at run time.
        """
        result = _verify_mod(_GENERIC_MAIN, [_resolved(("blib",), _GENERIC_LIB)])
        assert "E500" in _codes(result), (
            "an imported generic's lying postcondition proved clean — the "
            f"clone was verified in the importer's namespace; got {_codes(result)}"
        )

    def test_verifier_clone_matches_codegen_clone(self) -> None:
        """The direct recount differential (``pin_clone.py``, in-tree).

        Compares the slot references the VERIFIER's monomorphization produces
        for an imported generic against the ones CODEGEN produces for the same
        template at the same instantiation.  A unit test on either side alone
        cannot see the desync — that is the whole point of a differential.
        """
        module = _resolved(("blib",), _GENERIC_LIB)
        prog = parse_to_ast(_GENERIC_MAIN)
        typecheck(prog, _GENERIC_MAIN, resolved_modules=[module])

        clones: dict[str, list[str]] = {}
        original = Monomorphizer.monomorphize_fn

        def record(side: str):
            def patched(self, decl, concrete_types, alias_env=None):
                out = original(self, decl, concrete_types, alias_env)
                if decl.name == "twolen":
                    clones.setdefault(side, _slot_refs(out))
                return out
            return patched

        try:
            Monomorphizer.monomorphize_fn = record("verifier")  # type: ignore[method-assign]
            verify(prog, _GENERIC_MAIN, resolved_modules=[module])
            Monomorphizer.monomorphize_fn = record("codegen")  # type: ignore[method-assign]
            _compile_mod(_GENERIC_MAIN, [module])
        finally:
            Monomorphizer.monomorphize_fn = original  # type: ignore[method-assign]

        assert "verifier" in clones and "codegen" in clones, (
            f"both sides must clone the imported generic; saw {sorted(clones)}"
        )
        assert clones["verifier"] == clones["codegen"], (
            "the verifier and codegen monomorphize the imported generic into "
            f"DIFFERENT bodies: {clones['verifier']} vs {clones['codegen']}"
        )

    def test_imported_generic_run_agrees_with_verify(self) -> None:
        """The runtime oracle for the same clone.

        The emitted clone's own postcondition guard fails, which is what the
        E500 above now predicts — verify and run agree on the same body.

        A CONTROL, not a proving test: codegen always named this clone in the
        defining module's env, so the trap is green before and after.  Its job
        is to show the E500 is HONEST — that the verifier now agrees with the
        emitted code rather than merely reporting more.
        """
        module = _resolved(("blib",), _GENERIC_LIB)
        result = _compile_mod(_GENERIC_MAIN, [module])
        errors = [
            d for d in result.diagnostics  # type: ignore[attr-defined]
            if d.severity == "error"
        ]
        assert not errors, f"unexpected codegen errors: {errors}"
        # `WasmTrapError.kind` is the classification, not the message text
        # (PR #1224 review): matching on substrings would also accept a
        # divide-by-zero or an out-of-bounds trap that happened to mention
        # them, and would go red on a message rewording that changes nothing.
        try:
            execute(result, fn_name="main")  # type: ignore[arg-type]
        except WasmTrapError as exc:
            assert exc.kind == "contract_violation", (
                f"expected the clone's postcondition guard to fail, "
                f"got kind={exc.kind!r}: {exc}"
            )
        else:  # pragma: no cover — a pass here would contradict the E500
            raise AssertionError(
                "the emitted clone satisfied a postcondition the verifier "
                "reports as violated: verify and run disagree"
            )

    def test_clone_construction_enters_the_modules_source_scope(self) -> None:
        """The clone-construction door pairs both scopes, like its siblings.

        Codegen enters an imported module's namespace at five doors; the
        alias scope alone leaves ``file``/``source`` on the IMPORTER, so a
        diagnostic raised there would pair the importer's path with
        module-local coordinates — the #1186/#1189 attribution failure, and
        the reason the E618 dedup (keyed on the resolved location) once
        merged two modules' reports.  Nothing inside this door reports
        today; the pairing is what keeps that true of whatever moves into
        it, so it is asserted structurally rather than through a
        diagnostic that does not exist.
        """
        from vera.codegen.core import CodeGenerator

        module = _resolved(("blib",), _GENERIC_LIB)
        gen = CodeGenerator(
            source=_GENERIC_MAIN, file="main.vera", resolved_modules=[module],
        )
        gen.compile_program(parse_to_ast(_GENERIC_MAIN))
        assert gen.file == "main.vera"
        with gen._clone_alias_env(("blib",)):
            assert gen.file == str(module.file_path), gen.file
            assert gen.source == _GENERIC_LIB
        assert gen.file == "main.vera", "the source scope was not restored"
        assert gen.source == _GENERIC_MAIN


class TestImportedNestedGenericOriginEnv:
    """A generic nested under an imported NON-generic function (#1208 round 2).

    ``_generic_origins`` records such a generic under the lexical chain that
    names it (``ng::outer$where$mid``) — there is no entry for the bare
    ancestor ``ng::outer``.  Both the discovery-time recount and the
    verification-time clone looked the origin up under a key that could never
    hit (the chain's first segment; the helper's bare name), fell back to the
    IMPORTER's env, and rendered the helper's alias-typed parameters in a
    namespace where the same alias names a different type.  Reviewer probe
    ``m4``.
    """

    _NG = """\
module ng;

type Elem = Nat;

public fn outer(@Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  mid(@Int.0)
}
where {
  forall<T> fn mid(@T -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    inner(@T.0, Some(3))
  }
  where {
    forall<V> fn inner(@V, @Option<Elem> -> @Int)
      requires(true)
      ensures(true)
      effects(pure)
    {
      0
    }
  }
}
"""

    _MAIN = """\
import ng;

type Elem = Bool;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  outer(1)
}
"""

    def test_nested_generic_clones_in_the_defining_modules_namespace(
        self,
    ) -> None:
        """Every clone of ``ng``'s nested generic renders ``Elem`` as ``Nat``.

        The importer declares ``type Elem = Bool``, so the two namespaces give
        the helper's ``@Option<Elem>`` parameter two different names — and the
        wrong one is a name neither the checker nor codegen ever binds.  The
        env is inspected through what it RENDERS rather than by identity: the
        failure is a rendering, and an identity assertion would pass for any
        env that happened to be the right object for the wrong reason.
        """
        from vera import naming
        from vera.monomorphize import Monomorphizer

        seen: list[tuple[str, str]] = []
        original = Monomorphizer.monomorphize_fn

        def patched(
            self: Monomorphizer, decl: ast.FnDecl,
            concrete_types: tuple[str, ...], alias_env: object = None,
        ) -> ast.FnDecl:
            seen.append((decl.name, "<default>" if alias_env is None
                         else naming.type_arg_name(
                             ast.NamedType(name="Elem", type_args=None),
                             alias_env)))  # type: ignore[arg-type]
            return original(self, decl, concrete_types, alias_env)  # type: ignore[arg-type]

        Monomorphizer.monomorphize_fn = patched  # type: ignore[method-assign]
        try:
            result = _verify_mod(self._MAIN, [_resolved(("ng",), self._NG)])
        finally:
            Monomorphizer.monomorphize_fn = original  # type: ignore[method-assign]

        assert not _codes(result), _codes(result)
        inner_envs = {rendered for name, rendered in seen if name == "inner"}
        assert inner_envs, (
            f"the nested generic was never monomorphized; saw {seen}"
        )
        assert inner_envs == {"Nat"}, (
            "a clone of ng's nested generic was built in the IMPORTER's alias "
            f"namespace (Elem = Bool): {sorted(inner_envs)}"
        )
        # The ancestor's own clone was already right — asserted so a
        # regression there cannot hide behind the helper's assertion.
        assert {
            rendered for name, rendered in seen if name.endswith("mid")
        } == {"Nat"}, seen


# =====================================================================
# Finding 1c — a `forall` variable shadows a same-named module alias
# =====================================================================

class TestForallShadowNarrowing:
    """``forall<T>`` shadows ``type T = …`` everywhere the signature renders.

    The checker binds the type parameter first (``_check_fn`` step 1), so
    ``forall<T> fn f(@Option<T>, @Option<Int>)`` binds TWO stacks for it.  Every
    consumer that rendered the same signature against the bare module env saw
    ONE, and silently resolved references onto the wrong parameter.  Reviewer
    probes ``reviewA1/m01``, ``m03`` and ``v01``.
    """

    _M01 = """\
type T = Int;

public forall<T> fn pick(@Option<T>, @Option<Int> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<T>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(pick(Some(11), Some(22)), 0)
}
"""

    def test_mono_clone_reads_the_parameter_the_checker_bound(self) -> None:
        """probe m01: ``@Option<T>.0`` is parameter 1 — the run must give 11.

        Without the narrowing the recount saw one ``Option<Int>`` stack, kept
        the index, and the clone read parameter 2: 22.
        """
        assert _run(self._M01) == 11

    def test_mono_clone_control_without_shadowing(self) -> None:
        """probe m01_control: the same program with the alias renamed.

        Green before and after — it is here so the assertion above is known to
        be about the SHADOWING and not about De Bruijn resolution generally.
        """
        assert _run(self._M01.replace("type T = Int;", "type TT = Int;")) == 11

    def test_let_binder_inside_a_generic_body(self) -> None:
        """probe m03: the same collapse reached through a body ``let``.

        The ``let @Option<Int>`` interposes a binding that only counts for the
        reference when the two stacks are (wrongly) one.
        """
        assert _run("""\
type T = Int;

public forall<T> fn pick(@Option<T> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = Some(99);
  @Option<T>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  option_unwrap_or(pick(Some(11)), 0)
}
""") == 11

    _V01 = """\
type T = Int;

public forall<T> fn f(@Array<T>, @Array<Int> -> @Nat)
  requires(array_length(@Array<T>.0) == 3 && array_length(@Array<Int>.0) == 7)
  ensures(@Nat.result == 999)
  effects(pure)
{
  array_length(@Array<T>.0)
}

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([1, 2, 3], [1, 2, 3, 4, 5, 6, 7])
}
"""

    def test_verifier_does_not_prove_from_collapsed_premises(self) -> None:
        """probe v01: a FALSE Tier-1, because the premises became unsatisfiable.

        The two ``requires`` conjuncts constrain different parameters.  Collapse
        them onto one slot and it must have length 3 AND 7 — from which anything
        follows, including the false ``ensures(@Nat.result == 999)``.
        """
        prog = parse_to_ast(self._V01)
        assert not [
            d for d in typecheck(prog, self._V01) if d.severity == "error"
        ]
        result = verify(prog, self._V01)
        codes = {d.error_code for d in result.diagnostics if d.severity == "error"}
        assert "E500" in codes, (
            "a postcondition that is false for every input proved at Tier 1: "
            f"the premises collapsed onto one slot; got {codes}"
        )

    def test_verifier_control_without_shadowing(self) -> None:
        """probe v01_control: the same program, alias renamed — E500 both ways."""
        src = self._V01.replace("type T = Int;", "type TT = Int;")
        prog = parse_to_ast(src)
        result = verify(prog, src)
        assert "E500" in {
            d.error_code for d in result.diagnostics if d.severity == "error"
        }

    def test_uninstantiated_generic_template_reads_parameter_one(self) -> None:
        """Codegen emits (and EXPORTS) the template, so it must name it right.

        A never-instantiated generic still reaches ``_compile_fn``; under the
        bare module env its two ``Option`` parameters merged and the exported
        body returned the second one.
        """
        wat = _compile_ok("""\
type T = Int;

public forall<T> fn pick(@Option<T>, @Option<Int> -> @Option<T>)
  requires(true)
  ensures(true)
  effects(pure)
{
  @Option<T>.0
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}
""").wat
        body = _fn_body(wat, "pick")
        assert _local_gets(body) == {0}, (
            "the exported template returns the wrong parameter:\n" + body
        )


class TestVerifierScopeIsTheSlotTableScope:
    """The narrowing, as a CROSS-COMPONENT differential (#1208 round 2).

    ``ContractVerifier._fn_naming_scope`` was green both ways: replace it with
    ``return env`` and the full suite still passed.  Every one of its call
    sites renders a signature and the references into that signature against
    the SAME environment, so a wrong scope is wrong CONSISTENTLY — the
    verifier proves a self-consistent story about parameters the checker
    never bound, and nothing inside the verifier can see it.

    What sees it is a second component that answers the same question:
    :func:`vera.slots.slot_table` is the binding table ``vera check
    --explain-slots`` and the LSP report, and it is pinned to the checker by
    ``test_slot_naming_differential.py``.

    The two are independent on the axis under test — whether each component
    NARROWS by the ``forall`` variables, and by which ones — but NOT
    end-to-end: both bottom out in :func:`vera.slots.fn_slot_scope` and
    :func:`vera.naming.slot_name`, so a defect in the shared renderer moves
    both sides together and the equality still holds (PR #1224 round-3).  The
    hand-derived LITERAL assertion beside each comparison is what closes that:
    it names the exact strings the checker's rule produces, so a
    both-sides-wrong rendering fails on the literal even when the differential
    agrees.  Neither assertion is redundant — the equality catches a
    one-sided narrowing, the literal catches a shared one.
    """

    _SHADOWED_GENERIC = """\
type T = Int;
type Pos = { @Int | @Int.0 > 0 };

public forall<T> fn g(@Option<Int>, @Option<T> -> @Pos)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}
"""

    @staticmethod
    def _declared_slots(source: str) -> list[tuple[str, int]]:
        """``(slot name, De Bruijn index)`` per parameter, as the VERIFIER
        declares them into its ``SlotEnv``/``SmtContext``.

        ``_count_slots`` is called exactly once per parameter, at the point
        the ``@Name.n`` Z3 constant is named, on both paths that declare a
        function's parameters — so recording it records the names the verifier
        actually reasons under, not a re-derivation of them.
        """
        seen: list[tuple[str, int]] = []
        original = ContractVerifier._count_slots

        def patched(env: object, type_name: str) -> int:
            index = original(env, type_name)  # type: ignore[arg-type]
            seen.append((type_name, index))
            return index

        # Re-wrapped in `staticmethod` on BOTH sides: `_count_slots` is a
        # staticmethod, and restoring the bare function would rebind it as an
        # instance method — a leak that fails unrelated tests later in the
        # session rather than this one.
        ContractVerifier._count_slots = staticmethod(  # type: ignore[method-assign]
            patched)
        try:
            program = parse_to_ast(source)
            verify(program, source)
        finally:
            ContractVerifier._count_slots = staticmethod(  # type: ignore[method-assign]
                original)
        return seen

    @staticmethod
    def _slot_table_slots(
        decl: ast.FnDecl, env: object, forall_vars: object,
    ) -> list[tuple[str, int]]:
        """The same list, derived from :func:`vera.slots.slot_table`.

        The table is ``{name: [1-based parameter positions, slot-0-first]}``,
        so a parameter's De Bruijn index is its distance from the END of its
        own group — which makes this a comparison of the ORDERING as well as
        of the names.
        """
        from vera.slots import slot_table

        table = slot_table(decl.params, env, forall_vars)  # type: ignore[arg-type]
        out: list[tuple[str, int]] = []
        for position in range(1, len(decl.params) + 1):
            name = next(n for n, ps in table.items() if position in ps)
            out.append(
                (name, len(table[name]) - 1 - table[name].index(position)))
        return out

    def test_generic_signature_declares_the_slot_table_names(self) -> None:
        """The differential: verifier parameter names == the slot table's.

        ``_check_generic_refined_return`` is the one path that declares a
        STILL-GENERIC signature's parameters (an instantiated generic is
        verified through its clones, whose ``forall_vars`` are already gone),
        so it is where the narrowing is observable end to end.  Under
        ``type T = Int`` the two ``Option`` parameters render as one stack
        without it and two with it, and the checker keeps two.
        """
        from tests.naming_helpers import alias_env_from_declarations

        source = self._SHADOWED_GENERIC
        program = parse_to_ast(source)
        decl = next(
            tld.decl for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "g"
        )
        env = alias_env_from_declarations(program.declarations)

        observed = self._declared_slots(source)
        expected = self._slot_table_slots(decl, env, decl.forall_vars)
        assert observed == expected, (
            "the verifier declared this generic's parameters under names the "
            f"slot table does not use: verifier={observed} table={expected}"
        )
        # Named, not merely equal: two equal-but-collapsed sides would also
        # satisfy the comparison above if BOTH components lost the narrowing.
        assert observed == [("Option<Int>", 0), ("Option<T>", 0)], observed

    def test_where_helper_scope_accumulates_its_ancestors_forall_vars(
        self,
    ) -> None:
        """The ``enclosing`` half, against the checker-side accumulation.

        A ``where`` helper sees its parent's ``forall`` variables as well as
        its own — ``_check_fn`` ADDS to one shared type-parameter map — so the
        scope the verifier renders a helper's signature in must be the scope
        :func:`vera.slots.fn_scopes` accumulates for it.  Drop the
        accumulation and the helper's ``@Option<T>`` renders ``Option<Int>``,
        merging with the sibling parameter the checker kept apart.

        Independent on the ACCUMULATION axis, shared below it: both sides
        reach :func:`vera.slots.fn_slot_scope`, so the two literal renderings
        asserted at the end are the half of this test that a shared-renderer
        defect cannot satisfy (PR #1224 round-3).
        """
        from vera import naming
        from vera.slots import fn_scopes, fn_slot_scope

        from tests.naming_helpers import alias_env_from_declarations

        source = """\
type T = Int;

private forall<T> fn parent(@T -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(Some(@T.0), Some(2))
}
where {
  fn helper(@Option<T>, @Option<Int> -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    0
  }
}
"""
        program = parse_to_ast(source)
        parent = next(
            tld.decl for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "parent"
        )
        helper = (parent.where_fns or ())[0]
        env = alias_env_from_declarations(program.declarations)

        scope = ContractVerifier._fn_naming_scope(env, helper, (parent,))
        inherited = next(
            in_scope for fn, in_scope, _ in fn_scopes(parent) if fn is helper
        )
        assert scope == fn_slot_scope(env, inherited), (
            "the verifier's helper scope is not the accumulation "
            "`fn_scopes` performs, so the two surfaces disagree about which "
            "module aliases a helper's signature still sees"
        )
        # The rendering that disagreement produces, stated outright.
        assert naming.slot_name(helper.params[0], scope) == "Option<T>"
        assert naming.slot_name(helper.params[1], scope) == "Option<Int>"


class TestMonoPostSubstitutionScope:
    """The recount's POST side narrows by the vars the CLONE declares.

    ``_compute_scoped_reindex`` narrowed only the pre-substitution side, on
    the stated ground that "the clone carries ``forall_vars=None``".  That is
    true of the function being cloned and false one level down:
    ``monomorphize_fn`` clears only the top declaration's variables, so a
    ``where`` helper declared ``forall<U>`` still carries them in the clone —
    and both consumers narrow by them when they re-render it.  The names the
    recount minted for that helper were therefore names nobody looks up
    (#1208 round 2).

    Narrowing instead by the vars that merely SURVIVE the substitution
    (``v not in mapping``) is a different rule, and wrong in the same
    direction one case further out — see
    ``test_post_side_matches_consumers_under_an_identity_mapping``.

    Independent of the consumers on the SCOPE axis (which variables the two
    sides narrow by), shared below it: both call
    :func:`vera.slots.fn_slot_scope` and :func:`vera.naming.slot_name`.  The
    literal assertion beside the comparison is what a shared-renderer defect
    cannot satisfy (PR #1224 round-3).
    """

    _SRC = """\
type U = Int;

private forall<T> fn parent(@T, @Option<Int> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(Some(true), @Option<Int>.0, false)
}
where {
  forall<U> fn helper(@Option<U>, @Option<Int>, @U -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    0
  }
}
"""

    def test_helper_post_names_are_the_names_the_clone_is_read_under(
        self,
    ) -> None:
        from vera import naming
        from vera.monomorphize import MonoContext, Monomorphizer
        from vera.slots import fn_slot_scope

        from tests.naming_helpers import alias_env_from_declarations

        program = parse_to_ast(self._SRC)
        parent = next(
            tld.decl for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "parent"
        )
        helper = (parent.where_fns or ())[0]
        env = alias_env_from_declarations(program.declarations)

        minted: dict[int, str | None] = {}
        original = Monomorphizer._substituted_slot_name

        def patched(
            self: Monomorphizer, te: ast.TypeExpr,
            mapping: dict[str, str], scope: object,
        ) -> str | None:
            name = original(self, te, mapping, scope)  # type: ignore[arg-type]
            minted[id(te)] = name
            return name

        Monomorphizer._substituted_slot_name = patched  # type: ignore[method-assign]
        try:
            mono = Monomorphizer(MonoContext(
                generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
                adt_tp_counts={}, type_aliases={}, type_alias_params={},
                fn_ret_types={},
            ))
            clone = mono.monomorphize_fn(parent, ("Int",), env)
        finally:
            Monomorphizer._substituted_slot_name = original  # type: ignore[method-assign]

        clone_helper = (clone.where_fns or ())[0]
        # The premise the old justification got wrong: substitution clears the
        # cloned function's variables, not its helpers'.
        assert clone_helper.forall_vars == ("U",), clone_helper.forall_vars

        observed = [minted[id(te)] for te in helper.params]
        # What the consumers will look the clone's helper up under: the clone's
        # own signature, rendered in the scope its surviving `forall` variables
        # create — the same narrowing `slot_table` and `WasmSlotEnv` apply.
        expected = [
            naming.slot_name(te, fn_slot_scope(env, clone_helper.forall_vars))
            for te in clone_helper.params
        ]
        assert observed == expected, (
            "the recount minted post-substitution names for the helper that "
            f"its consumers do not rebuild: recount={observed} "
            f"consumers={expected}"
        )
        # Named outright: under `type U = Int` the un-narrowed post side
        # rendered `Option<Int>`, merging the helper's first two parameters.
        assert observed == ["Option<U>", "Option<Int>", "U"], observed

    # The helper SHADOWS its parent's type variable, so the parent's mapping
    # has a key with the helper's variable's name.  `surviving` (`v not in
    # mapping`) drops it; the clone still declares it, so the consumers do
    # not.
    _SHADOW_SRC = """\
type T = Int;

private forall<T> fn parent(@Option<T>, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  helper(None, 0)
}
where {
  forall<T> fn helper(@Option<T>, @Int -> @Int)
    requires(true)
    ensures(true)
    effects(pure)
  {
    0
  }
}
"""

    def test_post_side_matches_consumers_under_an_identity_mapping(
        self,
    ) -> None:
        """The post side is the CLONE's declared vars, not the surviving ones.

        A generic instantiated at a type spelled with its OWN type variable's
        name — a module alias called ``T``, so ``forall<T> fn parent`` is
        cloned at ``T`` — makes the mapping the identity.  Every declared
        variable is a key of ``mapping`` whatever it maps to, so ``v not in
        mapping`` drops the helper's shadowing ``T``; substitution leaves the
        helper's ``@Option<T>`` textually alone, so the post side resolved
        ``T`` through the module alias and minted ``Option<Int>`` where the
        consumers, narrowing by the clone's own ``forall_vars=('T',)``,
        rebuild ``Option<T>`` (PR #1224 round-3).

        Pinned here rather than end to end: every program that reaches this
        shape has a generic ``where``-helper under a generic parent, which
        codegen drops before it can run
        (`#1223 <https://github.com/aallan/vera/issues/1223>`_).
        """
        from vera import naming
        from vera.monomorphize import MonoContext, Monomorphizer
        from vera.slots import fn_slot_scope

        from tests.naming_helpers import alias_env_from_declarations

        program = parse_to_ast(self._SHADOW_SRC)
        parent = next(
            tld.decl for tld in program.declarations
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "parent"
        )
        helper = (parent.where_fns or ())[0]
        env = alias_env_from_declarations(program.declarations)

        minted: dict[int, str | None] = {}
        original = Monomorphizer._substituted_slot_name

        def patched(
            self: Monomorphizer, te: ast.TypeExpr,
            mapping: dict[str, str], scope: object,
        ) -> str | None:
            name = original(self, te, mapping, scope)  # type: ignore[arg-type]
            minted[id(te)] = name
            return name

        Monomorphizer._substituted_slot_name = patched  # type: ignore[method-assign]
        try:
            mono = Monomorphizer(MonoContext(
                generic_decls={}, ctor_to_adt={}, ctor_tp_indices={},
                adt_tp_counts={}, type_aliases={}, type_alias_params={},
                fn_ret_types={},
            ))
            # The IDENTITY instantiation: `T` names the module alias here.
            clone = mono.monomorphize_fn(parent, ("T",), env)
        finally:
            Monomorphizer._substituted_slot_name = original  # type: ignore[method-assign]

        clone_helper = (clone.where_fns or ())[0]
        assert clone_helper.forall_vars == ("T",), clone_helper.forall_vars

        observed = [minted[id(te)] for te in helper.params]
        expected = [
            naming.slot_name(te, fn_slot_scope(env, clone_helper.forall_vars))
            for te in clone_helper.params
        ]
        assert observed == expected, (
            "under an identity mapping the recount minted names the "
            f"consumers do not rebuild: recount={observed} "
            f"consumers={expected}"
        )
        # Named outright, so a both-sides-collapsed rendering cannot pass:
        # `T` is the helper's OWN type parameter, not the module alias.
        assert observed == ["Option<T>", "Int"], observed


# =====================================================================
# Finding 1d — the tester's SmtContext gets the NARROWED scope
# =====================================================================

class TestTesterSmtScope:
    """``_generate_inputs`` keys its slot names in the function's own scope, so
    the ``SmtContext`` that RESOLVES those names must hold the same scope.

    Handed the un-narrowed module env, ``_translate_slot_ref`` looks a
    ``requires`` clause's ``@T.n`` up under a key the bind side never pushed —
    latent until a ``forall`` variable shadows a same-named module alias.

    The fixture puts ``T`` in ARGUMENT position (``@Box<T>``, where
    ``type Box<X> = Int`` keeps the semantic type Z3-representable), because
    that is where the shadowing changes a rendering: a bare ``@T`` head is
    alias-opaque on both sides and would make the narrowing unobservable
    (#1208 round 2).  The two ``requires`` conjuncts then constrain different
    parameters when the scope is right and ONE parameter to two different
    values when it is wrong — so the generator's own output distinguishes the
    two, rather than only the environment it was handed.
    """

    _SRC = """\
type T = Int;
type Box<X> = Int;

public forall<T> fn f(@Box<T>, @Box<Int> -> @Int)
  requires(@Box<T>.0 == 5 && @Box<Int>.0 == 9)
  ensures(true)
  effects(pure)
{
  @Box<T>.0
}
"""

    def _decl_and_env(self) -> tuple[ast.FnDecl, object]:
        from tests.naming_helpers import alias_env_from_declarations

        prog = parse_to_ast(self._SRC)
        decl = next(
            tld.decl for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
        )
        return decl, alias_env_from_declarations(prog.declarations)

    def test_generated_inputs_satisfy_both_conjuncts(self) -> None:
        """The behavioural pin: two parameters, two constraints, one answer.

        Rendered without the narrowing, ``@Box<T>`` and ``@Box<Int>`` are one
        stack: both references resolve onto parameter 2, which must then be
        ``5`` and ``9`` at once.  The precondition becomes unsatisfiable and
        the generator returns NO inputs — every contract-driven trial for this
        function silently disappears.
        """
        from vera.tester import _generate_inputs
        from vera.types import INT

        decl, env = self._decl_and_env()
        assert _generate_inputs(decl, [INT, INT], 1, env) == [[5, 9]]

    def test_smt_context_holds_the_narrowed_scope(self) -> None:
        """The plumbing, kept alongside: the SMT context gets that scope.

        The behavioural assertion above covers the two together; this one says
        which of them is responsible, so a regression names the seam.
        """
        from vera.smt import SmtContext
        from vera.tester import _generate_inputs
        from vera.types import INT

        decl, env = self._decl_and_env()
        seen: list[object] = []
        original = SmtContext.__init__

        def patched(self, *args, **kwargs):
            original(self, *args, **kwargs)
            seen.append(self._alias_env)

        try:
            SmtContext.__init__ = patched  # type: ignore[method-assign]
            _generate_inputs(decl, [INT, INT], 1, env)
        finally:
            SmtContext.__init__ = original  # type: ignore[method-assign]

        assert seen, "the generator must build an SmtContext"
        assert "T" in seen[0].type_params, (  # type: ignore[attr-defined]
            "the tester handed SmtContext the un-narrowed module env, so a "
            "reference under a shadowed alias resolves against a scope the "
            "bind side never used"
        )


# =====================================================================
# The verifier's per-module registries
# =====================================================================

class TestVerifierModuleAliasEnvs:
    """``ContractVerifier`` builds its OWN per-module naming envs (#1208).

    ``CheckArtifacts`` carries none: ``vera verify`` runs with module-artifact
    collection off, so an artifact-sourced table would have been empty exactly
    where the cross-module obligations need it.  This pins that the verifier's
    own registration supplies them.
    """

    def test_module_env_is_the_modules_own_namespace(self) -> None:
        module = _resolved(("clib",), _CONFLICT_LIB)
        prog = parse_to_ast("""\
import clib(need3);

type Cnt = Int;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  need3(Some(9), Some(3))
}
""")
        v = ContractVerifier(resolved_modules=[module])
        v.register_program(prog)
        assert ("clib",) in v._module_alias_envs
        mod_env = v._module_alias_envs[("clib",)]
        assert mod_env.aliases["Cnt"].name == "Nat"  # type: ignore[union-attr]
        assert v._alias_env.aliases["Cnt"].name == "Int"  # type: ignore[union-attr]

    def test_check_artifacts_carry_no_per_module_env(self) -> None:
        """The dead artifact field is gone, not merely unread (#1208).

        Two consumers need a per-module env and each builds its own from a
        namespace it already holds — codegen from its flat alias maps, the
        verifier from its own registration.  A third, unread copy on
        ``CheckArtifacts`` was one more table to drift.
        """
        from vera.checker.core import CheckArtifacts

        assert "module_alias_envs" not in CheckArtifacts.__dataclass_fields__

    def test_generic_origin_records_the_defining_module(self) -> None:
        module = _resolved(("blib",), _GENERIC_LIB)
        prog = parse_to_ast(_GENERIC_MAIN)
        v = ContractVerifier(resolved_modules=[module])
        v.register_program(prog)
        assert v._generic_origins.get("twolen") == ("blib",)
        assert v._alias_env_for_generic("twolen") is v._module_alias_envs[("blib",)]
        # A main-file generic has no origin and keeps this program's env.
        assert v._alias_env_for_generic("no_such_generic") is v._alias_env


# =====================================================================
# Finding 1e — an UNPINNED callee renders in the module under verification
# =====================================================================

_UNPINNED_HELPER_LIB = """\
module blib;

type Cnt = Bool;

public forall<T> fn f(@Array<Bool>, @Array<Int>, @T -> @Nat)
  requires(array_length(@Array<Bool>.0) == 3 && array_length(@Array<Int>.0) == 2)
  ensures(@Nat.result >= 0)
  effects(pure)
{
  help(@Array<Bool>.0, @Array<Int>.0)
}
where {
  fn help(@Array<Cnt>, @Array<Int> -> @Nat)
    requires(array_length(@Array<Cnt>.0) == 2)
    ensures(@Nat.result >= 0)
    effects(pure)
  {
    array_length(@Array<Int>.0)
  }
}
"""

_UNPINNED_HELPER_MAIN = """\
import blib(f);

type Cnt = Int;

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  f([true, false, true], array_range(0, 2), 9)
}
"""


class TestUnpinnedCalleeRendersInTheDeclaringModule:
    """``_callee_alias_env``'s fallback is the module UNDER verification.

    Only PUBLIC functions of DIRECTLY imported modules are pinned into
    ``_fn_origins`` (``_register_modules``), so an imported generic's own
    ``where``-helper — resolved through ``_fn_info_for_decl`` while the
    generic's clone verifies inside ``_declaring_module_scope`` — always
    reaches the fallback.  Falling back to ``_alias_env`` rendered that
    helper's contract in the IMPORTER's namespace (PR #1224 review).

    Here ``help``'s two parameters are two stacks in ``blib`` (``Cnt = Bool``)
    and ONE merged stack in the importer (``Cnt = Int``), so
    ``@Array<Cnt>.0`` denotes the length-3 array whose precondition is FALSE
    under the correct env and the length-2 array whose precondition is TRUE
    under the importer's.  The wrong env therefore discharged a violated
    precondition — a false Tier 1, which the runtime oracle below catches.
    """

    def test_verify_reports_the_violation_the_runtime_traps_on(self) -> None:
        module = _resolved(("blib",), _UNPINNED_HELPER_LIB)
        result = _verify_mod(_UNPINNED_HELPER_MAIN, [module])
        assert "E501" in _codes(result), (
            "the helper's violated precondition was discharged as true — the "
            "unpinned callee rendered in the importer's namespace: "
            f"{[(d.error_code, d.description[:80]) for d in result.diagnostics]}"
        )

    def test_the_runtime_oracle_agrees_the_precondition_fails(self) -> None:
        """The other half: the emitted code really does trap there.

        Without this the E501 above could be a spurious rejection rather than
        a caught violation — the two failure directions of a wrong namespace
        look identical from inside the verifier.
        """
        module = _resolved(("blib",), _UNPINNED_HELPER_LIB)
        result = _compile_mod(_UNPINNED_HELPER_MAIN, [module])
        errors = [
            d for d in result.diagnostics  # type: ignore[attr-defined]
            if d.severity == "error"
        ]
        assert not errors, f"unexpected codegen errors: {errors}"
        with pytest.raises(WasmTrapError) as exc:
            execute(result, fn_name="main")  # type: ignore[arg-type]
        assert exc.value.kind == "contract_violation", exc.value.kind

    def test_the_control_without_a_conflicting_alias_is_unchanged(
        self,
    ) -> None:
        """The same program with the importer's shadowing alias removed.

        A fix that simply started reporting more would move this too.
        """
        module = _resolved(("blib",), _UNPINNED_HELPER_LIB)
        control = _UNPINNED_HELPER_MAIN.replace("type Cnt = Int;\n\n", "")
        assert "type Cnt" not in control
        result = _verify_mod(control, [module])
        assert "E501" in _codes(result)


_REFINED_RETURN_LIB = """\
module rlib;

type Cnt = Nat;

public fn mk(@Nat -> @{ @Cnt | @Cnt.0 >= 18 })
  requires(@Nat.0 >= 18)
  ensures(true)
  effects(pure)
{
  @Nat.0
}
"""

_REFINED_RETURN_MAIN = """\
import rlib(mk);

type Cnt = Int;

public fn main(@Unit -> @Nat)
  requires(true)
  ensures(true)
  effects(pure)
{
  mk(20)
}
"""


class TestRefinedReturnTranslatesInTheCalleeNamespace:
    """A callee's refined-RETURN predicate is the callee's own text.

    ``requires`` and ``ensures`` are translated inside
    ``SmtContext._callee_contract_scope``; the refined-return predicate the same
    call site ASSUMES was not, so an alias it names resolved in the IMPORTER's
    namespace (PR #1224 review).  Here ``Cnt`` is ``Nat`` in ``rlib`` and
    ``Int`` in the importer.

    Asserted on the ENVIRONMENT rather than on a diagnostic, because the
    behaviour this pin protects depends on the SHAPE of the refinement: the
    binder key renders its type ARGUMENTS (``naming.predicate_binder_key``), so
    it is env-dependent for a parameterised base and env-independent for a bare
    one — and ``rlib``'s base is bare, which is what makes the observation here
    a pure provenance one.  The prediction this pin recorded while the binder
    was still a bare ``UPPER_IDENT`` reading no env at all has since come true
    and is asserted behaviourally in
    ``tests/test_callee_contract_scope_1220_1225_1226.py``
    (``TestRefinedReturnBinderIsKeyedInTheCalleeScope``, #1226): over a
    PARAMETERISED base the same wrap decides whether a valid program is
    accepted, and moving the derivation out of the scope leaves the
    single-module case green and turns the cross-module one red.
    """

    def test_the_predicate_is_translated_under_the_defining_modules_env(
        self,
    ) -> None:
        from vera import naming as naming_mod
        from vera import smt as smt_module

        module = _resolved(("rlib",), _REFINED_RETURN_LIB)
        # `naming.predicate_binder_key` has exactly one caller in the SMT layer
        # — the refined-return site — so it opens a window that isolates THAT
        # translation from the `requires` / `ensures` ones (which are wrapped
        # already, and would otherwise supply the observation on their own).
        window = {"open": False}
        seen: list[str] = []
        orig_binder = naming_mod.predicate_binder_key
        orig_translate = smt_module.SmtContext.translate_expr

        def binder_spy(predicate: object, env: object) -> object:
            window["open"] = True
            return orig_binder(predicate, env)  # type: ignore[arg-type]

        def translate_spy(
            self: object, expr: object, env: object = None,
        ) -> object:
            if window["open"]:
                window["open"] = False
                # How the ACTIVE env renders the conflicting alias — inspected
                # through the RENDERING, not by object identity.
                resolved = naming_mod.resolve_type_expr(
                    ast.NamedType(name="Cnt", type_args=None),
                    self._alias_env,  # type: ignore[attr-defined]
                )
                seen.append(naming_mod.pretty_type(resolved))
            return orig_translate(self, expr, env)  # type: ignore[arg-type]

        naming_mod.predicate_binder_key = binder_spy  # type: ignore[assignment]
        smt_module.SmtContext.translate_expr = translate_spy  # type: ignore[method-assign]
        try:
            _verify_mod(_REFINED_RETURN_MAIN, [module])
        finally:
            naming_mod.predicate_binder_key = orig_binder  # type: ignore[assignment]
            smt_module.SmtContext.translate_expr = orig_translate  # type: ignore[method-assign]

        # Floor first: an empty observation list would satisfy the
        # set-equality assertion below vacuously — `set() == {"Nat"}` is
        # False, but only because the floor makes it so; without it a spy
        # patched onto a function the code no longer calls measures
        # nothing and says so with a green tick.
        assert seen, (
            "the refined-return translation never ran — this test is "
            "measuring nothing"
        )
        assert set(seen) == {"Nat"}, (
            "the callee's refined-return predicate was translated in the "
            f"IMPORTER's namespace (`Cnt` = Int), not its own: {seen}"
        )


# =====================================================================
# Finding 1f — the declaration-index space is PER NAMESPACE
# =====================================================================

_DECL_ORDER_LIB = """\
public data X {
  MkX(Int)
}
"""

_DECL_ORDER_MAIN = """\
import dolib;

type Z = X;
type X = Nat;

private fn pick(@Option<Nat>, @Option<Z> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(option_unwrap_or(@Option<Nat>.0, 0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick(Some(7), Some(MkX(99)))
}
"""


class TestDeclOrderIsPerNamespace:
    """Codegen's declaration-index space is keyed to its owning namespace.

    The index answers "was this name already declared when this alias body
    was registered?" — a question about ONE namespace (§8.4.1: aliases are
    module-local).  Codegen shared a single first-wins space across every
    absorbed namespace, and modules register at Pass 0.5 while the main file
    registers at Pass 1, so a name a module had already stamped kept that
    EARLIER index inside the main file — turning the main file's FORWARD
    reference into a backward one (PR #1224 review).

    ``type Z = X;`` precedes ``type X = Nat;`` here, so ``Z``'s body sees only
    the imported ADT ``X``, and the checker keeps ``@Option<Nat>`` and
    ``@Option<Z>`` as two stacks.  With the shared space codegen resolved
    ``Z`` through the LATER ``type X = Nat``, merged the two stacks, and
    ``@Option<Nat>.0`` became parameter 2 — a check-clean, verify-clean
    program that reads the wrong parameter and returns a garbage value from
    valid WASM (both parameters erase to ``i32``, so nothing traps).
    """

    def test_the_program_returns_its_first_parameter(self) -> None:
        module = _resolved(("dolib",), _DECL_ORDER_LIB)
        result = _compile_mod(_DECL_ORDER_MAIN, [module])
        errors = [
            d for d in result.diagnostics  # type: ignore[attr-defined]
            if d.severity == "error"
        ]
        assert not errors, f"unexpected codegen errors: {errors}"
        ran = execute(result, fn_name="main")  # type: ignore[arg-type]
        assert ran.value == 7, (
            "codegen merged two parameter stacks the checker kept apart — a "
            f"module's declaration index leaked into the main file's: got "
            f"{ran.value}"
        )

    def test_codegen_reads_the_parameter_the_checker_names(self) -> None:
        """The same claim in the instruction stream, so a coincidence of
        values cannot satisfy it."""
        module = _resolved(("dolib",), _DECL_ORDER_LIB)
        result = _compile_mod(_DECL_ORDER_MAIN, [module])
        body = _fn_body(result.wat, "pick")  # type: ignore[attr-defined]
        assert 0 in _local_gets(body), (
            "the emitted body does not read parameter 1:\n" + body
        )

    def test_the_control_without_the_shadowing_alias_is_unchanged(
        self,
    ) -> None:
        """The identical program minus the ``type X = Nat;`` line.

        It differs from the repro by exactly the declaration whose index was
        leaking, and it was green throughout — so this pins that the fix did
        not simply disable the ordering bound.
        """
        module = _resolved(("dolib",), _DECL_ORDER_LIB)
        control = _DECL_ORDER_MAIN.replace("type X = Nat;\n", "")
        result = _compile_mod(control, [module])
        ran = execute(result, fn_name="main")  # type: ignore[arg-type]
        assert ran.value == 7

    def test_a_module_keeps_its_own_space(self) -> None:
        """The stored spaces are per module, and the main file is not in them.

        Structural, so a future change that reinstates one shared dict fails
        here as well as end to end.
        """
        from vera.codegen.core import CodeGenerator

        module = _resolved(("dolib",), _DECL_ORDER_LIB)
        gen = CodeGenerator(
            source=_DECL_ORDER_MAIN, file="main.vera",
            resolved_modules=[module],
        )
        gen.compile_program(parse_to_ast(_DECL_ORDER_MAIN))
        assert ("dolib",) in gen._module_decl_order
        assert "X" in gen._module_decl_order[("dolib",)]
        assert "Z" not in gen._module_decl_order[("dolib",)]
        # The main file's own space orders its two aliases as written, and
        # the module's `X` is NOT what stamped the main file's.
        assert gen._decl_order["Z"] < gen._decl_order["X"], gen._decl_order


# =====================================================================
# #1221 — the prelude's type aliases are CODEGEN-INTERNAL and unspellable
# =====================================================================

_PRELUDE_ALIAS_SRC = """\
public fn f(@Array<ArrayMapFn<Int, Bool>>,
            @Array<fn(Int -> Bool) effects(pure)> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(array_length(@Array<ArrayMapFn<Int, Bool>>.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = array_map([1], fn(@Int -> @Int) effects(pure) { @Int.0 });
  nat_to_int(array_length(@Array<Int>.0))
}
"""

# The same program spelled with the RESERVED twin the prelude's own
# combinators resolve through.  Renaming the public names into the reserved
# namespace only closes #1221 if the reserved namespace is itself unwritable
# — otherwise the identical divergence survives four characters longer.
_RESERVED_ALIAS_SRC = _PRELUDE_ALIAS_SRC.replace(
    "ArrayMapFn", "VeraOptionMapFn",
)

_PRELUDE_ALIAS_NAMES = (
    "OptionMapFn", "OptionBindFn", "ResultMapFn",
    "ArrayMapFn", "ArrayFilterFn", "ArrayFoldFn",
)


def _codegen_alias_env(source: str) -> naming.AliasEnv:
    """The naming env codegen renders the MAIN file under."""
    from vera.codegen.core import CodeGenerator

    gen = CodeGenerator(source=source, file="<prelude-alias>")
    gen.compile_program(parse_to_ast(source))
    return gen._alias_env


class TestPreludeAliasesAreCodegenInternal:
    """The prelude's aliases live in the reserved namespace, unspellable.

    ``inject_prelude`` runs at CODEGEN and at the verifier's mono discovery,
    never at check — so any alias name it injects is a name codegen resolves
    and the checker does not.  With the six user-facing names injected, a
    program mixing ``ArrayMapFn<Int, Bool>`` with the function type it aliases
    made codegen merge two parameter stacks the checker keeps apart, and the
    emitted export read parameter 2 where the binding table says parameter 1
    (#1221; reachable only by a host calling the export, since the checker
    rejects every Vera-source argument for the opaque head).

    The close is Vera-prefix internalization, not teaching the checker: the
    prelude injects only reserved ``Vera``-prefixed declarations (spec §8.4.1,
    E154), the six public spellings become ordinary unknown names both sides
    treat opaquely, and a reference to a reserved name is refused where it is
    written.  The checker's ignorance is then correct by construction — no
    name it leaves opaque is a name codegen resolves.
    """

    def test_the_checker_keeps_the_two_stacks_apart(self) -> None:
        """Unchanged by the fix: an unknown head is opaque and stays apart.

        ``ArrayMapFn`` was never in the checker's alias table and still is
        not, so what the checker names — the rule every naming consumer keys
        off — is byte-identical before and after internalization.
        """
        from vera.checker.core import TypeChecker

        prog = parse_to_ast(_PRELUDE_ALIAS_SRC)
        checker = TypeChecker(source=_PRELUDE_ALIAS_SRC, file="<x01>")
        checker.check_program(prog)
        fn = next(
            tld.decl for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "f"
        )
        env = naming.alias_env_from_environment(checker.env)
        assert "ArrayMapFn" not in env.aliases, sorted(env.aliases)
        names = [naming.slot_name(te, env) for te in fn.params]
        assert names == [
            "Array<ArrayMapFn<Int, Bool>>",
            "Array<fn(Int -> Bool) effects(pure)>",
        ], names

    def test_codegen_names_the_parameters_the_checker_names(self) -> None:
        """The differential: one renderer, two envs, and they must agree.

        Both sides go through :func:`vera.naming.slot_name`, so a divergence
        here is a divergence of the ENVIRONMENTS — exactly the #1213 class.
        Compared as a list rather than a set: the partition is what decides
        which parameter a slot reference lands on.
        """
        from vera.checker.core import TypeChecker

        prog = parse_to_ast(_PRELUDE_ALIAS_SRC)
        checker = TypeChecker(source=_PRELUDE_ALIAS_SRC, file="<x01>")
        checker.check_program(prog)
        fn = next(
            tld.decl for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == "f"
        )
        check_env = naming.alias_env_from_environment(checker.env)
        gen_env = _codegen_alias_env(_PRELUDE_ALIAS_SRC)
        checker_names = [naming.slot_name(te, check_env) for te in fn.params]
        codegen_names = [naming.slot_name(te, gen_env) for te in fn.params]
        assert checker_names == codegen_names, (
            "codegen and the checker partition f's parameters differently: "
            f"checker {checker_names} vs codegen {codegen_names}"
        )

    def test_codegen_reads_the_parameter_the_checker_names(self) -> None:
        """The same claim in the emitted instruction stream.

        ``@Array<ArrayMapFn<Int, Bool>>.0`` is parameter 1 for the checker, so
        the exported body must load the first pair of locals.  Asserted on the
        WAT because no Vera caller can reach this export — only a host can.
        """
        wat = _compile_ok(_PRELUDE_ALIAS_SRC).wat
        body = _fn_body(wat, "f")
        reads = _local_gets(body)
        assert {0, 1} <= reads, body
        assert 2 not in reads, (
            "codegen still reads parameter 2 — the prelude alias is still "
            f"resolving on the codegen side only:\n{body}"
        )

    def test_the_user_facing_alias_names_reach_no_namespace(self) -> None:
        """Structural: the six public spellings are injected nowhere.

        A future re-injection of any one of them reopens the divergence for
        that name, so the whole family is named here rather than counted.
        """
        from vera.prelude import inject_prelude

        prog = parse_to_ast(_PRELUDE_ALIAS_SRC)
        inject_prelude(prog)
        declared = {
            tld.decl.name for tld in prog.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }
        leaked = sorted(declared & set(_PRELUDE_ALIAS_NAMES))
        assert not leaked, (
            f"the prelude still injects user-facing aliases: {leaked}"
        )
        gen_env = _codegen_alias_env(_PRELUDE_ALIAS_SRC)
        leaked_env = sorted(set(gen_env.aliases) & set(_PRELUDE_ALIAS_NAMES))
        assert not leaked_env, (
            f"codegen still resolves user-facing prelude aliases: {leaked_env}"
        )

    def test_the_prelude_keeps_its_reserved_twins(self) -> None:
        """The control on the assertion above: the internals are still there.

        The combinators resolve their closure parameters through the reserved
        twins, so deleting the injections outright (rather than internalizing
        them) would satisfy the emptiness assertion and break ``option_map``.
        """
        from vera.prelude import inject_prelude

        prog = parse_to_ast(_PRELUDE_ALIAS_SRC)
        inject_prelude(prog)
        declared = {
            tld.decl.name for tld in prog.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }
        assert {"VeraOptionMapFn", "VeraOptionBindFn"} <= declared, sorted(
            declared,
        )
        assert all(name.startswith("Vera") for name in declared), sorted(
            declared,
        )

    def test_a_reserved_prelude_name_is_unspellable(self) -> None:
        """E154 covers REFERENCES, not only declarations.

        The reserved twins stay in codegen's alias table (the combinators need
        them), so a user reference to one reproduces #1221 verbatim under a
        longer name unless the reservation refuses it where it is written.
        """
        prog = parse_to_ast(_RESERVED_ALIAS_SRC)
        errors = [
            d for d in typecheck(prog, _RESERVED_ALIAS_SRC)
            if d.severity == "error"
        ]
        assert [d.error_code for d in errors] == ["E154"], errors
        assert "VeraOptionMapFn" in errors[0].description, errors[0].description

    def test_an_ordinary_vera_containing_name_stays_ordinary(self) -> None:
        """The reservation is anchored: ``Veranda`` is not the prelude's."""
        src = _PRELUDE_ALIAS_SRC.replace("ArrayMapFn", "Veranda")
        errors = [
            d for d in typecheck(parse_to_ast(src), src)
            if d.severity == "error"
        ]
        assert not errors, errors

    def test_the_option_combinators_still_run(self) -> None:
        """End-to-end control: internalization did not break the prelude."""
        src = """\
public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Option<Int> = option_map(
    Some(20), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }
  );
  option_unwrap_or(@Option<Int>.0, 0)
}
"""
        assert _run(src) == 21

# =====================================================================
# #1227 — an imported ADT's declaration index is its OWNING module's
# =====================================================================

_XMOD_ADT_LIB = """\
public data Float {
  MkFloat(Int)
}
"""

# The same module with a declaration ahead of the ADT, so "the module's own
# position" is distinguishable from "0" and from any before-everything
# sentinel.
_XMOD_ADT_LIB_PADDED = """\
public data Pad {
  MkPad(Int)
}

public data Float {
  MkFloat(Int)
}
"""

_XMOD_ADT_MAIN = """\
import dolib;

type M = Float;

public fn pick(@Array<M>, @Array<Float> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(array_length(@Array<M>.0))
}

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  pick([], [])
}
"""


def _checker_env(source: str, modules: list[ResolvedModule]) -> naming.AliasEnv:
    from vera.checker.core import TypeChecker

    checker = TypeChecker(
        source=source, file="main.vera", resolved_modules=modules,
    )
    checker.check_program(parse_to_ast(source))
    return naming.alias_env_from_environment(checker.env)


def _codegen_env(
    source: str, modules: list[ResolvedModule],
) -> naming.AliasEnv:
    from vera.codegen.core import CodeGenerator

    gen = CodeGenerator(
        source=source, file="main.vera", resolved_modules=modules,
    )
    gen.compile_program(parse_to_ast(source))
    return gen._alias_env


def _params_of(source: str, fn_name: str) -> tuple[ast.TypeExpr, ...]:
    prog = parse_to_ast(source)
    fn = next(
        tld.decl for tld in prog.declarations
        if isinstance(tld.decl, ast.FnDecl) and tld.decl.name == fn_name
    )
    return fn.params


class TestImportedAdtIndexIsPerOwningNamespace:
    """An imported ADT is ordered where ITS module declared it.

    Codegen's ``_adt_layouts`` is one map across every absorbed namespace,
    while the alias maps and the declaration-index space are module-scoped
    (§8.4.1, PR #1224).  An imported ADT therefore reached the main file's
    naming environment with no index of its own and took the
    before-everything fallback every built-in takes — so a main-file alias
    naming it resolved THROUGH it, while the checker (which carries the
    ADT's own module-space index) left the alias body opaque.

    ``type M = Float;`` over an imported ``data Float`` is the shape that
    exhibits it: the checker partitions ``['Array<?>', 'Array<Float>']`` and
    codegen rendered ``['Array<Float>', 'Array<Float>']``, merging two
    parameter stacks the binding table keeps apart (#1227).  A user ADT
    named after a removed built-in alias is what makes the divergence
    visible rather than merely latent — the alias falls back to ``?`` on the
    side that cannot see the ADT.
    """

    def test_codegen_partitions_what_the_checker_partitions(self) -> None:
        """The differential, on the rendering both sides key off."""
        module = _resolved(("dolib",), _XMOD_ADT_LIB)
        params = _params_of(_XMOD_ADT_MAIN, "pick")
        check_env = _checker_env(_XMOD_ADT_MAIN, [module])
        gen_env = _codegen_env(_XMOD_ADT_MAIN, [module])
        checker_names = [naming.slot_name(te, check_env) for te in params]
        codegen_names = [naming.slot_name(te, gen_env) for te in params]
        assert checker_names == codegen_names, (
            "codegen and the checker partition pick's parameters "
            f"differently: checker {checker_names} vs codegen {codegen_names}"
        )

    def test_the_export_reads_the_parameter_the_checker_names(self) -> None:
        """The consequence, in the emitted instruction stream.

        ``@Array<M>.0`` is parameter 1 for the checker — one of two stacks.
        Merged into one stack, index 0 is the LAST occurrence, so the body
        loads the second array's locals instead.
        """
        module = _resolved(("dolib",), _XMOD_ADT_LIB)
        result = _compile_mod(_XMOD_ADT_MAIN, [module])
        errors = [
            d for d in result.diagnostics  # type: ignore[attr-defined]
            if d.severity == "error"
        ]
        assert not errors, f"unexpected codegen errors: {errors}"
        body = _fn_body(result.wat, "pick")  # type: ignore[attr-defined]
        reads = _local_gets(body)
        assert {0, 1} & reads, (
            "the emitted body does not read parameter 1:\n" + body
        )
        assert not ({2, 3} & reads), (
            "the emitted body reads parameter 2 — the imported ADT is still "
            f"ordered ahead of the main file's aliases:\n{body}"
        )

    def test_the_index_is_the_modules_own_position(self) -> None:
        """Structural, and against the checker's number rather than a rule.

        The module here declares an ADT ahead of ``Float``, so its own
        position is 1 — distinguishable from 0 and from any
        before-everything or after-everything sentinel that would happen to
        render this one program correctly.
        """
        module = _resolved(("dolib",), _XMOD_ADT_LIB_PADDED)
        check_env = _checker_env(_XMOD_ADT_MAIN, [module])
        gen_env = _codegen_env(_XMOD_ADT_MAIN, [module])
        assert check_env.data_types["Float"] == 1, check_env.data_types
        assert gen_env.data_types["Float"] == check_env.data_types["Float"], (
            f"codegen orders the imported ADT at "
            f"{gen_env.data_types['Float']}, the checker at "
            f"{check_env.data_types['Float']}"
        )

    def test_a_locally_declared_adt_keeps_the_main_files_index(self) -> None:
        """The control: a main-file ADT is still ordered by the main file.

        Green before and after — it differs from the repro by exactly the
        namespace the ADT is declared in, so it pins that the fix reorders
        imported declarations only.
        """
        source = _XMOD_ADT_MAIN.replace(
            "import dolib;\n\ntype M = Float;",
            "private data Float {\n  MkFloat(Int)\n}\n\ntype M = Float;",
        )
        check_env = _checker_env(source, [])
        gen_env = _codegen_env(source, [])
        params = _params_of(source, "pick")
        checker_names = [naming.slot_name(te, check_env) for te in params]
        codegen_names = [naming.slot_name(te, gen_env) for te in params]
        assert checker_names == ["Array<Float>", "Array<Float>"], checker_names
        assert codegen_names == checker_names, codegen_names

    def test_the_module_names_its_own_adt_in_its_own_scope(self) -> None:
        """The other direction: inside the module's scope the ADT is visible.

        The owning module's own alias bodies must keep resolving through it
        — an index that made it invisible everywhere would satisfy the
        differential above by breaking the module.
        """
        from vera.codegen.core import CodeGenerator

        lib = _XMOD_ADT_LIB + """
type N = Float;

public fn count(@Array<N> -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  nat_to_int(array_length(@Array<N>.0))
}
"""
        module = _resolved(("dolib",), lib)
        gen = CodeGenerator(
            source=_XMOD_ADT_MAIN, file="main.vera", resolved_modules=[module],
        )
        gen.compile_program(parse_to_ast(_XMOD_ADT_MAIN))
        with gen._module_alias_scope(("dolib",)):
            assert gen._alias_env.data_types["Float"] == 0, (
                gen._alias_env.data_types
            )
            te = _params_of(lib, "count")[0]
            assert naming.slot_name(te, gen._alias_env) == "Array<Float>"
