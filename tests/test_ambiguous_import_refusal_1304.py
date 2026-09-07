"""#1304: two imports supplying one bare name are refused, in every namespace.

Spec §8.5 ordered a local declaration against an import (§8.5.2) and gave the
module-qualified form for reaching what a clash hides (§8.5.3), but it defined
no order between two IMPORTS that both supply one name.  Neither did the
implementation, and the gap was observable: a module importing two
dependencies that each export ``gen`` — one returning ``@Int``, one ``@Bool``
— bound its bare call to whichever supplier a set happened to yield first, so
one unchanged file type-checked on one run and reported ``body has type Bool``
on the next.  Codegen's E608 rail caught the ENTRY-visible pair before it
mattered there; the flap lived in the shapes the rail only reached later, from
inside a module the entry program merely imports.

The rule is now REFUSAL, and the refusal is what removes the flap: with no
pick to make, there is no iteration order to expose.  That is why the
determinism cells below are the load-bearing ones — a test that only asserted
"the program is rejected" would also pass against a fix that picked
deterministically, which DESIGN.md's explicitness (§0.2.2) and
constrained-expressiveness (§0.2.6) priorities rule out.

DEFINITION-GATED, matching the rail it generalises.  The clash is refused
because the import pair exists, not because a body names it: an entry program
importing two suppliers and never calling either is E608 today, so the
check-phase refusal fires there too (:class:`TestTheRefusalIsDefinitionGated`).
Replacing a bare call with the qualified form therefore does NOT clear it —
that shape is E608 at base and E155 here, asserted rather than assumed.  What
does clear it is either supplier being kept out of the bare namespace:
declaring the name locally (§8.5.2), or naming the other import's declarations
selectively.  Both are exercised end to end, through to the runtime value.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

import vera
from tests.module_fixture_helpers import (
    build_multi_module,
    build_multi_module_past_check,
    module_value,
)

INT_ANSWER = 111
LOCAL_ANSWER = 222
OTHER_ANSWER = 5

# The repository this test's `vera` was imported from.  Every subprocess below
# is given it as PYTHONPATH, so a checkout tested through a `PYTHONPATH`
# override measures ITSELF and not whichever copy the interpreter's default
# path happens to find — the determinism cells compare runs against each
# other, and two runs of two different trees would agree for the wrong reason.
_VERA_ROOT = Path(vera.__file__).resolve().parent.parent

_LIB_INT = f"""\
module libint;

public forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER})
  effects(pure)
{{ {INT_ANSWER} }}
"""

# The SAME name at a different return type.  A namespace binding `gen` to the
# wrong supplier is then a type error rather than a silently swapped body,
# which is what made the pick observable in the first place: with both
# libraries returning `@Int` the flap would have been invisible.
_LIB_BOOL = f"""\
module libbool;

public forall<T> fn gen(@T -> @Bool)
  requires(true)
  ensures(@Bool.result)
  effects(pure)
{{ true }}

public fn other(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {OTHER_ANSWER})
  effects(pure)
{{ {OTHER_ANSWER} }}
"""

_MID_AB = """\
module midc;

import libint;
import libbool;

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ gen(@Bool.0) }
"""

# The identical module with the two imports swapped.  The verdict must be a
# property of the import SET: an order-sensitive rule accepts one spelling and
# rejects the other, and a positional one (codegen's reroute map is last-wins)
# would have made these two disagree.
_MID_BA = """\
module midc;

import libbool;
import libint;

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ gen(@Bool.0) }
"""

_MAIN_VIA_MID = f"""\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER})
  effects(pure)
{{ doorc(true) }}
"""

_FLAP_FILES: dict[str, dict[str, str]] = {
    "ab": {"libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
           "midc.vera": _MID_AB, "main.vera": _MAIN_VIA_MID},
    "ba": {"libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
           "midc.vera": _MID_BA, "main.vera": _MAIN_VIA_MID},
}


def _write(tmp_path: Path, files: dict[str, str]) -> Path:
    """Write a fixture set and return the entry program's path."""
    tmp_path.mkdir(parents=True, exist_ok=True)
    for name, src in files.items():
        (tmp_path / name).write_text(src, encoding="utf-8")
    return tmp_path / "main.vera"


def _run_check_json(
    argv: list[str], *, seed: str,
) -> subprocess.CompletedProcess[str]:
    """One ``vera check --json`` subprocess; the raw result, unparsed."""
    return subprocess.run(
        argv,
        capture_output=True,
        text=True,
        encoding="utf-8",
        env={**os.environ, "PYTHONHASHSEED": seed,
             "PYTHONPATH": str(_VERA_ROOT)},
        # A seed that drives the checker into a non-terminating
        # resolution loop is the exact failure this file exists to
        # find, and an unbounded wait reports it as a hung suite
        # rather than as a finding (#1330 review).
        timeout=300,
        check=False,
    )


def _parse_check_json(
    result: subprocess.CompletedProcess[str], *, seed: str,
) -> dict:
    """The subprocess's stdout as JSON, or a failure that says why.

    ``check=False`` plus a bare ``json.loads`` would turn a crashed CLI into a
    ``JSONDecodeError`` about column 1 of an empty document, with the exit
    code and the whole traceback on stderr discarded — and a crash that
    happens under SOME hash seeds is precisely what this file exists to
    catch, so the one failure mode the suite must describe well is the one it
    described worst.  The seed, the exit code and both streams travel with
    the failure instead.
    """
    try:
        payload: dict = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise AssertionError(
            f"vera check --json produced no parseable JSON under "
            f"PYTHONHASHSEED={seed} (exit code {result.returncode}): {exc}\n"
            f"--- stdout ---\n{result.stdout or '<empty>'}\n"
            f"--- stderr ---\n{result.stderr or '<empty>'}"
        ) from exc
    return payload


def _check_json(main_path: Path, *, seed: str) -> dict:
    """``vera check --json`` in a fresh interpreter under *seed*.

    A SUBPROCESS, and a fresh one per seed, because ``PYTHONHASHSEED`` is
    fixed at interpreter start: the randomised string hashing this issue's
    flap rode is not reachable from inside one process, so an in-process loop
    would measure one seed many times and call it determinism.
    """
    result = _run_check_json(
        [sys.executable, "-m", "vera.cli", "check", "--json", str(main_path)],
        seed=seed,
    )
    return _parse_check_json(result, seed=seed)


def _codes(payload: dict) -> list[str]:
    return sorted(
        d["error_code"]
        for d in [*payload.get("diagnostics", ()), *payload.get("warnings", ())]
    )


def _error_codes(payload: dict) -> list[str]:
    """Just the ERROR codes, sorted — warnings are a separate assertion."""
    return sorted(d["error_code"] for d in payload.get("diagnostics", ()))


def _fingerprint(payload: dict) -> str:
    """Everything about a verdict a reader would notice, as one string.

    Not just the code list: a fix that refused deterministically but pointed
    the diagnostic at whichever import a set yielded first would still flip
    the LOCATION and the module names in the message run to run, and this
    issue is about a user seeing two different answers to one question.
    """
    return json.dumps(
        {
            "ok": payload["ok"],
            "diagnostics": [
                {k: d.get(k) for k in
                 ("error_code", "severity", "description", "rationale",
                  "fix", "spec_ref", "location")}
                for d in payload.get("diagnostics", ())
            ],
            "warnings": [
                {k: d.get(k) for k in
                 ("error_code", "severity", "description", "location")}
                for d in payload.get("warnings", ())
            ],
        },
        sort_keys=True,
    )


# Enough seeds to have caught the base tree's flap with room to spare: at
# `release/v0.1.12` the same fixture answered OK on seeds 0, 2 and 3 and E121
# on 1, 4, 5, 6 and 7, so any two of these disagree there.
_SEEDS = ("0", "1", "4", "7")


def test_the_subprocesses_measure_this_checkout() -> None:
    """The canary for every cell below: same tree, both sides of the fork.

    Without it a PYTHONPATH mistake would have each subprocess measure an
    installed copy of Vera while the in-process cells measure the working
    tree, and the two halves of this file would silently be about different
    compilers.
    """
    result = subprocess.run(
        [sys.executable, "-c", "import vera; print(vera.__file__)"],
        capture_output=True, text=True, encoding="utf-8",
        env={**os.environ, "PYTHONPATH": str(_VERA_ROOT)},
        check=True,
    )
    assert Path(result.stdout.strip()).resolve() == Path(vera.__file__).resolve()


_ADT_A = """\
module liba;

public data Shape {
  Sq(Int),
  Dot
}
"""

# Same TYPE name, same CONSTRUCTOR name, different field type — so a namespace
# binding `Shape`/`Sq` to the wrong supplier is a type error rather than a
# silently swapped layout, exactly as the function fixtures differ by return
# type.
_ADT_B = """\
module libb;

public data Shape {
  Sq(Bool),
  Blob
}
"""

_ADT_MID = """\
module midc;

import liba;
import libb;

public fn doorc(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Sq(3) {
    Sq(@Int) -> @Int.0,
    Dot -> 0
  }
}
"""

_ADT_MID_SWAPPED = _ADT_MID.replace(
    "import liba;\nimport libb;", "import libb;\nimport liba;",
)

_ADT_MAIN = """\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ doorc(()) }
"""

_ADT_FILES: dict[str, dict[str, str]] = {
    "ab": {"liba.vera": _ADT_A, "libb.vera": _ADT_B,
           "midc.vera": _ADT_MID, "main.vera": _ADT_MAIN},
    "ba": {"liba.vera": _ADT_A, "libb.vera": _ADT_B,
           "midc.vera": _ADT_MID_SWAPPED, "main.vera": _ADT_MAIN},
}


def test_an_unparseable_check_reports_its_stderr_and_exit_code() -> None:
    """The helper's own failure path, exercised (#1304 review).

    Pointed at a command that exits nonzero with empty stdout and a known
    marker on stderr — the shape a seed-specific CLI crash takes.  Before
    this, that arrived as a bare ``JSONDecodeError`` about an empty document
    with the traceback thrown away, which is the least useful possible
    report of the one failure the determinism cells exist to find.
    """
    marker = "vera-cli-crashed-under-this-seed"
    result = _run_check_json(
        [sys.executable, "-c",
         f"import sys; sys.stderr.write({marker!r}); sys.exit(3)"],
        seed="0",
    )
    with pytest.raises(AssertionError) as caught:
        _parse_check_json(result, seed="0")
    message = str(caught.value)
    assert marker in message, message
    assert "exit code 3" in message, message
    assert "PYTHONHASHSEED=0" in message, message


class TestTheDataSideFlapShapes:
    """The same defect in the TYPE and CONSTRUCTOR namespaces (#1304).

    Spec §8.5.4 says constructor names follow the same shadowing rules as
    function names, which made the function-only refusal leave that sentence
    false: two imports supplying one `data` name flapped exactly as two
    supplying one `fn` name did, and the accepting seeds were the worse half
    — `check` AND `verify` both passed, and the program died at `run` with an
    `E609` located at line 0 of the entry file, naming two modules the entry
    never imported.

    Measured at the branch point and again with the function-only fix in
    place, byte-identical: accepted on hash seeds 2, 8, 9, 10 and 11 and
    `[E213]` on 0, 1, 3, 4, 5, 6 and 7.
    """

    @pytest.mark.parametrize("order", ["ab", "ba"])
    def test_two_imports_supplying_one_data_name_are_refused(
        self, tmp_path: Path, order: str,
    ) -> None:
        """Both codes, because both namespaces clash here."""
        payload = _check_json(_write(tmp_path, _ADT_FILES[order]), seed="0")
        assert payload["ok"] is False
        # A SUBSET assertion, deliberately: an unbound `Shape`/`Sq` leaves the
        # body's slot references and match arms unresolved (E130/E313), and
        # suppressing that cascade would mean the fixture no longer USES the
        # ambiguous names — which is what made the flap observable. The whole
        # stream, cascade included, is pinned byte-for-byte by the
        # determinism cell below.
        assert {"E156", "E157"} <= set(_error_codes(payload)), payload
        by_code = {d["error_code"]: d for d in payload["diagnostics"]}
        assert "Shape" in by_code["E156"]["description"]
        assert "Sq" in by_code["E157"]["description"]
        for diag in by_code.values():
            assert diag["location"]["file"].endswith("midc.vera")

    @pytest.mark.parametrize("order", ["ab", "ba"])
    def test_the_data_verdict_does_not_vary_with_the_hash_seed(
        self, tmp_path: Path, order: str,
    ) -> None:
        """The data-side twin of the function determinism cell."""
        main_path = _write(tmp_path, _ADT_FILES[order])
        prints = {seed: _fingerprint(_check_json(main_path, seed=seed))
                  for seed in _SEEDS}
        assert len(set(prints.values())) == 1, (
            "the data-side verdict varies with PYTHONHASHSEED: "
            + json.dumps({s: json.loads(p) for s, p in prints.items()},
                         indent=2)
        )

    def test_a_shared_constructor_alone_is_E157_without_E156(
        self, tmp_path: Path,
    ) -> None:
        """Two DIFFERENTLY-named ADTs sharing a constructor name.

        The shape that makes three codes the right split rather than one: the
        type names do not clash at all, only `Sq` does, and codegen separates
        the two cases as E609 and E610 for the same reason.  It flapped too —
        `OK` on the same seeds the type-name shape accepted on.
        """
        files = {
            "liba.vera": _ADT_A.replace("data Shape", "data Alpha"),
            "libb.vera": _ADT_B.replace("data Shape", "data Beta"),
            "midc.vera": _ADT_MID,
            "main.vera": _ADT_MAIN,
        }
        payload = _check_json(_write(tmp_path, files), seed="0")
        codes = set(_error_codes(payload))
        assert "E157" in codes and "E156" not in codes, payload
        ctor = next(d for d in payload["diagnostics"]
                    if d["error_code"] == "E157")
        assert "Sq" in ctor["description"]

    def test_every_remedy_the_diagnostic_offers_actually_works(
        self, tmp_path: Path,
    ) -> None:
        """The fix text names three routes, and each is measured here.

        Renaming was the only one that worked until #1317: E609 refused two
        modules' same-named data declarations by DECLARATION, with none of
        the visibility, filter or shadowing relaxation E608 received in
        #1281.  Per-owner ADT identity added the other two, under one
        condition the text states — no namespace may reach both
        declarations — so the cell asserts the text offers all three and
        the sibling cells above run each of them.
        """
        files = dict(_ADT_FILES["ab"])
        # BOTH names, because both namespaces clashed: renaming the type
        # alone leaves `Sq` supplied twice and the program still E157.
        files["libb.vera"] = (
            _ADT_B.replace("data Shape", "data Renamed").replace("Sq(", "Sqr(")
        )
        assert _answer(tmp_path, files) == 3
        payload = _check_json(_write(tmp_path / "x", _ADT_FILES["ab"]),
                              seed="0")
        fix = next(d["fix"] for d in payload["diagnostics"]
                   if d["error_code"] == "E156")
        assert "Import at most one supplier" in fix
        assert "in this file resolves it" in fix
        assert "rename" in fix
        assert "no namespace can reach both declarations" in fix

    def test_a_shared_constructor_is_backstopped_by_E610(
        self, tmp_path: Path,
    ) -> None:
        """The E610 axis, pinned at both layers.

        Two DIFFERENTLY-named types sharing one constructor: the checker
        refuses `Sq` (E157) and codegen's constructor rail refuses the pair
        (E610), so the sibling of the E609 cell above is measured rather
        than assumed.  It is the shape that shows the collision is not about
        the type name — `Alpha` and `Beta` never clash — which is why the
        two codes are separate on both sides.

        `midc` imports both modules wholesale, so it can name both `Alpha`
        and `Beta` and therefore both suppliers of `Sq`; that is the
        AMBIGUOUS shape, which #1317's per-owner identity declines to
        qualify apart (§8.5.2.2 refuses it rather than picking) and which
        the codegen rail therefore still backstops.
        """
        files = {
            "liba.vera": _ADT_A.replace("data Shape", "data Alpha"),
            "libb.vera": _ADT_B.replace("data Shape", "data Beta"),
            "midc.vera": _ADT_MID,
            "main.vera": _ADT_MAIN,
        }
        check_errors, _result, cg_errors = build_multi_module_past_check(
            tmp_path, files,
        )
        assert [c for c, _ in check_errors if c == "E157"], check_errors
        assert not [c for c, _ in check_errors if c == "E156"], check_errors
        assert [c for c, _ in cg_errors if c == "E610"], cg_errors

    @pytest.mark.parametrize("remedy", ["selective", "local", "private"])
    def test_the_function_remedies_now_clear_a_data_clash(
        self, tmp_path: Path, remedy: str,
    ) -> None:
        """Measured, not assumed — this is what the fix text may promise.

        Each leaves the clash out of the checker's view (one supplier, or a
        local declaration that owns the name), so E156/E157 correctly fall
        silent.  Codegen used to refuse the program anyway, which is why
        `_ambiguous_data_fix` once prescribed renaming alone; #1317's
        per-owner ADT identity compiles each declaration under its own
        `mod$<path>$<Name>` symbol, so all three now carry through to the
        runtime value.  `doorc` matches `Sq(3)` against `liba`'s `Shape`
        (the `local` remedy against `midc`'s own, which is the same layout),
        so the answer is 3 in every arm.
        """
        files = dict(_ADT_FILES["ab"])
        if remedy == "private":
            files["libb.vera"] = _ADT_B.replace("public data", "private data")
        elif remedy == "selective":
            files["libb.vera"] = _ADT_B + """
public fn helper(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ 5 }
"""
            files["midc.vera"] = _ADT_MID.replace(
                "import libb;", "import libb(helper);",
            )
        else:
            files["midc.vera"] = _ADT_MID.replace(
                "import libb;",
                "import libb;\n\nprivate data Shape {\n  Sq(Int),\n  Dot\n}",
            )
        assert _error_codes(_check_json(_write(tmp_path / "c", files),
                                        seed="0")) == []
        _, result, cg_errors = build_multi_module(tmp_path, files)
        assert cg_errors == [], cg_errors
        assert module_value(result) == ("ok", 3)


class TestTheRefusedDataNamesBindToNothing:
    """The data-side twin of `test_the_refused_name_binds_to_nothing`.

    Structural, because the type half has no end-to-end tell: an unresolved
    type expression becomes an opaque ADT rather than a diagnostic, so a
    program cannot distinguish "no `Shape` here" from "some `Shape` here" by
    its verdict.  The environment can, and it is the thing the injection loop
    writes — so it is asserted directly, on both halves at once and against
    controls, since a cell that only checked the ambiguous names would pass
    just as well against an environment that registered nothing at all.
    """

    def _env(self, files: dict[str, str]) -> object:
        from tests.module_fixture_helpers import fake_resolved_module
        from vera.checker.core import TypeChecker
        from vera.parser import parse_to_ast

        mods = [
            fake_resolved_module((name[: -len(".vera")],), src)
            for name, src in files.items() if name != "main.vera"
        ]
        checker = TypeChecker(source=files["main.vera"], file="main.vera",
                              resolved_modules=mods)
        checker.check_program(parse_to_ast(files["main.vera"]))
        return checker.env

    def test_neither_the_type_nor_its_constructor_is_registered(self) -> None:
        entry = """\
import liba;
import libb;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ 7 }
"""
        env = self._env({"liba.vera": _ADT_A, "libb.vera": _ADT_B,
                         "main.vera": entry})
        assert "Shape" not in env.data_types  # type: ignore[attr-defined]
        assert "Sq" not in env.constructors  # type: ignore[attr-defined]
        # The controls: the two UNAMBIGUOUS constructors of those same two
        # types are registered, so the assertions above are about ambiguity
        # and not about the harvest having failed.
        assert "Dot" in env.constructors  # type: ignore[attr-defined]
        assert "Blob" in env.constructors  # type: ignore[attr-defined]


class TestTheDiagnosticNamesTheLastSupplyingImport:
    """Position, not just presence (#1304 review).

    Every cell above would pass against a rule that reported the clash at the
    FIRST supplying import, and the two spellings of one import list differ
    only in which module that is — so the sequence-independence the refusal
    is for would be unpinned in exactly the dimension it is about.  The last
    import is the one whose presence completes the clash, so that is where
    the diagnostic goes.
    """

    @pytest.mark.parametrize(
        ("files", "code", "last"),
        [
            (_FLAP_FILES["ab"], "E155", "libbool"),
            (_FLAP_FILES["ba"], "E155", "libint"),
            (_ADT_FILES["ab"], "E156", "libb"),
            (_ADT_FILES["ba"], "E156", "liba"),
        ],
    )
    def test_reported_at_the_second_import_not_the_first(
        self, tmp_path: Path, files: dict[str, str], code: str, last: str,
    ) -> None:
        payload = _check_json(_write(tmp_path, files), seed="0")
        diag = next(d for d in payload["diagnostics"]
                    if d["error_code"] == code)
        assert diag["source_line"].strip() == f"import {last};", diag
        # The mid module writes its imports on lines 3 and 4; the clash is
        # completed by the second, so the line number is pinned too rather
        # than left to the source-line text alone.
        assert diag["location"]["line"] == 4, diag


class TestABuiltinOwnedNameIsNeverAmbiguous:
    """The incumbent wins, so two imports of it are not a clash (#1304 review).

    Every injection in `_register_modules` is a `setdefault` onto a `TypeEnv`
    the built-in registry populated first, so a dependency exporting its own
    `option_map` never wins the bare name — measured as `E201` against the
    PRELUDE's two-argument signature, from a program importing exactly one
    such module.  Two of them are therefore not ambiguous either, and the
    first version of this refusal reported them anyway: a new rejection where
    the branch point was green.

    Kept deliberately narrow.  A prelude-owned name supplied by ONE import
    beside the prelude is the existing rails' business, and this refusal is
    silent there for the same reason it is silent here.
    """

    _PRELUDE_NAMED_LIB = """\
module lib{n};

public fn option_map(@Int -> @Int)
  requires(true)
  ensures(@Int.result == 9)
  effects(pure)
{ 9 }
"""

    # Only the TYPE name is shared. The constructors are per-module on
    # purpose: two modules supplying one CONSTRUCTOR name is a real E157
    # whatever the type is called, and reusing one here would have made this
    # cell assert the built-in carve-out while measuring that instead.
    _PRELUDE_NAMED_ADT = """\
module lib{n};

public data Option {
  Wrapped{n}(Int)
}
"""

    def _two_libs(self, template: str) -> dict[str, str]:
        return {
            "liba.vera": template.replace("{n}", "a"),
            "libb.vera": template.replace("{n}", "b"),
            "main.vera": """\
import liba;
import libb;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ 7 }
""",
        }

    def test_a_function_the_prelude_owns_is_not_reported(
        self, tmp_path: Path,
    ) -> None:
        payload = _check_json(
            _write(tmp_path, self._two_libs(self._PRELUDE_NAMED_LIB)),
            seed="0",
        )
        assert _error_codes(payload) == []

    def test_a_data_type_the_builtins_own_is_not_reported(
        self, tmp_path: Path,
    ) -> None:
        """`Option` is the prelude's, so two modules exporting one do not
        make it ambiguous HERE — whatever the other rails make of them."""
        payload = _check_json(
            _write(tmp_path, self._two_libs(self._PRELUDE_NAMED_ADT)),
            seed="0",
        )
        assert _error_codes(payload) == []

    def test_the_prelude_argument_changes_the_ambiguity_half(self) -> None:
        """Pins the corrected `namespace_fn_names` docstring (#1304 review).

        The old text claimed the ambiguity half was identical whether or not
        the prelude names were passed, "since a prelude name is imported from
        nowhere".  It is not: the combinators are overridable rather than
        reserved, so a dependency may export one, and the two answers differ.
        Codegen's two calls pass different preludes and its E608 rail reads
        the first; the checker passes its built-in snapshot and reads the
        populated one.  That ordering is load-bearing, so the difference is
        asserted rather than described.
        """
        from vera.monomorphize import namespace_fn_names
        from vera.parser import parse_to_ast

        files = self._two_libs(self._PRELUDE_NAMED_LIB)
        entry = parse_to_ast(files["main.vera"])
        mods = [((name[: -len(".vera")],), parse_to_ast(src))
                for name, src in files.items() if name != "main.vera"]
        assert namespace_fn_names(entry, mods).ambiguous == {"option_map"}
        assert namespace_fn_names(
            entry, mods, prelude={"option_map"},
        ).ambiguous == frozenset()


class TestTheTwoViewsOfOneWalk:
    """``ambiguous`` and ``ambiguous_sources`` cannot drift apart.

    The checker refuses a namespace's OWN clashes and codegen's rail reads
    the union over every namespace.  Both claim to be views of one walk, and
    that claim is what lets the two layers be described as one rule — so it
    is asserted on the structure rather than inferred from the two of them
    happening to agree on the fixtures above.
    """

    def _tables(self, files: dict[str, str]) -> object:
        from vera.monomorphize import namespace_fn_names
        from vera.parser import parse_to_ast

        entry = parse_to_ast(files["main.vera"])
        modules = [
            ((name[: -len(".vera")],), parse_to_ast(src))
            for name, src in files.items() if name != "main.vera"
        ]
        return namespace_fn_names(entry, modules)

    def test_the_union_is_exactly_the_per_namespace_keys(self) -> None:
        tables = self._tables(_FLAP_FILES["ab"])
        union = {
            name
            for clashes in tables.ambiguous_sources.values()  # type: ignore[attr-defined]
            for name in clashes
        }
        assert tables.ambiguous == frozenset(union)  # type: ignore[attr-defined]
        assert union == {"gen"}, union

    def test_the_clash_is_recorded_against_the_namespace_holding_it(
        self,
    ) -> None:
        """`midc`'s, not the entry's — the distinction the refusal needed.

        The entry program imports only `midc`, so its own namespace is
        clean; a per-namespace table that reported the clash against the
        entry would point the diagnostic at a file that does not contain the
        two imports.
        """
        tables = self._tables(_FLAP_FILES["ab"])
        assert tables.ambiguous_in(None) == {}  # type: ignore[attr-defined]
        assert tables.ambiguous_in(("midc",)) == {  # type: ignore[attr-defined]
            "gen": (("libint",), ("libbool",)),
        }

    def test_the_suppliers_are_listed_in_import_order(self) -> None:
        """Swapping the two imports swaps the recorded order, and nothing else.

        The property the diagnostic's wording and its location both rest on.
        """
        assert self._tables(_FLAP_FILES["ba"]).ambiguous_in(  # type: ignore[attr-defined]
            ("midc",),
        ) == {"gen": (("libbool",), ("libint",))}


class TestTheDiagnosticIsRegisteredAtItsOwnPhase:
    """E155 is a CHECK-phase code, and the registry says so.

    #1304's complaint was that a scope question was enforced by a codegen
    rail — the wrong layer.  Reusing E608 for the checker's refusal would
    have carried that mislabelling into the fix: ``vera errors`` derives a
    diagnostic's phase from its numeric range, so an E6xx code reported by
    ``vera check`` tells every consumer the wrong thing about when it fires.
    """

    def test_the_code_is_registered_with_a_typecheck_phase(self) -> None:
        from vera._since import SINCE
        from vera.errors import ERROR_CODES
        from vera.introspect import errors_payload

        assert "E155" in ERROR_CODES
        assert SINCE["E155"] == "0.1.12"
        items = {i["code"]: i for i in errors_payload()["items"]}  # type: ignore[attr-defined,index,union-attr]
        assert items["E155"]["phase"] == "typecheck"

    def test_the_refusal_reports_a_typecheck_phase_code(
        self, tmp_path: Path,
    ) -> None:
        """Asked of the emitted diagnostic, not of the registry alone.

        The registry can be right while the emission site passes a different
        code; this reads the code off ``vera check``'s own output and holds
        it to the same range.
        """
        from vera.introspect import errors_payload

        phases = {i["code"]: i["phase"]  # type: ignore[index]
                  for i in errors_payload()["items"]}  # type: ignore[union-attr]
        main_path = _write(tmp_path, _FLAP_FILES["ab"])
        emitted = [d["error_code"]
                   for d in _check_json(main_path, seed="0")["diagnostics"]]
        assert emitted == ["E155"]
        assert phases[emitted[0]] == "typecheck"


class TestTheFlapShapes:
    """The measured nondeterminism, now a fixed refusal."""

    @pytest.mark.parametrize("order", ["ab", "ba"])
    def test_a_module_importing_two_suppliers_is_refused(
        self, tmp_path: Path, order: str,
    ) -> None:
        """Either spelling of the two imports, one verdict: E155.

        The refusal is reported against the MODULE that holds the clash, and
        surfaced into the program being checked — the entry program declares
        nothing ambiguous itself, so a refusal scoped to the entry namespace
        alone would miss this shape entirely, which is precisely the gap
        codegen's rail was standing in for.
        """
        main_path = _write(tmp_path, _FLAP_FILES[order])
        payload = _check_json(main_path, seed="0")
        assert payload["ok"] is False
        e155 = [d for d in payload["diagnostics"]
                if d["error_code"] == "E155"]
        assert len(e155) == 1, payload["diagnostics"]
        assert "gen" in e155[0]["description"]
        assert "libint" in e155[0]["description"]
        assert "libbool" in e155[0]["description"]
        assert e155[0]["location"]["file"].endswith("midc.vera")

    @pytest.mark.parametrize("order", ["ab", "ba"])
    def test_the_verdict_does_not_vary_with_the_hash_seed(
        self, tmp_path: Path, order: str,
    ) -> None:
        """The cell that was impossible before the fix.

        At the branch point this fixture's verdict tracked ``PYTHONHASHSEED``
        — accepted under some, ``[E121] body has type Bool`` under others —
        because the binding came from iterating a set of module paths.  With
        the name refused there is no binding to pick, so every seed must give
        one byte-identical answer, message and location included.
        """
        main_path = _write(tmp_path, _FLAP_FILES[order])
        prints = {seed: _fingerprint(_check_json(main_path, seed=seed))
                  for seed in _SEEDS}
        assert len(set(prints.values())) == 1, (
            "the verdict varies with PYTHONHASHSEED: "
            + json.dumps({s: json.loads(p) for s, p in prints.items()},
                         indent=2)
        )
        assert "E155" in _codes(_check_json(main_path, seed=_SEEDS[0]))

    def test_both_import_orders_give_the_same_diagnostic_codes(
        self, tmp_path: Path,
    ) -> None:
        """One import SET, one verdict, however it is spelled.

        Weaker than the per-order fingerprint (the two orders legitimately
        name their modules in a different sequence, so their MESSAGES differ)
        and aimed at the other half of the question: whether the rule reads
        the import list as an ordered sequence at all.
        """
        codes = {
            order: _codes(_check_json(
                _write(tmp_path / order, files), seed="0",
            ))
            for order, files in _FLAP_FILES.items()
        }
        assert codes["ab"] == codes["ba"] == ["E155", "E200"]

    def test_the_refused_name_binds_to_nothing(
        self, tmp_path: Path,
    ) -> None:
        """The bare call misses (E200) rather than resolving to a supplier.

        The other half of "no pick": had the checker reported the clash and
        then injected one supplier anyway, the follow-on diagnostics would
        still be keyed to whichever module the injection loop reached first,
        and E155 would be a label on a nondeterminism it had not removed.
        Here the ambiguous name is in no namespace, so what follows a bare
        call to it is the same miss under every seed.
        """
        main_path = _write(tmp_path, _FLAP_FILES["ab"])
        payload = _check_json(main_path, seed="0")
        misses = [d for d in payload["warnings"]
                  if d["error_code"] == "E200"]
        assert len(misses) == 1, payload["warnings"]
        assert "gen" in misses[0]["description"]
        assert misses[0]["location"]["file"].endswith("midc.vera")


class TestTheRefusalIsDefinitionGated:
    """It fires on the import PAIR, not on a use — as E608 always has."""

    _NO_CALL_MAIN = """\
import libint;
import libbool;

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == 7)
  effects(pure)
{ 7 }
"""

    _QUALIFIED_MID = f"""\
module midc;

import libint;
import libbool;

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER})
  effects(pure)
{{ libint::gen(@Bool.0) }}
"""

    def test_an_unused_ambiguous_name_is_still_refused(
        self, tmp_path: Path,
    ) -> None:
        """No body names ``gen``; the program is refused anyway.

        This is the semantics codegen's rail already had — the same program
        is E608 at the branch point, with `vera check` green — so the two
        layers now answer one question the same way instead of disagreeing
        about when the shape becomes illegal.
        """
        main_path = _write(tmp_path, {
            "libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
            "main.vera": self._NO_CALL_MAIN,
        })
        payload = _check_json(main_path, seed="0")
        assert _codes(payload) == ["E155"]

    def test_swapping_a_bare_call_for_a_qualified_one_does_not_clear_it(
        self, tmp_path: Path,
    ) -> None:
        """The qualified form alone is not the escape hatch, and never was.

        Worth pinning because the opposite is the intuitive reading of
        §8.5.3's design note: qualification disambiguates a CALL, but the
        clash is in the import list, and this shape is refused at the branch
        point too (E608, at compile).  What the refusal changes is the layer
        and the message, not the verdict.  The two shapes that DO clear it
        are in :class:`TestTheEscapeHatches`.
        """
        main_path = _write(tmp_path, {
            "libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
            "midc.vera": self._QUALIFIED_MID, "main.vera": _MAIN_VIA_MID,
        })
        payload = _check_json(main_path, seed="0")
        assert _codes(payload) == ["E155"]


class TestTheEscapeHatches:
    """Two ways out, each green through to the runtime value.

    Asserted to the VALUE, not to "no diagnostics": a disambiguation that
    resolved to the wrong supplier would be silent at check and wrong at run,
    which is the failure mode the refusal exists to prevent.
    """

    def test_a_local_declaration_takes_every_bare_call(
        self, tmp_path: Path,
    ) -> None:
        """§8.5.2: declare the name and both imports stay reachable.

        The bare call is the local one, and each dependency's is still
        available through the module-qualified form — so this shape keeps
        access to BOTH suppliers, which selective import cannot.
        """
        midc = f"""\
module midc;

import libint;
import libbool;

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LOCAL_ANSWER})
  effects(pure)
{{ {LOCAL_ANSWER} }}

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LOCAL_ANSWER + INT_ANSWER})
  effects(pure)
{{ gen(@Bool.0) + libint::gen(@Bool.0) }}
"""
        main = f"""\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {LOCAL_ANSWER + INT_ANSWER})
  effects(pure)
{{ doorc(true) }}
"""
        assert _answer(tmp_path, {
            "libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
            "midc.vera": midc, "main.vera": main,
        }) == LOCAL_ANSWER + INT_ANSWER

    def test_selective_import_leaves_one_supplier(
        self, tmp_path: Path,
    ) -> None:
        """§8.5's design note: name exactly what is needed.

        ``libbool`` is imported for ``other`` alone, so only ``libint``
        supplies ``gen`` and the bare call has one meaning.
        """
        midc = f"""\
module midc;

import libint(gen);
import libbool(other);

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER + OTHER_ANSWER})
  effects(pure)
{{ gen(@Bool.0) + other(@Bool.0) }}
"""
        main = f"""\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER + OTHER_ANSWER})
  effects(pure)
{{ doorc(true) }}
"""
        assert _answer(tmp_path, {
            "libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
            "midc.vera": midc, "main.vera": main,
        }) == INT_ANSWER + OTHER_ANSWER


class TestNonAmbiguousShapesAreUnmoved:
    """The refusal keys on bare-name ambiguity and nothing wider."""

    def test_one_import_supplying_the_name(self, tmp_path: Path) -> None:
        """A single supplier is not a clash however many imports there are."""
        midc = f"""\
module midc;

import libint;

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""
        assert _answer(tmp_path, {
            "libint.vera": _LIB_INT, "midc.vera": midc,
            "main.vera": _MAIN_VIA_MID,
        }) == INT_ANSWER

    def test_two_imports_supplying_different_names(
        self, tmp_path: Path,
    ) -> None:
        """Two wildcard imports whose exports do not overlap on the name in
        question: ``gen`` comes from one, ``other`` from the other."""
        midc = f"""\
module midc;

import libint;
import libbool(other);

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER + OTHER_ANSWER})
  effects(pure)
{{ gen(@Bool.0) + other(@Bool.0) }}
"""
        main = f"""\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER + OTHER_ANSWER})
  effects(pure)
{{ doorc(true) }}
"""
        assert _answer(tmp_path, {
            "libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
            "midc.vera": midc, "main.vera": main,
        }) == INT_ANSWER + OTHER_ANSWER

    def test_a_private_namesake_is_not_a_supplier(
        self, tmp_path: Path,
    ) -> None:
        """Only PUBLIC declarations an import list admits can clash.

        ``libpriv`` declares ``gen`` too, but privately, so it supplies
        nothing to an importer — the shape #1281's relaxation is for, and one
        an ambiguity test reading declarations rather than exports would
        wrongly refuse.
        """
        libpriv = f"""\
module libpriv;

private forall<T> fn gen(@T -> @Int)
  requires(true)
  ensures(@Int.result == {LOCAL_ANSWER})
  effects(pure)
{{ {LOCAL_ANSWER} }}

public fn door_priv(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {LOCAL_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""
        midc = f"""\
module midc;

import libint;
import libpriv;

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER + LOCAL_ANSWER})
  effects(pure)
{{ gen(@Bool.0) + door_priv(@Bool.0) }}
"""
        main = f"""\
import midc(doorc);

public fn main(@Unit -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER + LOCAL_ANSWER})
  effects(pure)
{{ doorc(true) }}
"""
        assert _answer(tmp_path, {
            "libint.vera": _LIB_INT, "libpriv.vera": libpriv,
            "midc.vera": midc, "main.vera": main,
        }) == INT_ANSWER + LOCAL_ANSWER

    def test_a_private_data_type_is_not_a_supplier(
        self, tmp_path: Path,
    ) -> None:
        """The data twin of the private-function control.

        Only PUBLIC declarations an import list admits can clash, on this
        side too: `libpriv` declares its own `Shape` privately, which
        supplies nothing to an importer, so the bare name has one supplier
        and no refusal is owed.

        Asserted at CHECK only, unlike its function counterpart, because
        this program cannot reach a runtime value: E609 refuses two modules'
        same-named data declarations without consulting visibility either, so
        a private namesake is enough to stop compilation.  That is the rail's
        breadth rather than this refusal's, and asserting silence here is
        what keeps the two from being confused.
        """
        libpriv = """\
module libpriv;

private data Shape {
  Hidden
}

public fn door_priv(@Unit -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  match Hidden {
    Hidden -> 4
  }
}
"""
        files = {
            "liba.vera": _ADT_A, "libpriv.vera": libpriv,
            "midc.vera": _ADT_MID.replace("import libb;", "import libpriv;"),
            "main.vera": _ADT_MAIN,
        }
        assert _error_codes(_check_json(_write(tmp_path, files),
                                        seed="0")) == []

    def test_an_out_of_filter_namesake_is_not_a_supplier(
        self, tmp_path: Path,
    ) -> None:
        """A public export the importer's selective list omits supplies
        nothing either — the filter is part of what "supplies" means."""
        midc = f"""\
module midc;

import libint;
import libbool(other);

public fn doorc(@Bool -> @Int)
  requires(true)
  ensures(@Int.result == {INT_ANSWER})
  effects(pure)
{{ gen(@Bool.0) }}
"""
        assert _answer(tmp_path, {
            "libint.vera": _LIB_INT, "libbool.vera": _LIB_BOOL,
            "midc.vera": midc, "main.vera": _MAIN_VIA_MID,
        }) == INT_ANSWER


def _answer(tmp_path: Path, files: dict[str, str]) -> object:
    """Check + verify + compile + run, asserting every stage agrees."""
    verify_errors, result, cg_errors = build_multi_module(tmp_path, files)
    assert not cg_errors, f"codegen errors: {cg_errors}"
    assert not verify_errors, f"verify errors: {verify_errors}"
    kind, payload = module_value(result)
    assert kind == "ok", f"module did not load/run: {payload}"
    return payload
