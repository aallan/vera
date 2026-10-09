"""Tests for scripts/check_examples_run.py — the harness gate that RUNS
the examples.

The gate's design has three separable parts, and each is tested here:

- **The coverage rule** (`check_coverage`) — every ``examples/*.vera`` on
  disk is either in ``RUN_SPECS`` or in ``SKIPS``.  An unclassified
  example is an ERROR, so adding an example forces classifying it; a
  table key with no file on disk is an ERROR too, so a deleted example
  cannot leave a suppression behind.
- **The documentation cross-check** (`check_testing_md`) — TESTING.md's
  execution-model table must agree with the script's own classification:
  the codebase is the oracle and the doc must match it.
- **The runner** (`run_corpus`) — a seeded corpus proves the gate goes red
  on a program that traps at runtime and green on one that does not.

Two conventions are asserted throughout: a regex or glob that matches
nothing must be an ERROR rather than a silent pass (otherwise a rewording
switches the gate off), and each check is exercised in both directions — a passing case
alongside the failing one it is supposed to catch, so a check that can
only ever return ``[]`` cannot masquerade as green.
"""

from __future__ import annotations

import importlib.util
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

_SCRIPT = Path(__file__).parent.parent / "scripts" / "check_examples_run.py"
_ROOT = Path(__file__).parent.parent


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("check_examples_run", _SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


_MOD = _load()


# ---------------------------------------------------------------------------
# Synthetic corpora
# ---------------------------------------------------------------------------

# A program that returns a value and exits cleanly.
_CLEAN_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1 + 1
}
"""

# A program that type-checks and compiles but traps at runtime: the index
# is out of bounds, so the emitted bounds guard fires.  This is the shape
# the gate exists to catch — `vera check` and `vera verify` both accept a
# program whose runtime behaviour is broken.
_TRAPPING_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1, 2, 3];
  @Array<Int>.0[10]
}
"""


# A program whose only external-resource signal is its declared effect
# ROW: `DB` is in ``RESOURCE_EFFECTS``, while `DB.execute` is not in
# ``RESOURCE_OPS`` — so a derivation that stopped reading effect rows
# would find nothing here.
_DB_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(<DB, IO>)
{
  let @Array<Option<String>> = [];
  match DB.execute("CREATE TABLE t (id INTEGER)", @Array<Option<String>>.0) {
    Err(@String) -> {
      IO.print(@String.0);
      1
    },
    Ok(@Int) -> {
      IO.print("created the table");
      0
    }
  }
}
"""

# The mirror image: the only signal is an operation CALL.  `IO` is not in
# ``RESOURCE_EFFECTS`` — sixteen examples declare a bare `<IO>` and only
# one touches the filesystem — so a derivation that stopped reading call
# sites would find nothing here.
_FILE_SRC = """\
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.read_file("hello.txt") {
    Ok(@String) -> IO.print(@String.0),
    Err(@String) -> IO.print(@String.0)
  }
}
"""

# Both shapes in prose only.  A text scan would call this a database
# program; the derivation reads the parsed declarations, so it does not.
_COMMENTED_SRC = """\
-- Names the <DB> effect and IO.read_file in prose, and uses neither.
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  -- effects(<DB>) would go here, and IO.write_file("a", "b") below.
  1 + 1
}
"""

# Not Vera at all — the parse must fail rather than yield "no signals".
_UNPARSEABLE_SRC = "public fn main(-> @Int) { this is not Vera at all\n"


# A module-qualified effect whose tail is `DB`.  `Mod.DB` names a user
# effect in another module, not the built-in the registry check validated,
# so the derivation must not credit it (#1329 review).
_QUALIFIED_DB_SRC = """\
public fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(<Mod.DB>)
{
  0
}
"""


def _corpus(tmp_path: Path, programs: dict[str, str]) -> Path:
    d = tmp_path / "examples"
    d.mkdir(exist_ok=True)
    for name, src in programs.items():
        (d / f"{name}.vera").write_text(src, encoding="utf-8")
    return d


# ---------------------------------------------------------------------------
# The coverage rule
# ---------------------------------------------------------------------------


class TestCoverageRule:
    """Every example is classified; nothing is classified that isn't there."""

    def test_real_corpus_is_fully_classified(self) -> None:
        """The shipped tables cover the shipped corpus — no unclassified
        example, no stale key.  This is the assertion that goes red when
        somebody adds `examples/new_thing.vera` without deciding whether
        the harness can run it."""
        names = _MOD.example_names(_ROOT / "examples")
        assert _MOD.check_coverage(names, _MOD.RUN_SPECS, _MOD.SKIPS) == []

    def test_every_example_on_disk_appears_in_exactly_one_table(self) -> None:
        names = set(_MOD.example_names(_ROOT / "examples"))
        assert names == set(_MOD.RUN_SPECS) | set(_MOD.SKIPS)
        assert not (set(_MOD.RUN_SPECS) & set(_MOD.SKIPS))

    def test_unclassified_example_is_an_error(self) -> None:
        """The heart of the anti-rot rule: an example on disk that neither
        table names fails the gate."""
        errors = _MOD.check_coverage(
            ["known", "brand_new"], {"known": _MOD.RunSpec()}, {}
        )
        assert len(errors) == 1
        assert "brand_new" in errors[0]
        assert "unclassified" in errors[0].lower()

    def test_stale_run_spec_is_an_error(self) -> None:
        """A RUN_SPECS key whose file was deleted or renamed is an error —
        otherwise the entry silently stops covering anything.

        The message must name the table it came from: both stale branches
        report the same example-name shape, so asserting the name alone
        passes whichever fired and cannot tell a stale run spec from a
        stale skip.
        """
        errors = _MOD.check_coverage(
            ["known"],
            {"known": _MOD.RunSpec(), "deleted": _MOD.RunSpec()},
            {},
        )
        assert len(errors) == 1
        assert "deleted" in errors[0]
        assert "RUN_SPECS" in errors[0]
        assert "SKIPS" not in errors[0]

    def test_stale_skip_is_an_error(self) -> None:
        """The same for a skip: a suppression outliving its example would
        quietly mask a re-added example with the same name."""
        errors = _MOD.check_coverage(
            ["known"], {"known": _MOD.RunSpec()}, {"gone": "network"}
        )
        assert len(errors) == 1
        assert "gone" in errors[0]
        assert "SKIPS" in errors[0]
        assert "RUN_SPECS" not in errors[0]

    def test_example_in_both_tables_is_an_error(self) -> None:
        """Ambiguous classification: which one wins is not a question the
        gate should have to answer."""
        errors = _MOD.check_coverage(
            ["both"], {"both": _MOD.RunSpec()}, {"both": "network"}
        )
        assert any("both" in e and "both tables" in e for e in errors)

    def test_unknown_skip_property_is_an_error(self) -> None:
        """A skip must cite a property from the documented set, so every
        suppression carries a stated reason the report can print."""
        errors = _MOD.check_coverage(["x"], {}, {"x": "because-i-said-so"})
        assert len(errors) == 1
        assert "because-i-said-so" in errors[0]
        assert "SKIP_PROPERTIES" in errors[0]

    def test_empty_corpus_is_an_error(self) -> None:
        """A glob that matches nothing is an ERROR, not a vacuous pass.
        Without this the gate reports success the moment its glob stops
        matching — the failure mode the whole check exists to rule out."""
        errors = _MOD.check_coverage([], {}, {})
        assert len(errors) == 1
        assert "no examples" in errors[0].lower()

    def test_example_names_reads_from_disk(self, tmp_path: Path) -> None:
        d = _corpus(tmp_path, {"b": _CLEAN_SRC, "a": _CLEAN_SRC})
        assert _MOD.example_names(d) == ["a", "b"]

    def test_example_names_ignores_nested_module_libraries(
        self, tmp_path: Path
    ) -> None:
        """`examples/vera/` holds the modules `modules.vera` imports.  They
        are not standalone programs and the corpus glob must not treat them
        as unclassified examples."""
        d = _corpus(tmp_path, {"top": _CLEAN_SRC})
        nested = d / "vera"
        nested.mkdir()
        (nested / "lib.vera").write_text(_CLEAN_SRC, encoding="utf-8")
        assert _MOD.example_names(d) == ["top"]


class TestRunSpecsAreWellFormed:
    """The specs must name entry points that exist, or the gate would be
    measuring `vera run`'s argument handling rather than the examples."""

    def test_every_named_fn_is_public_in_its_example(self) -> None:
        bad = []
        for name, spec in _MOD.RUN_SPECS.items():
            src = (_ROOT / "examples" / f"{name}.vera").read_text(
                encoding="utf-8"
            )
            if f"public fn {spec.fn}(" not in src:
                bad.append(f"{name}: no `public fn {spec.fn}`")
        assert bad == []

    def test_no_spec_relies_on_the_first_export_fallback(self) -> None:
        """`vera run` with no `--fn` falls back to the *first export*, and
        that fallback is a silent pass waiting to happen: privatise or
        rename `main` and the gate runs some other function at exit 0.
        Every spec names its entry point, so the CLI resolves it by name
        and exits 1 when it is gone.

        Asserted on the built argv rather than on ``spec.fn`` being
        truthy: ``fn`` defaults to ``"main"``, so a truthiness check
        passes for every spec that could ever exist short of a
        deliberate ``fn=""`` — it restates the default instead of
        testing the property, which is that ``--fn`` reaches the CLI.
        """
        for name, spec in _MOD.RUN_SPECS.items():
            cmd = _MOD.build_command(
                "py", _ROOT / "examples" / f"{name}.vera", spec
            )
            assert "--fn" in cmd, name
            assert cmd[cmd.index("--fn") + 1] == spec.fn, name

    def test_environment_dependent_specs_carry_an_output_sentinel(
        self,
    ) -> None:
        """An example that reaches outside the process answers a failure by
        printing a message and completing normally, so exit code alone
        cannot tell its success path from its graceful one: each must pin a
        substring only the success path prints.

        WHICH examples those are is derived from the corpus, not listed
        here.  A literal `("sqlitedb", "database", "file_io")` asserts the
        sentinels the corpus already has and nothing about the next
        example of the same kind — the one case the rule exists for.  So
        the assertion is the two-way equality between the examples that
        *declare* an external resource and the specs that carry an
        `expect`, which a new database or filesystem example joins by
        being written rather than by being remembered.
        """
        assert _MOD.check_sentinel_coverage(
            _ROOT / "examples", _MOD.RUN_SPECS
        ) == []

    def test_every_skip_property_is_documented(self) -> None:
        for name, prop in _MOD.SKIPS.items():
            assert prop in _MOD.SKIP_PROPERTIES, name
            assert _MOD.SKIP_PROPERTIES[prop].strip(), prop

    def test_no_unused_skip_property(self) -> None:
        """A property nothing cites is dead documentation that would drift."""
        assert set(_MOD.SKIP_PROPERTIES) == set(_MOD.SKIPS.values())


# ---------------------------------------------------------------------------
# The derived sentinel rule
# ---------------------------------------------------------------------------


class TestResourceSignalDerivation:
    """Which examples must pin a sentinel is read off the examples.

    The declared constants are resource *names* — the `DB` effect, the
    `IO.read_file` / `IO.write_file` operations — and the example set
    follows from which programs declare them.  Names rather than
    filenames is the whole point: a filename list is a snapshot of
    today's corpus, and the case the rule exists for is tomorrow's
    example.

    An effect row alone cannot discriminate, which is why the operations
    are read too: `FileIO` and `Time` are not effects in Vera, so
    `file_io.vera` declares the same bare `<IO>` that `hello_world.vera`
    does, and only the `IO.read_file` call tells them apart.
    """

    def test_declared_resource_names_are_all_live(self) -> None:
        """Every name in ``RESOURCE_EFFECTS`` / ``RESOURCE_OPS`` still
        exists in the effect registry the compiler serves."""
        assert _MOD.resource_registry_errors() == []

    def test_an_effect_row_signal_is_derived(self, tmp_path: Path) -> None:
        """A `<DB>` in the effect row is a signal.  `DB.execute` is not in
        ``RESOURCE_OPS``, so this program's whole signal comes from the
        row — an exact-set assertion, so an implementation that credited
        the call site instead would not pass."""
        d = _corpus(tmp_path, {"dbish": _DB_SRC})
        assert _MOD.resource_signals(d / "dbish.vera") == frozenset({"DB"})

    def test_an_operation_call_signal_is_derived(
        self, tmp_path: Path
    ) -> None:
        """The mirror image: `IO` is not a resource effect, so this
        program's whole signal comes from the `IO.read_file` call."""
        d = _corpus(tmp_path, {"filish": _FILE_SRC})
        assert _MOD.resource_signals(d / "filish.vera") == frozenset(
            {"IO.read_file"}
        )

    def test_a_resource_free_example_declares_no_signal(
        self, tmp_path: Path
    ) -> None:
        """The other direction, without which a derivation that returned
        every name for every program would pass the two above."""
        d = _corpus(tmp_path, {"pure": _CLEAN_SRC})
        assert _MOD.resource_signals(d / "pure.vera") == frozenset()

    def test_signals_come_from_the_declarations_not_the_comments(
        self, tmp_path: Path
    ) -> None:
        """The derivation reads the parsed program, so prose naming `<DB>`
        or `IO.read_file` is not a resource declaration.

        Not hypothetical: `examples/sqlitedb.vera`'s first line is a
        comment containing `<DB>`, so a text scan would agree with the
        parse there by luck and disagree on the first example whose
        header describes what it deliberately does *not* do.
        """
        d = _corpus(tmp_path, {"prose": _COMMENTED_SRC})
        assert _MOD.resource_signals(d / "prose.vera") == frozenset()

    def test_a_pinned_spec_whose_file_is_gone_is_not_mis_diagnosed(
        self, tmp_path: Path
    ) -> None:
        """The derivation never opened it, so it cannot say what it
        declares.  Building `pinned` from every entry in `run_specs` put
        this spec into `pinned - signals_by_name`, where it drew the
        spurious-sentinel wording — "declares no external resource" —
        for a file that does not exist (#1329 review).
        """
        d = _corpus(tmp_path, {"present": _DB_SRC})
        specs = {
            "present": _MOD.RunSpec(expect="created the table"),
            "vanished": _MOD.RunSpec(expect="never printed"),
        }
        errors = _MOD.check_sentinel_coverage(d, specs)
        assert not [e for e in errors if "vanished" in e]

    def test_a_module_qualified_effect_is_not_the_builtin(
        self, tmp_path: Path
    ) -> None:
        """`Mod.DB` is another module's effect, not the registry's `DB`.

        `resource_signals` narrows on `isinstance(ref, ast.EffectRef)`
        precisely to drop it, and no cell reached that decision: a mutant
        dropping the narrowing, or one crediting any reference whose tail
        is `DB`, passed every other case here.  This is the boundary in
        the direction `_COMMENTED_SRC` does not cover — that one is prose,
        this one is a real declaration of a different effect (#1329
        review).
        """
        d = _corpus(tmp_path, {"qualified": _QUALIFIED_DB_SRC})
        assert _MOD.resource_signals(d / "qualified.vera") == frozenset()

    def test_a_renamed_resource_effect_is_an_error(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """A resource effect the registry no longer has must fail loudly.

        Silently, it would match no example — and with nothing left
        requiring a sentinel the rule switches itself off.  The
        *registry* diagnosis is asserted, not merely that an error came
        back: the coinciding-message trap, since the matched-nothing
        guard also fires on this input and reads as a different fault.
        """
        monkeypatch.setattr(_MOD, "RESOURCE_EFFECTS", ("Databayse",))
        d = _corpus(tmp_path, {"dbish": _DB_SRC})
        errors = _MOD.check_sentinel_coverage(d, {"dbish": _MOD.RunSpec()})
        assert len(errors) == 1
        assert "Databayse" in errors[0]
        assert "could not find" in errors[0]
        assert "no longer gated" not in errors[0]

    def test_a_renamed_resource_op_is_an_error(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """The same for an operation: `IO` exists, `read_flie` does not."""
        monkeypatch.setattr(
            _MOD, "RESOURCE_OPS", (("IO", "read_flie"),)
        )
        d = _corpus(tmp_path, {"filish": _FILE_SRC})
        errors = _MOD.check_sentinel_coverage(d, {"filish": _MOD.RunSpec()})
        assert len(errors) == 1
        assert "read_flie" in errors[0]
        assert "could not find" in errors[0]
        assert "no longer gated" not in errors[0]

    def test_a_resource_op_under_an_unknown_effect_is_an_error(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """An operation is only meaningful under an effect that exists, and
        looking its name up under a missing one must not be read as the
        operation being absent."""
        monkeypatch.setattr(
            _MOD, "RESOURCE_OPS", (("FileIO", "read_file"),)
        )
        d = _corpus(tmp_path, {"filish": _FILE_SRC})
        errors = _MOD.check_sentinel_coverage(d, {"filish": _MOD.RunSpec()})
        assert len(errors) == 1
        assert "FileIO" in errors[0]
        assert "could not find" in errors[0]
        # The discriminating half.  BOTH branches say "could not find" and
        # both interpolate `{effect}.{op}`, so the three assertions above
        # are satisfied by either — including by the operation-missing
        # branch, which would have raised KeyError on `live_ops[effect]`
        # to get there.  This pins the branch that avoids it (#1329 review).
        assert "has no 'FileIO'" in errors[0]
        assert "read_file" not in errors[0].split("could not find")[1]


class TestDerivedSentinelCoverage:
    """The two-way equality: the examples that declare an external
    resource are exactly the specs that carry an ``expect``.

    Both directions are errors.  A resource-touching example with no
    sentinel passes on its graceful arm the day its fixture vanishes,
    which is the failure the sentinels exist to catch; a sentinel on an
    example with no resource re-pins stdout the dedicated tests own and
    goes red on a cosmetic edit.
    """

    def test_a_new_database_example_needs_a_sentinel(
        self, tmp_path: Path
    ) -> None:
        """The property a hard-coded triple could not have: an example
        under a name no table has ever heard of is required to pin a
        sentinel because of what it declares."""
        d = _corpus(tmp_path, {"brand_new_db": _DB_SRC})
        errors = _MOD.check_sentinel_coverage(
            d, {"brand_new_db": _MOD.RunSpec()}
        )
        assert len(errors) == 1
        assert "brand_new_db" in errors[0]
        assert "expect" in errors[0]

    def test_a_new_filesystem_example_needs_a_sentinel(
        self, tmp_path: Path
    ) -> None:
        """The same through the operation half of the derivation, which
        the effect row cannot reach: `<IO>` is what sixteen examples
        declare, and only the `IO.read_file` call marks this one."""
        d = _corpus(tmp_path, {"brand_new_file": _FILE_SRC})
        errors = _MOD.check_sentinel_coverage(
            d, {"brand_new_file": _MOD.RunSpec()}
        )
        assert len(errors) == 1
        assert "brand_new_file" in errors[0]
        assert "expect" in errors[0]

    def test_a_resource_touching_example_with_a_sentinel_passes(
        self, tmp_path: Path
    ) -> None:
        """The green direction, without which a check that always
        returned an error would pass the two above."""
        d = _corpus(tmp_path, {"dbish": _DB_SRC, "filish": _FILE_SRC})
        assert _MOD.check_sentinel_coverage(
            d,
            {
                "dbish": _MOD.RunSpec(expect="created the table"),
                "filish": _MOD.RunSpec(expect="Hello from Vera!"),
            },
        ) == []

    def test_a_sentinel_on_a_resource_free_example_is_an_error(
        self, tmp_path: Path
    ) -> None:
        """The other direction of the equality.  Without it the rule is
        one-way and a spec can pin stdout on any example at all — which
        is the duplication of the dedicated output tests that the gate's
        design deliberately refuses."""
        d = _corpus(tmp_path, {"dbish": _DB_SRC, "pure": _CLEAN_SRC})
        errors = _MOD.check_sentinel_coverage(
            d,
            {
                "dbish": _MOD.RunSpec(expect="created the table"),
                "pure": _MOD.RunSpec(expect="2"),
            },
        )
        assert len(errors) == 1
        assert "pure" in errors[0]
        assert "dbish" not in errors[0]

    def test_an_empty_derived_set_is_an_error_not_a_skip(
        self, tmp_path: Path
    ) -> None:
        """A derivation that matches nothing must fail, not pass.

        The corpus below is resource-free and its specs pin nothing, so
        both sides of the equality are empty and the equality *holds* —
        a vacuous green that would also be the verdict if the walk
        broke, an effect were renamed, or the parse silently returned
        nothing.  The whole rule would be switched off and every gate
        run would report success.
        """
        d = _corpus(tmp_path, {"pure": _CLEAN_SRC, "also_pure": _CLEAN_SRC})
        errors = _MOD.check_sentinel_coverage(
            d, {"pure": _MOD.RunSpec(), "also_pure": _MOD.RunSpec()}
        )
        assert len(errors) == 1
        assert "no longer gated" in errors[0]

    def test_an_unparseable_example_is_an_error_not_an_empty_signal_set(
        self, tmp_path: Path
    ) -> None:
        """A program the parse cannot read has *unknown* signals, and
        unknown must not be spelled the same as none.

        Read as none, a file that stopped parsing would silently leave
        the sentinel rule — and the diagnosis a reader got would be the
        opposite one, that its sentinel covers no resource.
        """
        d = _corpus(tmp_path, {"broken": _UNPARSEABLE_SRC, "dbish": _DB_SRC})
        errors = _MOD.check_sentinel_coverage(
            d,
            {
                "broken": _MOD.RunSpec(),
                "dbish": _MOD.RunSpec(expect="created the table"),
            },
        )
        assert len(errors) == 1
        assert "broken" in errors[0]
        assert "could not be parsed" in errors[0]

    def test_main_computes_the_rule_and_reports_it(self) -> None:
        """A structural pin on the wiring, the technique
        `test_the_runner_hands_both_streams_to_the_output_check` uses and
        for the same reason: reaching `main` end to end means running all
        34 examples under the native runtime, which no unit test can
        afford, so nothing else here can distinguish a `main` that
        computes the sentinel errors from one that drops them on the
        floor.  That mutant is the most consequential of the lot — the
        rule would hold in this file and gate nothing in CI — so it gets
        the tripwire.
        """
        import inspect

        src = inspect.getsource(_MOD.main)
        assert re.search(
            r"sentinel_errors\s*=\s*check_sentinel_coverage\(", src
        ), src
        # And the result reaches the report, rather than being computed
        # and discarded: passing `[]` in its place would satisfy a
        # presence check on the name alone.
        assert re.search(
            r"error_blocks\(\s*\[\]\s*,\s*sentinel_errors\s*,", src
        ), src


class TestBuildCommand:
    def test_default_spec_names_main_explicitly(self) -> None:
        """No spec leaves the entry point implicit — see
        `test_no_spec_relies_on_the_first_export_fallback`."""
        cmd = _MOD.build_command("py", Path("/x/a.vera"), _MOD.RunSpec())
        assert cmd[:4] == ["py", "-m", "vera.cli", "run"]
        assert cmd[-2:] == ["--fn", "main"]

    def test_named_entry_point_and_args(self) -> None:
        cmd = _MOD.build_command(
            "py", Path("/x/a.vera"), _MOD.RunSpec(fn="f", args=("1", "-2"))
        )
        assert cmd[-5:] == ["--fn", "f", "--", "1", "-2"]

    def test_db_fixture_env_points_at_the_committed_sqlite(self) -> None:
        env = _MOD.spec_env(
            _MOD.RunSpec(needs_db_fixture=True), _ROOT / "examples"
        )
        assert env["VERA_DB_URL"].startswith("sqlite:///")
        assert env["VERA_DB_URL"].endswith("examples/sqlitedb.sqlite")

    def test_no_db_fixture_adds_no_env(self) -> None:
        assert _MOD.spec_env(_MOD.RunSpec(), _ROOT / "examples") == {}


class TestFixturePrecondition:
    """A missing fixture must stop the run, not be papered over by it.

    `sqlite3` CREATES the database file named by a `sqlite:///` URL when
    it is not there.  Handing the example a URL for an absent fixture
    therefore materialises an empty `examples/sqlitedb.sqlite` as a side
    effect of the gate — the sentinel still fails the run, so the verdict
    is right, but the gate has written into the corpus it is checking,
    which is precisely what the per-run scratch directory exists to
    prevent.  The fixture is checked before the process starts.
    """

    def test_present_fixture_is_not_reported(self) -> None:
        assert _MOD.missing_fixture(
            _MOD.RunSpec(needs_db_fixture=True), _ROOT / "examples"
        ) is None

    def test_absent_fixture_is_reported_by_path(self, tmp_path: Path) -> None:
        missing = _MOD.missing_fixture(
            _MOD.RunSpec(needs_db_fixture=True), tmp_path
        )
        assert missing is not None
        assert missing.name == "sqlitedb.sqlite"

    def test_specs_that_need_no_fixture_are_not_reported(
        self, tmp_path: Path
    ) -> None:
        assert _MOD.missing_fixture(_MOD.RunSpec(), tmp_path) is None

    def test_absent_fixture_fails_the_gate_and_creates_nothing(
        self, tmp_path: Path
    ) -> None:
        """The proving test, on the real example: the run must fail
        naming the fixture, and must leave no file behind where the
        fixture would have been."""
        d = tmp_path / "examples"
        d.mkdir()
        (d / "sqlitedb.vera").write_text(
            (_ROOT / "examples" / "sqlitedb.vera").read_text(
                encoding="utf-8"
            ),
            encoding="utf-8",
        )
        fixture = d / "sqlitedb.sqlite"
        assert not fixture.exists()

        failures = _MOD.run_corpus(
            d, {"sqlitedb": _MOD.RunSpec(needs_db_fixture=True)}, tmp_path
        )
        assert len(failures) == 1
        assert "sqlitedb.sqlite" in failures[0]
        assert not fixture.exists(), (
            "the gate created the fixture it was checking for — sqlite3 "
            "materialises an absent database, so the URL must not be "
            "handed over at all"
        )


class TestHermeticEnvironment:
    """The gate must measure the examples, not the developer's shell.

    `database.vera` and `sqlitedb.vera` both read `VERA_DB_URL`, and the
    inference examples read six provider keys.  An ambient value would
    change what the gate exercises — at worst pointing a run at somebody's
    real database — so the runner strips them and puts back only what a
    spec explicitly asks for.
    """

    def test_ambient_db_url_is_stripped(self) -> None:
        env = _MOD.build_env(
            _MOD.RunSpec(), _ROOT / "examples",
            {"VERA_DB_URL": "postgres://prod/live", "PATH": "/bin"},
        )
        assert "VERA_DB_URL" not in env
        assert env["PATH"] == "/bin"

    def test_ambient_provider_keys_are_stripped(self) -> None:
        base = {f"VERA_{p}_API_KEY": "sk-real" for p in
                ("ANTHROPIC", "OPENAI", "MOONSHOT", "MISTRAL", "XAI",
                 "DEEPSEEK")}
        env = _MOD.build_env(_MOD.RunSpec(), _ROOT / "examples", base)
        assert [k for k in env if k.endswith("_API_KEY")] == []

    def test_fixture_spec_puts_its_own_db_url_back(self) -> None:
        env = _MOD.build_env(
            _MOD.RunSpec(needs_db_fixture=True), _ROOT / "examples",
            {"VERA_DB_URL": "postgres://prod/live"},
        )
        assert env["VERA_DB_URL"].startswith("sqlite:///")
        assert "prod" not in env["VERA_DB_URL"]

    def test_every_neutralised_name_is_actually_read_by_an_example(
        self,
    ) -> None:
        """Neutralising a variable nothing reads is dead configuration.
        Each name must appear in the runtime that backs the effect the
        examples use, so the list shrinks when a provider goes away."""
        runtime = (_ROOT / "vera" / "runtime").rglob("*.py")
        blob = "\n".join(p.read_text(encoding="utf-8") for p in runtime)
        for name in _MOD.NEUTRALISED_ENV:
            assert name in blob, name


class TestOutputSignals:
    """Exit code is not enough, and the sibling gate already says so.

    `scripts/check_examples.py` asserts the exit code *and* an output
    sentinel, because either alone can be satisfied by the wrong thing.
    Here the two measured cases are a `main` that stops being callable —
    where `vera run` falls back to an arbitrary export and exits 0 — and
    an external fixture that vanishes, where the example takes its
    graceful arm and exits 0.
    """

    def test_clean_output_passes(self) -> None:
        assert _MOD.check_output("a", _MOD.RunSpec(), "all good") is None

    def test_every_command_names_its_entry_point(self) -> None:
        """What makes the fallback unreachable, pinned.

        `build_command` always passes `--fn`, so `vera run` refuses a
        missing or private export instead of falling back to the first
        one.  The backstop below guards a path the command line cannot
        take *while this holds* — so this is the cell that has to hold
        (#1330 review).
        """
        for name, spec in _MOD.RUN_SPECS.items():
            assert spec.fn, f"{name} names no entry point"
            cmd = _MOD.build_command("python", Path(f"{name}.vera"), spec)
            assert "--fn" in cmd, name
            assert cmd[cmd.index("--fn") + 1] == spec.fn, name

    def test_an_unresolvable_entry_point_fails_loudly(self, tmp_path: Path) -> None:
        """The real path, end to end: the failure a privatised or renamed
        `main` actually produces is a refusal, not a silent fallback."""
        d = _corpus(tmp_path, {"prog": _CLEAN_SRC})
        spec = _MOD.RunSpec(fn="not_an_export")
        result = subprocess.run(
            _MOD.build_command(sys.executable, d / "prog.vera", spec),
            capture_output=True, text=True, encoding="utf-8",
            cwd=str(tmp_path), check=False,
        )
        assert result.returncode != 0, "an unresolvable entry point exited 0"
        combined = result.stdout + result.stderr
        assert "not found in exports" in combined
        assert _MOD.FALLBACK_NOTE not in combined, (
            "vera run fell back instead of refusing, so the backstop below "
            "is load-bearing after all"
        )

    def test_fallback_note_is_a_failure_at_exit_zero(self) -> None:
        """The backstop, kept for a `build_command` that stops passing
        `--fn`.  Unreachable through the live command path — the two
        cells above are what establish that — so it is asserted directly
        on `check_output` rather than end to end."""
        msg = _MOD.check_output(
            "a", _MOD.RunSpec(),
            "Note: no 'main' declared — running public function 'other'.\n7",
        )
        assert msg is not None
        assert "a" in msg
        assert "first export" in msg

    def test_missing_sentinel_is_a_failure(self) -> None:
        msg = _MOD.check_output(
            "sqlitedb", _MOD.RunSpec(expect="read 4 cities"),
            "no cities table — run with VERA_DB_URL=...",
        )
        assert msg is not None
        assert "read 4 cities" in msg

    def test_present_sentinel_passes(self) -> None:
        assert _MOD.check_output(
            "sqlitedb", _MOD.RunSpec(expect="read 4 cities"),
            "read 4 cities from the on-disk database:\nLondon | UK",
        ) is None

    def test_no_sentinel_means_no_output_assertion(self) -> None:
        """Specs without an `expect` are asserted on exit code alone — the
        gate does not re-pin stdout that the dedicated tests own."""
        assert _MOD.check_output("a", _MOD.RunSpec(), "anything at all") is None

    def test_the_runner_hands_both_streams_to_the_output_check(self) -> None:
        """A structural pin, because the behaviour it protects is currently
        unreachable and that is exactly why it needs one.

        `vera run` writes the fallback note to **stderr** and emits nothing
        there on a clean exit, so with `--fn` always passed there is no
        program that can make the note appear at exit 0 — no end-to-end
        fixture can distinguish a runner that reads both streams from one
        that reads only stdout.  The guard is a tripwire for the day
        `--fn` stops being honoured, and a tripwire wired to the wrong
        stream is no tripwire at all.  Pinning the call shape keeps it
        armed; the same technique `tests/test_verifier_refinements.py`
        uses for its Tier-3 disclosure sites.
        """
        import inspect

        src = inspect.getsource(_MOD.run_corpus)
        call = re.search(r"check_output\(([^)]*)\)", src)
        assert call is not None, "run_corpus no longer calls check_output"
        args = call.group(1)
        assert "result.stdout" in args, args
        assert "result.stderr" in args, args


# ---------------------------------------------------------------------------
# The runner
# ---------------------------------------------------------------------------


class TestRunnerGoesRedOnRuntimeFailure:
    """The proving test: a seeded corpus whose program traps must fail the
    gate.  A runner that never reports a failure would pass every other
    test in this file."""

    def test_trapping_example_fails_the_gate(self, tmp_path: Path) -> None:
        d = _corpus(tmp_path, {"boom": _TRAPPING_SRC})
        failures = _MOD.run_corpus(d, {"boom": _MOD.RunSpec()}, tmp_path)
        assert len(failures) == 1
        assert "boom" in failures[0]

    def test_clean_example_passes_the_gate(self, tmp_path: Path) -> None:
        d = _corpus(tmp_path, {"fine": _CLEAN_SRC})
        assert _MOD.run_corpus(d, {"fine": _MOD.RunSpec()}, tmp_path) == []

    def test_mixed_corpus_reports_only_the_broken_one(
        self, tmp_path: Path
    ) -> None:
        """Chosen so a runner that reported every program, or none, is
        distinguishable from one that reports the right one."""
        d = _corpus(tmp_path, {"fine": _CLEAN_SRC, "boom": _TRAPPING_SRC})
        failures = _MOD.run_corpus(
            d, {"fine": _MOD.RunSpec(), "boom": _MOD.RunSpec()}, tmp_path
        )
        assert len(failures) == 1
        assert "boom" in failures[0]
        assert "fine" not in failures[0]

    def test_named_entry_point_is_actually_invoked(
        self, tmp_path: Path
    ) -> None:
        """A runner that ignored ``spec.fn`` would run the same thing for
        both specs below.  One entry point is clean and the other traps, so
        only a runner that honours the spec can be green for one and red for
        the other."""
        src = """\
public fn first(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  0
}

public fn second(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  let @Array<Int> = [1];
  @Array<Int>.0[9]
}
"""
        d = _corpus(tmp_path, {"pick": src})
        assert _MOD.run_corpus(
            d, {"pick": _MOD.RunSpec(fn="first")}, tmp_path
        ) == []
        failures = _MOD.run_corpus(
            d, {"pick": _MOD.RunSpec(fn="second")}, tmp_path
        )
        assert len(failures) == 1

    def test_a_renamed_entry_point_fails_rather_than_falling_back(
        self, tmp_path: Path
    ) -> None:
        """The other half of the privatised-main case: a spec naming an
        entry point the example no longer has must exit 1 on the name,
        never quietly run whatever export happens to be first."""
        d = _corpus(tmp_path, {"pick": _CLEAN_SRC})
        failures = _MOD.run_corpus(
            d, {"pick": _MOD.RunSpec(fn="renamed_away")}, tmp_path
        )
        assert len(failures) == 1
        assert "renamed_away" in failures[0]

    def test_runner_does_not_write_into_the_corpus(
        self, tmp_path: Path
    ) -> None:
        """`file_io.vera` writes `hello.txt` relative to the process CWD.
        The runner must give each example a scratch working directory so a
        gate run leaves no artefact beside the examples."""
        src = """\
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  match IO.write_file("side_effect.txt", "x") {
    Ok(_) -> (),
    Err(@String) -> IO.print(@String.0)
  };

  ()
}
"""
        d = _corpus(tmp_path, {"writer": src})
        before = sorted(p.name for p in d.iterdir())
        assert _MOD.run_corpus(d, {"writer": _MOD.RunSpec()}, tmp_path) == []
        assert sorted(p.name for p in d.iterdir()) == before

    def test_privatised_main_fails_the_gate(self, tmp_path: Path) -> None:
        """The measured silent pass: with `main` no longer callable,
        `vera run` picks the first export and exits 0.  Reproduced here
        with a second export that succeeds, so exit code alone cannot
        distinguish it — only naming the entry point, or catching the
        fallback note, goes red."""
        src = """\
private fn main(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  1
}

public fn other(-> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{
  2
}
"""
        d = _corpus(tmp_path, {"hidden": src})
        failures = _MOD.run_corpus(d, {"hidden": _MOD.RunSpec()}, tmp_path)
        assert len(failures) == 1
        assert "hidden" in failures[0]

    def test_absent_sentinel_fails_the_gate_at_exit_zero(
        self, tmp_path: Path
    ) -> None:
        """The fixture-vanished shape: the program completes normally and
        exits 0 down its graceful arm, printing something other than what
        the success path prints."""
        src = """\
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.print("took the graceful arm")
}
"""
        d = _corpus(tmp_path, {"degraded": src})
        spec = _MOD.RunSpec(expect="read 4 cities")
        failures = _MOD.run_corpus(d, {"degraded": spec}, tmp_path)
        assert len(failures) == 1
        assert "read 4 cities" in failures[0]
        # And the same program passes once its own output is the sentinel,
        # so the check is reading the output rather than always failing.
        assert _MOD.run_corpus(
            d, {"degraded": _MOD.RunSpec(expect="graceful arm")}, tmp_path
        ) == []

    def test_a_hanging_example_is_reported_as_a_timeout(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        """The budget exists so a hung program fails the hook instead of
        blocking it, and until now nothing reached that branch.

        A purpose-built sleeper rather than a real example: `life.vera` is
        the only long-running one in the corpus and it is skipped, so
        driving the branch through it would mean un-skipping it.  The
        budget is monkeypatched down instead of the sleep being made long,
        so the test costs a second rather than the real budget.
        """
        src = """\
public fn main(-> @Unit)
  requires(true)
  ensures(true)
  effects(<IO>)
{
  IO.sleep(30000)
}
"""
        d = _corpus(tmp_path, {"sleeper": src})
        monkeypatch.setattr(_MOD, "TIMEOUT_SECONDS", 5)
        failures = _MOD.run_corpus(d, {"sleeper": _MOD.RunSpec()}, tmp_path)
        assert len(failures) == 1
        # The timeout wording specifically, not merely *a* failure: a
        # sleeper that died some other way would also produce one.
        assert "5s budget" in failures[0]
        assert "hung rather than terminating" in failures[0]

    def test_missing_file_for_a_spec_is_a_failure(
        self, tmp_path: Path
    ) -> None:
        """Belt-and-braces against the runner silently skipping what it
        cannot find; `check_coverage` catches this earlier, but the runner
        must not turn a missing file into a pass on its own."""
        d = _corpus(tmp_path, {"present": _CLEAN_SRC})
        failures = _MOD.run_corpus(
            d, {"present": _MOD.RunSpec(), "absent": _MOD.RunSpec()}, tmp_path
        )
        assert len(failures) == 1
        assert "absent" in failures[0]
        # The specific wording, not merely *a* failure: `vera run` on a path
        # that isn't there exits non-zero of its own accord, so the generic
        # exit-code arm reports this case even with the guard removed.  What
        # the guard adds is the diagnosis — that a RUN_SPECS entry covers
        # nothing — and only asserting that makes the test able to tell the
        # two apart.
        assert "covers nothing" in failures[0]


# ---------------------------------------------------------------------------
# The report
# ---------------------------------------------------------------------------


def _sole_index(blocks: list[str], needle: str) -> int:
    """The index of the one line containing *needle*.

    Position, not presence: `in "\\n".join(blocks)` answers "is this text
    somewhere in the report", which stays true however the lines are
    ordered.  What the report promises is that each error sits *beneath
    its own header*, and only an index can say that.
    """
    matches = [i for i, line in enumerate(blocks) if needle in line]
    assert len(matches) == 1, (
        f"expected exactly one line containing {needle!r}, got "
        f"{len(matches)}: {blocks!r}"
    )
    return matches[0]


class TestErrorBlocks:
    """Each error kind gets its own header carrying its own count, with
    its own errors underneath it.

    Filing one kind's lines under another's header misreports both — a
    reader who counts the lines beneath `COVERAGE ERRORS (n)` gets a
    number the header disagrees with.
    """

    def test_doc_errors_are_never_filed_under_the_coverage_count(
        self,
    ) -> None:
        """Two error kinds, two labelled blocks, each counting its own.
        Printing documentation mismatches beneath a `COVERAGE ERRORS (n)`
        header whose n excludes them misreports both — the reader counts
        the lines and gets a different number from the one on the header.

        Asserted positionally.  Presence plus counts is satisfied by a
        report that emits both headers first and then every error line —
        each string is there, each count is right, and every error is
        attributed to the wrong header.  That is the shape this test
        exists to reject, so the ordering is what it checks.
        """
        blocks = _MOD.error_blocks(
            coverage_errors=["one coverage problem"],
            sentinel_errors=[],
            doc_errors=["one doc problem", "another doc problem"],
            failures=[],
        )
        cov_header = _sole_index(blocks, "COVERAGE ERRORS (1)")
        cov_error = _sole_index(blocks, "one coverage problem")
        doc_header = _sole_index(blocks, "DOCUMENTATION MISMATCH (2)")
        doc_first = _sole_index(blocks, "one doc problem")
        doc_second = _sole_index(blocks, "another doc problem")

        # The coverage error sits under the coverage header, and both doc
        # errors under the documentation one — so no error can be read as
        # belonging to a header that did not count it.
        assert cov_header < cov_error < doc_header
        assert doc_header < doc_first
        assert doc_header < doc_second

        # And every header's count still matches the lines beneath it.
        counted = {
            int(m) for m in re.findall(r"\((\d+)\)", "\n".join(blocks))
        }
        assert counted == {1, 2}

    def test_error_blocks_are_empty_when_nothing_is_wrong(self) -> None:
        assert _MOD.error_blocks([], [], [], []) == []

    def test_runtime_failures_get_their_own_counted_block(self) -> None:
        blocks = _MOD.error_blocks([], [], [], ["boom: exited 1"])
        assert (
            _sole_index(blocks, "RUNTIME FAILURES (1)")
            < _sole_index(blocks, "boom: exited 1")
        )

    def test_sentinel_errors_get_their_own_counted_block(self) -> None:
        """The derived sentinel rule reports under its own header, for the
        same reason the other three do: filed under `COVERAGE ERRORS (n)`
        its lines would be attributed to a count that excludes them.

        Positional, like the doc-error test above — presence plus counts
        is satisfied by a report that emits every header and then every
        line.
        """
        blocks = _MOD.error_blocks(
            ["one coverage problem"], ["one sentinel problem"], [], [],
        )
        assert (
            _sole_index(blocks, "COVERAGE ERRORS (1)")
            < _sole_index(blocks, "one coverage problem")
            < _sole_index(blocks, "SENTINEL COVERAGE (1)")
            < _sole_index(blocks, "one sentinel problem")
        )


# ---------------------------------------------------------------------------
# The TESTING.md cross-check
# ---------------------------------------------------------------------------


def _table(rows: list[tuple[str, str]]) -> str:
    body = "\n".join(
        f"| `{name}.vera` | some prose | {gate} |" for name, gate in rows
    )
    return (
        "### Example execution coverage\n\n"
        "| Example | Executed by | Harness gate |\n"
        "|---------|-------------|--------------|\n"
        f"{body}\n\n"
        "## Next section\n"
    )


class TestTestingMdCrossCheck:
    """docs must match the codebase."""

    def test_shipped_testing_md_matches_the_shipped_tables(self) -> None:
        text = (_ROOT / "TESTING.md").read_text(encoding="utf-8")
        assert _MOD.check_testing_md(text, _MOD.RUN_SPECS, _MOD.SKIPS) == []

    def test_matching_table_passes(self) -> None:
        doc = _table([("a", "runs"), ("b", "skip: network")])
        errors = _MOD.check_testing_md(
            doc, {"a": _MOD.RunSpec()}, {"b": "network"}
        )
        assert errors == []

    def test_missing_row_is_an_error(self) -> None:
        doc = _table([("a", "runs")])
        errors = _MOD.check_testing_md(
            doc, {"a": _MOD.RunSpec()}, {"b": "network"}
        )
        assert len(errors) == 1
        assert "b.vera" in errors[0]

    def test_extra_row_is_an_error(self) -> None:
        doc = _table([("a", "runs"), ("ghost", "runs")])
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        assert "ghost" in errors[0]

    def test_renamed_example_is_an_error_naming_both_sides(self) -> None:
        """The rename case: the doc still cites the old name and the script
        the new one, so the reader is told which is which rather than just
        that a count is off."""
        doc = _table([("old_name", "runs")])
        errors = _MOD.check_testing_md(doc, {"new_name": _MOD.RunSpec()}, {})
        joined = " ".join(errors)
        assert "old_name" in joined
        assert "new_name" in joined

    def test_wrong_gate_disposition_is_an_error(self) -> None:
        doc = _table([("a", "skip: network")])
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        assert "a.vera" in errors[0]

    def test_wrong_skip_property_is_an_error(self) -> None:
        """Same disposition, different property: documenting `http.vera` as
        skipped for the wrong reason is a lie the gate must catch."""
        doc = _table([("a", "skip: stdin")])
        errors = _MOD.check_testing_md(doc, {}, {"a": "network"})
        assert len(errors) == 1
        assert "network" in errors[0]

    def test_reworded_heading_is_an_error_not_a_silent_pass(self) -> None:
        """The convention this whole file turns on: if the anchor the check
        keys off is reworded away, the check must fail loudly rather than
        find nothing to compare and report success."""
        doc = (
            "### Some other heading entirely\n\n"
            "| Example | Executed by | Harness gate |\n"
            "|---------|-------------|--------------|\n"
            "| `a.vera` | prose | runs |\n"
        )
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        # The *missing-heading* diagnosis specifically.  Both this branch and
        # the empty-table one below name the heading, so asserting the
        # heading alone passes whichever fires — the coinciding-message trap.
        # `parse_testing_table` returns None here and an empty dict there,
        # and `None` is falsy, so a missing-heading case that fell through
        # would be reported as an empty table and read as a pass.
        assert "no heading containing" in errors[0]
        assert "Example execution coverage" in errors[0]

    def test_heading_present_but_table_empty_is_an_error(self) -> None:
        doc = (
            "### Example execution coverage\n\n"
            "The table went away in a refactor.\n\n"
            "## Next section\n"
        )
        errors = _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {})
        assert len(errors) == 1
        assert "no rows" in errors[0].lower()

    def test_a_fenced_hash_line_does_not_end_the_subsection(self) -> None:
        """`#` at column 0 inside a fence is a shell comment, not a
        heading.  TESTING.md carries 32 such lines today, none of them
        between this heading and its table — so the guard is not fixing
        a present breakage but removing a trap: adding an ordinary
        annotated code block above the table would otherwise empty it
        and fail the gate on a well-formed document.
        """
        doc = (
            "### Example execution coverage\n\n"
            "```bash\n"
            "# regenerate the table\n"
            "python scripts/check_examples_run.py\n"
            "```\n\n"
            "| Example | Executed by | Harness gate |\n"
            "|---------|-------------|--------------|\n"
            "| `a.vera` | prose | runs |\n\n"
            "## Next section\n"
        )
        assert _MOD.parse_testing_table(doc) == {"a": "runs"}
        assert _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {}) == []

    def test_an_unfenced_hash_line_still_ends_the_subsection(self) -> None:
        """The guard must not swallow real headings — the complement,
        without which fence-awareness could degenerate into never
        terminating."""
        doc = (
            "### Example execution coverage\n\n"
            "| `a.vera` | prose | runs |\n\n"
            "## Next section\n\n"
            "| `ghost.vera` | prose | runs |\n"
        )
        assert _MOD.parse_testing_table(doc) == {"a": "runs"}

    def test_the_shipped_document_parses_to_every_example(self) -> None:
        """End to end on the real file: the parse finds one row per
        example, so neither guard has quietly changed what it reads."""
        text = (_ROOT / "TESTING.md").read_text(encoding="utf-8")
        rows = _MOD.parse_testing_table(text)
        assert rows is not None
        assert set(rows) == set(_MOD.example_names(_ROOT / "examples"))

    def test_table_parse_stops_at_the_next_heading(self) -> None:
        """A row-shaped line in a later section must not be swept in as an
        example row — the parse is scoped to the subsection."""
        doc = _table([("a", "runs")]).replace(
            "## Next section\n",
            "## Next section\n\n| `ghost.vera` | x | runs |\n",
        )
        assert _MOD.check_testing_md(doc, {"a": _MOD.RunSpec()}, {}) == []
