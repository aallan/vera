"""Tests for scripts/mutate_diff.py, the mutation lane scoped to a diff.

The script maps a diff's changed lines to the functions mutmut mutates as
units, runs mutmut over exactly those functions in a scratch tree, and
reports a table, a JSON record and an exit code.  What is tested here is
everything around mutmut itself:

- the diff parse and the line-to-function mapping, over every shape a
  change can take (a method, a nested function, a decorator, a docstring or
  comment alone, a new file, a deleted function, code outside any function);
- the narrowing that keeps mutmut from generating mutants for the functions
  the diff leaves alone, and the rewrite of the scratch tree's
  ``[tool.mutmut]``;
- the parse of ``mutmut results --all true``, over every status mutmut 3
  prints, and the refusal of a line or a status it does not model;
- the exit code (0 when every mutant is killed or timed out, 1 on a
  survivor, 2 when the run stops short), the budget that stops it, and the
  whole run end to end against a stand-in engine;
- the workflow that runs it, read as data.

The tests that need mutmut itself (its status table, and its generator
reading the narrowing pragma) skip where the ``[mutation]`` extra is not
installed; the lane's workflow installs it and runs this file before the
script.
"""

from __future__ import annotations

import ast
import importlib.util
import json
import os
import re
import subprocess
import sys
import textwrap
import tomllib
from pathlib import Path
from typing import Any

import pytest
import yaml

ROOT = Path(__file__).resolve().parent.parent
_SCRIPT = ROOT / "scripts" / "mutate_diff.py"
WORKFLOW = ROOT / ".github" / "workflows" / "mutation-diff.yml"
SEP = "ǁ"  # mutmut's class separator in a method's mangled name


def _load() -> Any:
    spec = importlib.util.spec_from_file_location("mutate_diff", _SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules["mutate_diff"] = module
    spec.loader.exec_module(module)
    return module


md = _load()


def _src(text: str) -> str:
    return textwrap.dedent(text).lstrip("\n")


def _change(path: str, added: set[int], removed: set[int] | None = None,
            old: str | None = "same") -> Any:
    return md.FileChange(
        old_path=path if old == "same" else old,
        new_path=path,
        added=frozenset(added),
        removed=frozenset(removed or set()),
    )


def _line_of(source: str, needle: str) -> int:
    for number, line in enumerate(source.splitlines(), start=1):
        if needle in line:
            return number
    raise AssertionError(f"{needle!r} not in source")


def _changed_lines(base: str, head: str) -> set[int]:
    """Head lines that differ from base, by a line-for-line comparison of
    two sources of equal length (every fixture below edits in place)."""
    a, b = base.splitlines(), head.splitlines()
    assert len(a) == len(b), "fixture must edit in place"
    return {i for i, (x, y) in enumerate(zip(a, b), start=1) if x != y}


# ---------------------------------------------------------------------------
# The diff parse
# ---------------------------------------------------------------------------


DIFF = """\
diff --git a/vera/smt.py b/vera/smt.py
index 1111111..2222222 100644
--- a/vera/smt.py
+++ b/vera/smt.py
@@ -10 +10 @@ def a():
-    return 1
+    return 2
@@ -20,0 +21,3 @@ def b():
+    x = 1
+    y = 2
+    return x + y
@@ -40,2 +42,0 @@ def c():
-    dead = 1
-    gone = 2
diff --git a/vera/new.py b/vera/new.py
new file mode 100644
index 0000000..3333333
--- /dev/null
+++ b/vera/new.py
@@ -0,0 +1,2 @@
+def fresh():
+    return 0
diff --git a/vera/old.py b/vera/old.py
deleted file mode 100644
index 4444444..0000000
--- a/vera/old.py
+++ /dev/null
@@ -1,2 +0,0 @@
-def stale():
-    return 0
diff --git a/vera/before.py b/vera/after.py
similarity index 90%
rename from vera/before.py
rename to vera/after.py
index 5555555..6666666 100644
--- a/vera/before.py
+++ b/vera/after.py
@@ -3 +3 @@ def moved():
-    return 1
+    return 3
\\ No newline at end of file
diff --git a/vera/grammar.lark b/vera/grammar.lark
index 7777777..8888888 100644
--- a/vera/grammar.lark
+++ b/vera/grammar.lark
@@ -1 +1 @@
-start: a
+start: b
"""


class TestDiffParse:
    def _by_new(self) -> dict[str | None, Any]:
        return {c.new_path or c.old_path: c for c in md.parse_diff(DIFF)}

    def test_a_modified_line_is_added_at_its_head_number(self) -> None:
        smt = self._by_new()["vera/smt.py"]
        assert 10 in smt.added

    def test_an_added_block_is_every_line_of_it(self) -> None:
        smt = self._by_new()["vera/smt.py"]
        assert {21, 22, 23} <= smt.added

    def test_a_pure_deletion_removes_its_base_lines_and_adds_none(self) -> None:
        smt = self._by_new()["vera/smt.py"]
        assert smt.removed == frozenset({10, 40, 41})
        assert smt.added == frozenset({10, 21, 22, 23})

    def test_a_new_file_has_no_old_path(self) -> None:
        new = self._by_new()["vera/new.py"]
        assert new.old_path is None and new.added == frozenset({1, 2})

    def test_a_deleted_file_has_no_new_path(self) -> None:
        old = self._by_new()["vera/old.py"]
        assert old.new_path is None and old.added == frozenset()

    def test_an_empty_new_file_has_no_old_path(self) -> None:
        """An empty file's diff has no `---`/`+++` lines: the mode line says
        it is new, or the lane would look for it at the merge base."""
        (change,) = md.parse_diff(
            "diff --git a/vera/pkg/__init__.py b/vera/pkg/__init__.py\n"
            "new file mode 100644\nindex 0000000..e69de29\n")
        assert change.old_path is None and change.new_path == "vera/pkg/__init__.py"

    def test_an_empty_deleted_file_has_no_new_path(self) -> None:
        (change,) = md.parse_diff(
            "diff --git a/vera/pkg/__init__.py b/vera/pkg/__init__.py\n"
            "deleted file mode 100644\nindex e69de29..0000000\n")
        assert change.new_path is None and change.old_path == "vera/pkg/__init__.py"

    def test_a_rename_keeps_both_paths(self) -> None:
        after = self._by_new()["vera/after.py"]
        assert after.old_path == "vera/before.py" and after.added == frozenset({3})

    def test_only_python_files_are_kept(self) -> None:
        assert "vera/grammar.lark" not in self._by_new()

    def test_a_hunk_outside_any_file_section_is_refused(self) -> None:
        with pytest.raises(md.DiffError):
            md.parse_diff("@@ -1 +1 @@\n-a\n+b\n")


# ---------------------------------------------------------------------------
# The line-to-function mapping
# ---------------------------------------------------------------------------


BASE = _src('''
    """A module."""

    LIMIT = 3


    def top(x):
        """Top-level."""
        # a comment
        return x + 1


    def outer(x):
        def inner(y):
            return y * 2
        return inner(x)


    @functools.cache
    def cached(x):
        return x - 1


    async def waits(x):
        return x


    class Box:
        size = 1

        def method(self, x):
            """A method."""
            return x * self.size

        @staticmethod
        def static(x):
            return x + 2

        @classmethod
        def klass(cls, x):
            return x + 3

        @property
        def prop(self):
            return self.size

        def __new__(cls):
            return super().__new__(cls)

        def nested_holder(self):
            def helper(z):
                return z + 4
            return helper(1)

        class Inner:
            def deep(self):
                return 5


    def pragmad(x):  # pragma: no mutate block
        return x + 6


    def gone(x):
        return x + 7
''')


def _edit(old: str, new: str) -> str:
    assert BASE.count(old) == 1, old
    return BASE.replace(old, new)


# (description, the in-place edit, the units the diff changes, the units
# reported as excluded with their reason, whether any line is outside every
# unit, the units whose lines changed but whose code did not)
MAPPING_CASES = [
    ("method body", ("return x * self.size", "return x * self.size * 2"),
     {f"x{SEP}Box{SEP}method"}, {}, False, set()),
    ("top-level function body", ("return x + 1", "return x + 10"),
     {"x_top"}, {}, False, set()),
    ("nested function, attributed to its enclosing function",
     ("return y * 2", "return y * 3"), {"x_outer"}, {}, False, set()),
    ("nested function in a method", ("return z + 4", "return z + 40"),
     {f"x{SEP}Box{SEP}nested_holder"}, {}, False, set()),
    ("a decorator line", ("@functools.cache", "@functools.lru_cache"),
     {"x_cached"}, {"x_cached": "decorated"}, False, set()),
    ("a decorated function's body", ("return x - 1", "return x - 10"),
     {"x_cached"}, {"x_cached": "decorated"}, False, set()),
    ("a staticmethod is mutated", ("return x + 2", "return x + 20"),
     {f"x{SEP}Box{SEP}static"}, {}, False, set()),
    ("a classmethod is mutated", ("return x + 3", "return x + 30"),
     {f"x{SEP}Box{SEP}klass"}, {}, False, set()),
    ("a property is not", ("return self.size", "return self.size + 0"),
     {f"x{SEP}Box{SEP}prop"}, {f"x{SEP}Box{SEP}prop": "decorated"}, False, set()),
    ("a name mutmut never mutates", ("return super().__new__(cls)", "return object.__new__(cls)"),
     {f"x{SEP}Box{SEP}__new__"}, {f"x{SEP}Box{SEP}__new__": "never mutated"}, False, set()),
    ("an async function", ("return x\n", "return x + 0\n"), {"x_waits"}, {}, False, set()),
    ("a function under a pragma", ("return x + 6", "return x + 60"),
     {"x_pragmad"}, {"x_pragmad": "pragma"}, False, set()),
    ("a docstring alone", ('"""Top-level."""', '"""Top-level, reworded."""'),
     set(), {}, False, {"top"}),
    ("a comment alone", ("# a comment", "# another comment"), set(), {}, False, {"top"}),
    ("a method's docstring alone", ('"""A method."""', '"""A method, reworded."""'),
     set(), {}, False, {"Box.method"}),
    ("a module-level constant", ("LIMIT = 3", "LIMIT = 4"), set(), {}, True, set()),
    ("a class attribute", ("size = 1", "size = 2"), set(), {}, True, set()),
    ("a method of a nested class", ("return 5", "return 50"), set(), {}, True, set()),
]


class TestMapping:
    @pytest.mark.parametrize(
        "case", MAPPING_CASES, ids=[c[0] for c in MAPPING_CASES])
    def test_an_in_place_edit(self, case: tuple[Any, ...]) -> None:
        _, (old, new), changed, excluded, outside, unchanged = case
        head = _edit(old, new)
        verdict = md.classify(
            _change("vera/m.py", _changed_lines(BASE, head)), BASE, head)
        assert {u.key for u in verdict.changed} == changed
        assert {u.key: u.excluded for u in verdict.changed if u.excluded} == excluded
        assert bool(verdict.outside) is outside
        assert set(verdict.unchanged_code) == unchanged
        assert verdict.deleted == []

    def test_a_blank_or_comment_line_outside_every_function_is_not_counted(self) -> None:
        head = _edit("LIMIT = 3\n", "LIMIT = 3\n# a note\n\n")
        lines = {_line_of(head, "# a note"), _line_of(head, "# a note") + 1}
        verdict = md.classify(_change("vera/m.py", lines), BASE, head)
        assert verdict.outside == [] and verdict.changed == []

    def test_every_unit_mutmut_mutates_is_scanned(self) -> None:
        keys = set(md.scan_units(BASE))
        assert keys == {
            "x_top", "x_outer", "x_cached", "x_waits", "x_pragmad", "x_gone",
            f"x{SEP}Box{SEP}method", f"x{SEP}Box{SEP}static",
            f"x{SEP}Box{SEP}klass", f"x{SEP}Box{SEP}prop",
            f"x{SEP}Box{SEP}__new__", f"x{SEP}Box{SEP}nested_holder",
        }

    def test_a_unit_spans_its_decorators(self) -> None:
        unit = md.scan_units(BASE)["x_cached"]
        assert unit.start == _line_of(BASE, "@functools.cache")
        assert unit.end == _line_of(BASE, "return x - 1")

    def test_a_deleted_function_is_reported_and_not_mutated(self) -> None:
        head = BASE.replace("\n\ndef gone(x):\n    return x + 7\n", "\n")
        removed = {_line_of(BASE, "def gone(x):"), _line_of(BASE, "return x + 7")}
        verdict = md.classify(_change("vera/m.py", set(), removed), BASE, head)
        assert verdict.changed == []
        assert verdict.deleted == ["gone"]
        assert verdict.outside_removed == []

    def test_a_deletion_inside_a_function_changes_it(self) -> None:
        base = _src("""
            def f(x):
                if x:
                    return 1
                return 2
        """)
        head = _src("""
            def f(x):
                return 2
        """)
        verdict = md.classify(_change("vera/m.py", set(), {2, 3}), base, head)
        assert [u.key for u in verdict.changed] == ["x_f"]

    def test_removing_a_functions_last_statement_changes_it(self) -> None:
        """The removed lines sat at the function's end, so the head side has no
        line of the function to point at: the base side names it."""
        base = _src("""
            def f(x):
                a = 1
                return a


            def g():
                return 2
        """)
        head = _src("""
            def f(x):
                a = 1


            def g():
                return 2
        """)
        diff = "diff --git a/vera/m.py b/vera/m.py\n--- a/vera/m.py\n+++ b/vera/m.py\n@@ -3 +2,0 @@\n-    return a\n"
        (change,) = md.parse_diff(diff)
        verdict = md.classify(change, base, head)
        assert [u.key for u in verdict.changed] == ["x_f"]

    def test_a_deletion_between_functions_changes_neither(self) -> None:
        base = _src("""
            def f():
                return 1

            X = 1

            def g():
                return 2
        """)
        head = _src("""
            def f():
                return 1


            def g():
                return 2
        """)
        verdict = md.classify(_change("vera/m.py", set(), {4, 5}), base, head)
        assert verdict.changed == []
        assert verdict.outside_removed == [4]  # `X = 1`; the blank line is not code

    def test_a_new_file_changes_every_unit(self) -> None:
        verdict = md.classify(
            _change("vera/m.py", set(range(1, len(BASE.splitlines()) + 1)), old=None),
            None, BASE)
        assert {u.key for u in verdict.changed} == set(md.scan_units(BASE))

    def test_a_deleted_file_reports_every_function(self) -> None:
        change = md.FileChange(old_path="vera/m.py", new_path=None,
                               added=frozenset(), removed=frozenset({1, 2}))
        verdict = md.classify(change, BASE, None)
        assert verdict.changed == []
        assert "Box.method" in verdict.deleted and "top" in verdict.deleted

    def test_a_renamed_function_is_new(self) -> None:
        head = _edit("def top(x):", "def top2(x):")
        verdict = md.classify(
            _change("vera/m.py", _changed_lines(BASE, head)), BASE, head)
        assert [u.key for u in verdict.changed] == ["x_top2"]
        assert verdict.deleted == ["top"]


HELPERS = {"pipeline": "import vera.checker\n", "matrix_sample": "import random\n"}


class TestOracle:

    @pytest.mark.parametrize(("source", "reaches"), [
        ("import vera\n", True),
        ("from vera.smt import SmtContext\n", True),
        ("def f():\n    import vera.cli\n", True),
        ("from tests import pipeline\n", True),
        ("from tests.pipeline import verify\n", True),
        ("from . import pipeline\n", True),
        ("from tests import matrix_sample\n", False),
        ("import yaml, subprocess\n", False),
        ("import vera_tools\n", False),
    ])
    def test_reaches_the_compiler(self, source: str, reaches: bool) -> None:
        assert md.reaches_compiler(source, HELPERS) is reaches


class TestMutantNames:
    @pytest.mark.parametrize(("path", "module"), [
        ("vera/smt.py", "vera.smt"),
        ("vera/checker/core.py", "vera.checker.core"),
        ("vera/obligations/__init__.py", "vera.obligations"),
    ])
    def test_module_name(self, path: str, module: str) -> None:
        assert md.module_name(path) == module

    def test_glob_selects_one_function_and_not_its_prefix_twin(self) -> None:
        import fnmatch

        glob = md.mutant_glob("vera/smt.py", "x_translate")
        assert fnmatch.fnmatch("vera.smt.x_translate__mutmut_7", glob)
        assert not fnmatch.fnmatch("vera.smt.x_translate_call__mutmut_7", glob)

    def test_method_glob(self) -> None:
        glob = md.mutant_glob("vera/smt.py", f"x{SEP}SmtContext{SEP}reset")
        assert glob == f"vera.smt.x{SEP}SmtContext{SEP}reset__mutmut_*"

    def test_unit_of_a_mutant(self) -> None:
        name = f"vera.smt.x{SEP}SmtContext{SEP}reset__mutmut_12"
        assert md.unit_of_mutant(name) == ("vera.smt", f"x{SEP}SmtContext{SEP}reset")


# ---------------------------------------------------------------------------
# Narrowing the scratch tree
# ---------------------------------------------------------------------------


class TestNarrowing:
    def test_untouched_units_get_the_block_pragma_and_touched_ones_do_not(self) -> None:
        out = md.narrow(BASE, {"x_top", f"x{SEP}Box{SEP}method"})
        lines = out.splitlines()
        assert "no mutate block" not in lines[_line_of(BASE, "def top(") - 1]
        assert "no mutate block" not in lines[_line_of(BASE, "def method(") - 1]
        for needle in ("def outer(", "def cached(", "def static(", "def gone("):
            assert "# pragma: no mutate block" in lines[_line_of(BASE, needle) - 1], needle

    def test_narrowing_moves_no_line_and_no_node(self) -> None:
        out = md.narrow(BASE, {"x_top"})
        assert len(out.splitlines()) == len(BASE.splitlines())
        assert ast.dump(ast.parse(out)) == ast.dump(ast.parse(BASE))

    def test_an_existing_comment_is_kept_behind_the_pragma(self) -> None:
        src = _src("""
            def f(x):  # noqa: C901
                return x
        """)
        out = md.narrow(src, set())
        assert out.splitlines()[0].endswith("# pragma: no mutate block  # noqa: C901")

    def test_an_existing_block_pragma_is_left_alone(self) -> None:
        out = md.narrow(BASE, set())
        line = out.splitlines()[_line_of(BASE, "def pragmad(") - 1]
        assert line.count("no mutate") == 1

    def test_the_pragma_goes_on_the_line_that_ends_a_wide_header(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The header's colon is the first at bracket depth 0: an annotation,
        a dict default and a lambda each hold a colon inside the brackets."""
        src = _src("""
            def wide(
                x: int,
                y: dict[str, int] = {"a": 1},
                f=lambda z: z,
            ) -> int:  # noqa: B006
                return x + y["a"] + f(1)


            def kept(x):
                return x * 2
        """)
        out = md.narrow(src, {"x_kept"})
        lines = out.splitlines()
        assert lines[4] == ") -> int:  # pragma: no mutate block  # noqa: B006"
        assert [n for n, line in enumerate(lines) if "no mutate" in line] == [4]
        pytest.importorskip("mutmut")
        from mutmut.configuration import reset_config
        from mutmut.mutation.file_mutation import mutate_file_contents

        (tmp_path / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["."]\n', encoding="utf-8")
        monkeypatch.chdir(tmp_path)
        reset_config()
        try:
            names = mutate_file_contents("m.py", out).mutant_names
        finally:
            reset_config()
        assert names and {n.partition("__mutmut_")[0] for n in names} == {"x_kept"}

    def test_a_one_line_function_is_narrowed_too(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        pytest.importorskip("mutmut")
        from mutmut.configuration import reset_config
        from mutmut.mutation.file_mutation import mutate_file_contents

        src = _src("""
            def one(x): return x + 1


            def kept(x):
                return x * 2
        """)
        out = md.narrow(src, {"x_kept"})
        assert out.splitlines()[0] == "def one(x): return x + 1  # pragma: no mutate block"
        (tmp_path / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["."]\n', encoding="utf-8")
        monkeypatch.chdir(tmp_path)
        reset_config()
        try:
            names = mutate_file_contents("m.py", out).mutant_names
            assert {n.partition("__mutmut_")[0] for n in mutate_file_contents("m.py", src).mutant_names} == {
                "x_one", "x_kept"}
        finally:
            reset_config()
        assert names and {n.partition("__mutmut_")[0] for n in names} == {"x_kept"}

    def test_mutmut_generates_mutants_for_the_kept_units_only(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The narrowing's premise, against mutmut's own generator: a unit
        under the block pragma yields no mutant, and a kept unit yields the
        same mutants it yields in an unnarrowed file."""
        pytest.importorskip("mutmut")
        from mutmut.configuration import reset_config
        from mutmut.mutation.file_mutation import mutate_file_contents

        (tmp_path / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["."]\n', encoding="utf-8")
        monkeypatch.chdir(tmp_path)
        reset_config()
        try:
            # Two kept units hold a nested def, whose mutants are the kept
            # unit's own: the narrowing must not mark it.
            keep = {"x_top", "x_outer", f"x{SEP}Box{SEP}method", f"x{SEP}Box{SEP}static",
                    f"x{SEP}Box{SEP}nested_holder"}
            full = mutate_file_contents("m.py", BASE).mutant_names
            narrowed = mutate_file_contents("m.py", md.narrow(BASE, keep)).mutant_names
        finally:
            reset_config()
        assert narrowed
        assert {n.partition("__mutmut_")[0] for n in narrowed} == keep
        assert sorted(narrowed) == sorted(
            n for n in full if n.partition("__mutmut_")[0] in keep)


PYPROJECT = _src('''
    [project]
    name = "x"

    [tool.mutmut]
    # comment
    source_paths = ["vera/"]
    only_mutate = [
        "vera/verifier.py",
        "vera/smt.py",
    ]
    also_copy = ["examples/"]
    use_setproctitle = false
    pytest_add_cli_args = ["--timeout=300"]
    pytest_add_cli_args_test_selection = [
        "tests/test_a.py",
    ]

    [tool.mypy]
    strict = true
''')


class TestConfigRewrite:
    def test_only_mutate_and_the_selection_change_and_nothing_else(self) -> None:
        out = md.rewrite_config(
            PYPROJECT, only_mutate=["vera/checker/core.py"],
            extra_tests=["tests/test_b.py", "tests/test_a.py"])
        before = tomllib.loads(PYPROJECT)
        after = tomllib.loads(out)
        mutmut_before = dict(before["tool"]["mutmut"])
        mutmut_after = dict(after["tool"]["mutmut"])
        assert mutmut_after.pop("only_mutate") == ["vera/checker/core.py"]
        assert mutmut_after.pop("pytest_add_cli_args_test_selection") == [
            "tests/test_a.py", "tests/test_b.py"]
        del mutmut_before["only_mutate"], mutmut_before["pytest_add_cli_args_test_selection"]
        assert mutmut_after == mutmut_before
        assert after["tool"]["mypy"] == before["tool"]["mypy"]
        assert after["project"] == before["project"]

    def test_a_config_without_the_section_is_refused(self) -> None:
        with pytest.raises(md.ConfigError):
            md.rewrite_config("[project]\nname = 'x'\n", only_mutate=[], extra_tests=[])

    def test_the_repository_config_rewrites(self) -> None:
        text = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
        out = md.rewrite_config(text, only_mutate=["vera/smt.py"], extra_tests=[])
        assert tomllib.loads(out)["tool"]["mutmut"]["only_mutate"] == ["vera/smt.py"]


class TestTheRepositoryConfig:
    """What the lane relies on in `[tool.mutmut]`, measured at its base:
    the stats run executes the whole selection with `-x` inside mutmut's
    copy, so one test that cannot pass there stops every run."""

    def _cfg(self) -> dict[str, Any]:
        text = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
        return dict(tomllib.loads(text)["tool"]["mutmut"])

    def test_the_copy_holds_what_the_selected_tests_read(self) -> None:
        also = self._cfg()["also_copy"]
        assert "scripts/" in also and "AGENTS.md" in also

    def test_every_selected_file_exists(self) -> None:
        for path in self._cfg()["pytest_add_cli_args_test_selection"]:
            assert (ROOT / path).is_file(), path

    def test_the_tests_that_read_a_mutated_modules_text_are_deselected(self) -> None:
        """Inside mutmut's copy, ``inspect.getsourcefile(vera.verifier)`` is
        the generated file, every function's mutants inlined: these two read
        it and fail there with no mutant active."""
        deselected = {arg.removeprefix("--deselect=") for arg in self._cfg()["pytest_add_cli_args"]
                      if arg.startswith("--deselect=")}
        reads = "tests/test_verifier_refinements.py::TestANonVerdictIsAttributedToTheRightOutcome::"
        assert deselected == {
            reads + "test_no_demotion_site_hardcodes_a_solver_reason",
            reads + "test_every_possibly_unguarded_demotion_supplies_a_reason",
        }

    def test_every_deselected_test_exists(self) -> None:
        args = [a for a in self._cfg()["pytest_add_cli_args"] if a.startswith("--deselect=")]
        assert args
        for arg in args:
            path, _, rest = arg.removeprefix("--deselect=").partition("::")
            assert (ROOT / path).is_file(), arg
            cls, _, name = rest.partition("::")
            text = (ROOT / path).read_text(encoding="utf-8")
            assert f"class {cls}" in text and f"def {name}(" in text, arg


# ---------------------------------------------------------------------------
# mutmut's results
# ---------------------------------------------------------------------------


M = f"vera.smt.x{SEP}SmtContext{SEP}reset__mutmut_"
F = "vera.smt.x_free__mutmut_"

#: `mutmut results --all true` as mutmut 3 prints it: four spaces, the
#: mutant's name, a colon, its status; one line for every status there is.
RESULTS = "\n".join([
    f"    {M}1: killed",
    f"    {M}2: survived",
    f"    {M}3: timeout",
    f"    {M}4: no tests",
    f"    {M}5: not checked",
    f"    {M}6: skipped",
    f"    {M}7: suspicious",
    f"    {M}8: caught by type check",
    f"    {M}9: check was interrupted by user",
    f"    {M}10: segfault",
    f"    {F}1: killed",
    "",
])


class TestResults:
    def test_every_status_mutmut_prints_parses(self) -> None:
        got = md.parse_results(RESULTS)
        assert got[f"{M}1"] == "killed"
        assert got[f"{M}9"] == "check was interrupted by user"
        assert len(got) == 11

    def test_the_statuses_are_every_status_mutmut_3_has(self) -> None:
        assert set(md.STATUSES) == {
            "killed", "survived", "timeout", "no tests", "not checked",
            "skipped", "suspicious", "caught by type check",
            "check was interrupted by user", "segfault",
        }

    def test_the_statuses_match_the_installed_engine(self) -> None:
        pytest.importorskip("mutmut")
        from mutmut.stats import status_by_exit_code

        engine = set(status_by_exit_code.values()) | {status_by_exit_code.default_factory()}
        assert engine == set(md.STATUSES)

    def test_a_status_it_does_not_model_is_refused(self) -> None:
        with pytest.raises(md.ResultsError, match="exploded"):
            md.parse_results(f"    {M}1: exploded\n")

    def test_a_line_it_cannot_parse_is_refused(self) -> None:
        with pytest.raises(md.ResultsError):
            md.parse_results("Some banner mutmut started printing\n")

    def test_a_mutant_listed_twice_is_refused(self) -> None:
        with pytest.raises(md.ResultsError):
            md.parse_results(f"    {M}1: killed\n    {M}1: survived\n")


def _unit(key: str, path: str = "vera/smt.py", excluded: str | None = None) -> Any:
    return md.Unit(key=key, qualname=key, path=path, start=1, end=2,
                   code="", excluded=excluded)


class TestTally:
    def test_results_are_counted_against_their_own_unit(self) -> None:
        units = [_unit(f"x{SEP}SmtContext{SEP}reset"), _unit("x_free")]
        rows = md.tally(units, md.parse_results(RESULTS))
        reset, free = rows
        assert reset.mutants == 10 and free.mutants == 1
        assert reset.counts["survived"] == 1 and free.counts == {"killed": 1}
        assert reset.survivors == [f"{M}2"]

    def test_a_unit_with_only_no_test_mutants_is_not_observable(self) -> None:
        units = [_unit("x_free")]
        rows = md.tally(units, {f"{F}1": "no tests", f"{F}2": "no tests"})
        assert rows[0].observable is False

    def test_a_result_outside_every_unit_is_counted_apart(self) -> None:
        rows = md.tally([_unit("x_free")], {f"{F}1": "killed", "vera.smt.x_other__mutmut_1": "survived"})
        assert [r.key for r in rows] == ["x_free"]
        assert rows[0].counts == {"killed": 1}
        assert md.outside_units([_unit("x_free")], {"vera.smt.x_other__mutmut_1": "survived"}) == [
            "vera.smt.x_other__mutmut_1"]


# (description, statuses over the diff's mutants, whether the engine
# stopped short, the exit code)
DECISIONS = [
    ("every mutant killed", ["killed", "killed"], None, 0),
    ("killed and timed out", ["killed", "timeout"], None, 0),
    ("caught by the type checker", ["caught by type check"], None, 0),
    ("one survivor", ["killed", "survived"], None, 1),
    ("not observable in process", ["no tests", "no tests"], None, 0),
    ("skipped by the engine", ["skipped", "killed"], None, 0),
    ("a mutant never run", ["killed", "not checked"], None, 2),
    ("an interrupted mutant", ["check was interrupted by user"], None, 2),
    ("a suspicious exit", ["suspicious"], None, 2),
    ("a killed process", ["segfault"], None, 2),
    ("a survivor in a run cut short", ["survived", "not checked"], None, 2),
    ("the budget stopped it", ["killed"], "budget", 2),
    ("the engine stopped it", [], "engine", 2),
    ("nothing to mutate", [], None, 0),
]


class TestExitCode:
    @pytest.mark.parametrize("case", DECISIONS, ids=[c[0] for c in DECISIONS])
    def test_exit_code(self, case: tuple[Any, ...]) -> None:
        _, statuses, stopped, code = case
        results = {f"{F}{i}": s for i, s in enumerate(statuses, start=1)}
        rows = md.tally([_unit("x_free")], results) if statuses else []
        assert md.exit_code(rows, stopped=stopped) == code


# ---------------------------------------------------------------------------
# The engine and its budget
# ---------------------------------------------------------------------------


class TestBudget:
    def test_a_run_inside_its_budget_finishes(self, tmp_path: Path) -> None:
        run = md.run_engine([sys.executable, "-c", "print('done')"], cwd=tmp_path,
                            budget_s=60, log_path=tmp_path / "log")
        assert run.returncode == 0 and run.stopped is None
        assert "done" in (tmp_path / "log").read_text(encoding="utf-8")

    def test_the_budget_stops_a_run_that_overruns_it(self, tmp_path: Path) -> None:
        run = md.run_engine([sys.executable, "-c", "import time; time.sleep(60)"],
                            cwd=tmp_path, budget_s=1, log_path=tmp_path / "log",
                            grace_s=(5, 5))
        assert run.stopped == "budget"
        assert run.elapsed_s < 30

    # Each step of the escalation is pinned by the signal that ends the child,
    # and the child says "ready" once its handlers are in place: a budget
    # shorter than its start-up would test the interrupt instead.
    _IGNORING = ("import signal, time; {ignore}; print('ready', flush=True); time.sleep(60)")

    @pytest.mark.skipif(os.name != "posix", reason="the escalation from an interrupt is POSIX's; "
                        "elsewhere the run is terminated at once")
    def test_a_run_that_ignores_the_interrupt_is_terminated(self, tmp_path: Path) -> None:
        import signal

        code = self._IGNORING.format(ignore="signal.signal(signal.SIGINT, signal.SIG_IGN)")
        run = md.run_engine([sys.executable, "-c", code], cwd=tmp_path, budget_s=3,
                            log_path=tmp_path / "log", grace_s=(1, 20))
        assert run.stopped == "budget"
        assert "ready" in (tmp_path / "log").read_text(encoding="utf-8")
        assert run.returncode == -signal.SIGTERM
        assert run.elapsed_s < 20

    @pytest.mark.skipif(os.name != "posix", reason="the escalation from an interrupt is POSIX's; "
                        "elsewhere the run is terminated at once")
    def test_a_run_that_ignores_the_terminate_too_is_killed(self, tmp_path: Path) -> None:
        import signal

        code = self._IGNORING.format(
            ignore="signal.signal(signal.SIGINT, signal.SIG_IGN); signal.signal(signal.SIGTERM, signal.SIG_IGN)")
        run = md.run_engine([sys.executable, "-c", code], cwd=tmp_path, budget_s=3,
                            log_path=tmp_path / "log", grace_s=(1, 1))
        assert run.stopped == "budget"
        assert "ready" in (tmp_path / "log").read_text(encoding="utf-8")
        assert run.returncode == -signal.SIGKILL
        assert run.elapsed_s < 20


    @pytest.mark.skipif(os.name != "posix", reason="process groups are POSIX's")
    def test_a_straggler_in_the_engines_group_is_ended_too(self, tmp_path: Path) -> None:
        """The interrupt ends the engine itself; a process it started (a test's
        subprocess, say) is still in its group, and the run ends that too."""
        import time

        code = ("import subprocess, sys, time; "
                "c = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
                "print('child', c.pid, flush=True); time.sleep(60)")
        run = md.run_engine([sys.executable, "-c", code], cwd=tmp_path, budget_s=3,
                            log_path=tmp_path / "log", grace_s=(5, 5))
        assert run.stopped == "budget"
        match = re.search(r"child (\d+)", (tmp_path / "log").read_text(encoding="utf-8"))
        assert match is not None
        pid = int(match.group(1))
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            time.sleep(0.2)
        else:
            os.kill(pid, 9)  # the test's own straggler, before it fails
            raise AssertionError(f"the engine's child {pid} outlived the run")


# ---------------------------------------------------------------------------
# End to end, against a stand-in engine
# ---------------------------------------------------------------------------


FAKE_ENGINE = '''
import json, os, sys
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
args = sys.argv[1:]
log = state / "calls.jsonl"
with log.open("a", encoding="utf-8") as fh:
    fh.write(json.dumps({"cwd": os.getcwd(), "args": args,
                         "git_dir": os.environ.get("GIT_DIR")}) + "\\n")
if args[0] == "run":
    print(os.environ.get("FAKE_RUN_OUTPUT", ""))
    sys.exit(int(os.environ.get("FAKE_RUN_EXIT", "0")))
if args[0] == "results":
    import time
    time.sleep(float(os.environ.get("FAKE_RESULTS_SLEEP", "0")))
    sys.stdout.write((state / "results.txt").read_text(encoding="utf-8"))
    sys.exit(0)
if args[0] == "show":
    print("# " + args[1] + ": survived")
    print("--- vera/m.py")
    print("+++ vera/m.py")
    print("@@ -1,2 +1,2 @@")
    print("-    return x + 1")
    print("+    return x - 1")
    sys.exit(0)
sys.exit(9)
'''


def _git(repo: Path, *args: str) -> str:
    env = {k: v for k, v in os.environ.items()
           if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE")}
    env.update(GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid",
               GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@example.invalid")
    return subprocess.run(["git", "-C", str(repo), *args], check=True, env=env,
                          capture_output=True, text=True, encoding="utf-8").stdout


@pytest.fixture
def repo(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    (root / "vera").mkdir(parents=True)
    (root / "tests").mkdir()
    (root / "pyproject.toml").write_text(_src('''
        [tool.mutmut]
        source_paths = ["vera/"]
        only_mutate = ["vera/smt.py"]
        pytest_add_cli_args_test_selection = ["tests/test_old.py"]
    '''), encoding="utf-8")
    (root / "vera" / "__init__.py").write_text("", encoding="utf-8")
    (root / "vera" / "m.py").write_text(_src("""
        def kept(x):
            return x + 1


        def other(x):
            return x * 2
    """), encoding="utf-8")
    (root / "tests" / "test_old.py").write_text("def test_x():\n    pass\n", encoding="utf-8")
    _git(root, "init", "-q", "-b", "main")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "base")
    (root / "vera" / "m.py").write_text(_src("""
        def kept(x):
            return x + 2


        def other(x):
            return x * 2
    """), encoding="utf-8")
    # The pull request's own test files: two that reach the compiler (one
    # directly, one through a helper), one tooling test, one of a family
    # the selection leaves out on purpose.
    (root / "tests" / "test_new.py").write_text(
        "import vera\n\ndef test_y():\n    pass\n", encoding="utf-8")
    (root / "tests" / "drive.py").write_text("import vera.m\n", encoding="utf-8")
    (root / "tests" / "test_via_helper.py").write_text(
        "from tests import drive\n\ndef test_z():\n    pass\n", encoding="utf-8")
    (root / "tests" / "test_tooling.py").write_text(
        "import yaml\n\ndef test_w():\n    pass\n", encoding="utf-8")
    (root / "tests" / "test_cli_new.py").write_text(
        "import vera\n\ndef test_v():\n    pass\n", encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-q", "-m", "head")
    return root


def _main(repo: Path, tmp_path: Path, results: str, run_exit: int = 0,
          run_output: str = "") -> tuple[int, dict[str, Any], list[dict[str, Any]]]:
    state = tmp_path / "state"
    state.mkdir(exist_ok=True)
    (state / "results.txt").write_text(results, encoding="utf-8")
    engine = tmp_path / "fake_mutmut.py"
    engine.write_text(FAKE_ENGINE, encoding="utf-8")
    out_json = tmp_path / "out.json"
    os.environ["FAKE_STATE"] = str(state)
    os.environ["FAKE_RUN_EXIT"] = str(run_exit)
    os.environ["FAKE_RUN_OUTPUT"] = run_output
    try:
        code = md.main([
            "--repo", str(repo), "--base", "HEAD~1", "--head", "HEAD",
            "--workdir", str(tmp_path / "work"), "--json", str(out_json),
            "--summary", str(tmp_path / "summary.md"),
            "--engine", sys.executable, str(engine),
        ])
    finally:
        del os.environ["FAKE_STATE"], os.environ["FAKE_RUN_EXIT"], os.environ["FAKE_RUN_OUTPUT"]
    calls = [json.loads(line) for line in
             (state / "calls.jsonl").read_text(encoding="utf-8").splitlines()]
    return code, json.loads(out_json.read_text(encoding="utf-8")), calls


class TestEndToEnd:
    @pytest.fixture(autouse=True)
    def _no_git_locators(self, monkeypatch: pytest.MonkeyPatch) -> None:
        for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR"):
            monkeypatch.delenv(name, raising=False)

    def test_the_repo_argument_wins_over_a_git_hooks_variables(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Inside a git hook GIT_DIR names the repository being committed;
        the lane reads --repo all the same."""
        other = tmp_path / "other"
        other.mkdir()
        _git(other, "init", "-q")
        monkeypatch.setenv("GIT_DIR", str(other / ".git"))
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0
        assert [f["qualname"] for f in record["functions"]] == ["kept"]
        assert calls and all(c["git_dir"] is None for c in calls)

    def test_a_survivor_fails_the_run_and_is_shown(self, repo: Path, tmp_path: Path) -> None:
        results = "    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: survived\n"
        code, record, calls = _main(repo, tmp_path, results)
        assert code == 1
        assert record["exit_code"] == 1
        (unit,) = record["functions"]
        assert unit["path"] == "vera/m.py" and unit["qualname"] == "kept"
        assert unit["counts"] == {"killed": 1, "survived": 1}
        assert unit["survivors"][0]["name"] == "vera.m.x_kept__mutmut_2"
        assert "-    return x + 1" in unit["survivors"][0]["diff"]

    def test_the_engine_runs_the_diffs_functions_in_the_scratch_tree(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0
        run = next(c for c in calls if c["args"][0] == "run")
        assert run["args"][-1] == "vera.m.x_kept__mutmut_*"
        tree = Path(run["cwd"]).resolve()
        assert tree.is_relative_to((tmp_path / "work").resolve())
        cfg = tomllib.loads((tree / "pyproject.toml").read_text(encoding="utf-8"))["tool"]["mutmut"]
        assert cfg["only_mutate"] == ["vera/m.py"]
        assert cfg["pytest_add_cli_args_test_selection"] == [
            "tests/test_old.py", "tests/test_new.py", "tests/test_via_helper.py"]
        assert record["extra_tests"] == ["tests/test_new.py", "tests/test_via_helper.py"]
        assert record["tests_left_out"] == ["tests/test_cli_new.py", "tests/test_tooling.py"]
        narrowed = (tree / "vera" / "m.py").read_text(encoding="utf-8")
        assert "def other(x):  # pragma: no mutate block" in narrowed
        assert "def kept(x):\n" in narrowed
        # the repository itself is untouched
        assert "no mutate" not in (repo / "vera" / "m.py").read_text(encoding="utf-8")

    def test_the_summary_is_the_table(self, repo: Path, tmp_path: Path) -> None:
        results = "    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: survived\n"
        _main(repo, tmp_path, results)
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert "| `vera/m.py` `kept` | 2 | 1 | 0 | 1 |" in summary
        assert "`vera.m.x_kept__mutmut_2`" in summary and "+    return x - 1" in summary

    def test_no_in_process_test_for_any_mutant_is_not_observable_and_passes(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        """mutmut stops with exit 1 when no selected test reaches any
        mutated function; every mutant of the diff is then not observable
        in process, which is reported and does not fail the run."""
        code, record, _ = _main(
            repo, tmp_path, "    vera.m.x_kept__mutmut_1: not checked\n", run_exit=1,
            run_output="Stopping early, because we could not find any test case for any mutant.")
        assert code == 0 and record["stopped"] is None
        (unit,) = record["functions"]
        assert unit["counts"] == {"no tests": 1} and unit["observable"] is False

    def test_a_mutant_the_lane_cannot_place_stops_the_run_short(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        """In the narrowed tree every mutant mutmut reports belongs to a
        changed function; one that does not (here a survivor of `other`,
        which the diff leaves alone) means the mapping or the narrowing went
        wrong, so the diff is not decided, whatever the table shows."""
        results = "    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_other__mutmut_1: survived\n"
        code, record, _ = _main(repo, tmp_path, results)
        assert code == 2 and record["stopped"] == "unmapped"
        assert record["outside_diff"] == ["vera.m.x_other__mutmut_1"]
        (unit,) = record["functions"]
        assert unit["counts"] == {"killed": 1}

    def test_a_hung_results_call_stops_the_run_short(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        monkeypatch.setattr(md, "ENGINE_CALL_TIMEOUT_S", 1)
        monkeypatch.setenv("FAKE_RESULTS_SLEEP", "30")
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 2 and record["stopped"] == "engine"
        assert record["elapsed_s"] < 20

    def test_the_summary_shows_a_bounded_number_of_survivors(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A step summary over 1 MiB is dropped whole, so the summary shows at
        most MAX_SHOWN_SURVIVORS diffs; the record lists every survivor."""
        monkeypatch.setattr(md, "MAX_SHOWN_SURVIVORS", 3)
        results = "".join(f"    vera.m.x_kept__mutmut_{i}: survived\n" for i in range(1, 6))
        code, record, calls = _main(repo, tmp_path, results)
        assert code == 1
        (unit,) = record["functions"]
        assert [s["name"] for s in unit["survivors"]] == [f"vera.m.x_kept__mutmut_{i}" for i in range(1, 6)]
        assert [bool(s["diff"]) for s in unit["survivors"]] == [True, True, True, False, False]
        assert len([c for c in calls if c["args"][0] == "show"]) == 3
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert summary.count("```diff") == 3
        assert "2 more survivors" in summary

    def test_an_engine_failure_stops_the_run_short(self, repo: Path, tmp_path: Path) -> None:
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: not checked\n",
                                run_exit=1)
        assert code == 2 and record["stopped"] == "engine"

    def test_a_diff_with_nothing_to_mutate_passes_without_the_engine(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        # A comment inside a function changes its lines and not its code.
        (repo / "vera" / "m.py").write_text(
            (repo / "vera" / "m.py").read_text(encoding="utf-8").replace(
                "def kept(x):\n", "def kept(x):\n    # why\n", 1), encoding="utf-8")
        (repo / "README.md").write_text("docs\n", encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "docs")
        state = tmp_path / "state"
        state.mkdir()
        (state / "results.txt").write_text("", encoding="utf-8")
        engine = tmp_path / "fake_mutmut.py"
        engine.write_text(FAKE_ENGINE, encoding="utf-8")
        out_json = tmp_path / "out.json"
        os.environ["FAKE_STATE"] = str(state)
        try:
            code = md.main(["--repo", str(repo), "--base", "HEAD~1", "--head", "HEAD",
                            "--workdir", str(tmp_path / "work"), "--json", str(out_json),
                            "--engine", sys.executable, str(engine)])
        finally:
            del os.environ["FAKE_STATE"]
        assert code == 0
        assert json.loads(out_json.read_text(encoding="utf-8"))["functions"] == []
        assert not (state / "calls.jsonl").exists()

    def test_a_failure_of_the_lane_itself_stops_the_run_short(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        """Exit 1 means a survivor, so a lane that fails (here, a base git
        cannot resolve) exits 2 and says why, in the record and the summary."""
        out_json = tmp_path / "out.json"
        code = md.main(["--repo", str(repo), "--base", "no-such-ref", "--head", "HEAD",
                        "--workdir", str(tmp_path / "work"), "--json", str(out_json),
                        "--summary", str(tmp_path / "summary.md")])
        assert code == 2
        record = json.loads(out_json.read_text(encoding="utf-8"))
        assert record["exit_code"] == 2 and record["stopped"] == "lane"
        assert "no-such-ref" in record["error"]
        assert "no-such-ref" in (tmp_path / "summary.md").read_text(encoding="utf-8")

    def test_a_non_empty_workdir_is_refused(self, repo: Path, tmp_path: Path) -> None:
        work = tmp_path / "work"
        work.mkdir()
        (work / "stale").write_text("x", encoding="utf-8")
        with pytest.raises(SystemExit):
            md.main(["--repo", str(repo), "--base", "HEAD~1", "--head", "HEAD",
                     "--workdir", str(work)])


# ---------------------------------------------------------------------------
# The workflow, read as data
# ---------------------------------------------------------------------------


class TestWorkflow:
    def _wf(self) -> dict[Any, Any]:
        data = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
        assert isinstance(data, dict)
        return data

    def _job(self) -> dict[str, Any]:
        (job,) = self._wf()["jobs"].values()
        return job

    def test_it_runs_on_a_pull_request_that_changes_the_compiler_or_the_lane(self) -> None:
        on = self._wf()[True]  # YAML 1.1 reads the bare key `on` as True
        assert set(on) == {"pull_request"}
        assert on["pull_request"]["paths"] == [
            "vera/**/*.py", "scripts/mutate_diff.py", "tests/test_mutate_diff.py",
            ".github/workflows/mutation-diff.yml"]

    def test_it_reads_the_repository_and_nothing_more(self) -> None:
        assert self._wf()["permissions"] == {"contents": "read"}
        assert self._job()["permissions"] == {"contents": "read"}
        text = WORKFLOW.read_text(encoding="utf-8")
        assert not re.search(r"\$\{\{[^}]*\b(secrets\b|github\.token\b)", text)

    def test_checkout_keeps_no_credentials_and_fetches_the_merge_base(self) -> None:
        (checkout,) = [s for s in self._job()["steps"]
                       if str(s.get("uses", "")).startswith("actions/checkout@")]
        assert checkout["with"]["persist-credentials"] is False
        assert checkout["with"]["fetch-depth"] == 0
        assert checkout["with"]["ref"] == "${{ github.event.pull_request.head.sha }}"

    def test_every_action_is_pinned_as_the_other_workflows_pin_it(self) -> None:
        pins: dict[str, set[str]] = {}
        for path in sorted((ROOT / ".github" / "workflows").glob("*.yml")):
            if path == WORKFLOW:
                continue
            for ref in re.findall(r"uses:\s*([\w./-]+@\S+)", path.read_text(encoding="utf-8")):
                name, _, pin = ref.partition("@")
                pins.setdefault(name, set()).add(pin)
        for step in self._job()["steps"]:
            if "uses" in step:
                name, _, pin = step["uses"].partition("@")
                assert pin in pins.get(name, set()), step["uses"]

    def test_it_runs_python_312_and_the_mutation_extra(self) -> None:
        steps = self._job()["steps"]
        (setup,) = [s for s in steps if str(s.get("uses", "")).startswith("actions/setup-python@")]
        assert setup["with"]["python-version"] == "3.12"
        runs = [s.get("run", "") for s in steps]
        assert any('pip install -e ".[mutation]"' in r for r in runs)
        assert any("pytest tests/test_mutate_diff.py" in r for r in runs)

    def test_the_script_runs_against_the_merge_base_inside_its_budget(self) -> None:
        job = self._job()
        (step,) = [s for s in job["steps"] if "scripts/mutate_diff.py" in s.get("run", "")]
        assert "${{" not in step["run"], "context values reach the shell through env only"
        assert step["env"]["BASE_SHA"] == "${{ github.event.pull_request.base.sha }}"
        assert step["env"]["HEAD_SHA"] == "${{ github.event.pull_request.head.sha }}"
        budget = int(re.search(r"--budget (\d+)", step["run"]).group(1))  # type: ignore[union-attr]
        assert job["timeout-minutes"] * 60 >= budget + 10 * 60
        assert "continue-on-error" not in job and "continue-on-error" not in step

    def test_the_record_is_kept_and_summarised_whatever_the_outcome(self) -> None:
        steps = self._job()["steps"]
        (upload,) = [s for s in steps if str(s.get("uses", "")).startswith("actions/upload-artifact@")]
        assert upload["if"] == "always()"
        (step,) = [s for s in steps if "scripts/mutate_diff.py" in s.get("run", "")]
        assert "--summary \"$GITHUB_STEP_SUMMARY\"" in step["run"]

    def test_a_newer_push_cancels_the_run_for_the_same_pull_request(self) -> None:
        concurrency = self._wf()["concurrency"]
        assert "github.event.pull_request.number" in concurrency["group"]
        assert concurrency["cancel-in-progress"] is True
