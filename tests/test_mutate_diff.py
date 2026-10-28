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
- what stopped mutmut's stats pass or clean run, read off its log: a test
  that fails in the copy, which the lane drops, or an exception of the
  engine's own code, which the lane names, over the engine's own logs;
- the exit code (1 on a survivor, 2 when the engine or the lane itself
  fails, and 0 otherwise: a run its budget stops with no survivor passes,
  its headline and a warning annotation saying it is incomplete), the
  budget that stops it, and the whole run end to end against a stand-in
  engine;
- the workflow that runs it, read as data.

The tests that need mutmut itself (its status table, and its generator
reading the narrowing pragma) skip where the ``[mutation]`` extra is not
installed; both mutation lanes install it from ``uv.lock`` and run this file
before their scripts.
"""

from __future__ import annotations

import ast
import importlib.util
import io
import json
import os
import re
import subprocess
import sys
import textwrap
import tomllib
import types
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

    def test_a_pure_deletion_records_the_head_line_it_follows(self) -> None:
        """`@@ -40,2 +42,0 @@` removes two lines after head line 42 and adds
        none, so no added line marks the place; the window reads it here."""
        assert self._by_new()["vera/smt.py"].deleted_after == frozenset({42})
        assert self._by_new()["vera/after.py"].deleted_after == frozenset()


# ---------------------------------------------------------------------------
# The window: the lines whose mutants the lane keeps
# ---------------------------------------------------------------------------


class TestTheWindow:
    """Within two lines of a line the diff adds, or of a point where it
    removes lines and adds none.  mutmut places a mutant on the line its
    node starts on, and generates only those the window keeps."""

    def test_an_added_line_keeps_two_lines_either_side(self) -> None:
        assert md.window(_change("vera/m.py", {10})) == frozenset(range(8, 13))

    def test_an_added_block_keeps_two_lines_beyond_each_end(self) -> None:
        assert md.window(_change("vera/m.py", {21, 22, 23})) == frozenset(range(19, 26))

    def test_a_pure_deletion_keeps_two_lines_either_side_of_its_point(self) -> None:
        change = md.FileChange(old_path="vera/m.py", new_path="vera/m.py", added=frozenset(),
                               removed=frozenset({40, 41}), deleted_after=frozenset({42}))
        assert md.window(change) == frozenset({41, 42, 43, 44})

    def test_two_changes_close_together_make_one_window(self) -> None:
        assert md.window(_change("vera/m.py", {4, 9})) == frozenset(range(2, 12))

    def test_the_window_starts_at_the_first_line(self) -> None:
        assert md.window(_change("vera/m.py", {1})) == frozenset({1, 2, 3})

    @pytest.mark.parametrize("context", [0, 1, 5])
    def test_the_context_is_the_lines_kept_either_side(self, context: int) -> None:
        assert md.window(_change("vera/m.py", {50}), context) == frozenset(
            range(50 - context, 51 + context))

    @pytest.mark.parametrize("value", ["-1", "two"])
    def test_the_context_is_a_whole_number_of_lines(
        self, value: str, capsys: pytest.CaptureFixture[str],
    ) -> None:
        with pytest.raises(SystemExit):
            md.main(["--context", value])
        assert "argument --context:" in capsys.readouterr().err

    def test_the_rule_names_its_context(self) -> None:
        assert md.rule(2) == ("the mutants whose node starts within 2 lines of a line the diff "
                              "adds or of a point where it removes lines, or on the first line "
                              "of a call, match, assignment, operation, comparison, conditional "
                              "expression or lambda that spans one of those lines")
        assert "within 1 line of" in md.rule(1)

    @pytest.mark.parametrize(("span", "joins"), [
        ((3, 9), True),      # holds the window's first lines
        ((1, 8), True),      # ends on its first line
        ((12, 20), True),    # starts on its last line
        ((9, 10), True),     # lies inside it
        ((1, 7), False),     # ends above it
        ((13, 20), False),   # starts below it
    ])
    def test_a_span_that_holds_a_window_line_adds_its_first_line(
        self, span: tuple[int, int], joins: bool,
    ) -> None:
        """mutmut places the mutants of a call, a match and the other
        enclosing kinds on the node's first line, so a node whose lines meet
        the window's (8 to 12) adds that line, and one that misses them adds
        nothing."""
        assert md.first_lines([span], range(8, 13)) == (frozenset({span[0]}) if joins
                                                        else frozenset())

    def test_a_span_between_two_window_lines_adds_nothing(self) -> None:
        assert md.first_lines([(5, 8), (4, 4), (2, 9)], [4, 9]) == frozenset({4, 2})


#: A unit of seven lines, the one the window test edits at line 4.
WINDOWED = _src("""
    def long(x):
        a = x + 1
        b = a * 2
        c = b - 3
        d = c // 4
        e = d % 5
        return a + b + c + d + e


    def other(x):
        return x * 2
""")


def _window_file(where: Path, lines: dict[str, list[int]], context: int = 0) -> tuple[Path, Path]:
    window_file, record = where / "window.json", where / "window-counts.json"
    window_file.write_text(json.dumps({"context": context, "record": str(record), "lines": lines}),
                           encoding="utf-8")
    return window_file, record


class TestTheWindowInTheEngine:
    """The window reaches mutmut's own generator through its covered-lines
    hook, and an engine without that hook stops before it generates."""

    def test_mutmuts_generation_makes_the_windows_mutants_alone(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """With the window installed, mutmut's own generation of a file (the
        call its pool makes for each file) makes the mutants whose node
        starts on a kept line, exactly those its visitor gives for that
        line, and the counts written are the unit's mutants on every line
        and in the window."""
        pytest.importorskip("mutmut")
        import mutmut.__main__ as engine
        from mutmut.configuration import reset_config
        from mutmut.mutation.file_mutation import mutate_file_contents

        (tmp_path / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["."]\n', encoding="utf-8")
        narrowed = md.narrow(WINDOWED, {"x_long"})
        (tmp_path / "m.py").write_text(narrowed, encoding="utf-8")
        window_file, record = _window_file(tmp_path, {"m.py": [4]})
        monkeypatch.chdir(tmp_path)
        monkeypatch.setattr(engine, "get_covered_lines_for_file", engine.get_covered_lines_for_file)
        reset_config()
        try:
            md.install_window(engine, window_file)
            generated = engine.write_all_mutants_to_file(
                out=io.StringIO(), source=narrowed, filename=Path("m.py")).mutant_names
            every = mutate_file_contents("m.py", narrowed).mutant_names
            on_the_line = mutate_file_contents("m.py", narrowed, {4}).mutant_names
        finally:
            reset_config()
        assert generated and sorted(generated) == sorted(on_the_line)
        assert len(every) > len(generated)
        counts = json.loads(record.read_text(encoding="utf-8"))["files"]
        assert counts == {"m.py": {"x_long": {"held": len(every), "window": len(generated)}}}

    def _stub_engine(self, monkeypatch: pytest.MonkeyPatch, **attrs: Any) -> list[dict[str, Any]]:
        """An engine module with only ``attrs`` and a command line that
        records its calls, in place of mutmut's."""
        calls: list[dict[str, Any]] = []
        package = types.ModuleType("mutmut")
        package.__path__ = []
        stub = types.ModuleType("mutmut.__main__")
        stub.cli = lambda **kwargs: calls.append(kwargs)  # type: ignore[attr-defined]
        for name, value in attrs.items():
            setattr(stub, name, value)
        monkeypatch.setitem(sys.modules, "mutmut", package)
        monkeypatch.setitem(sys.modules, "mutmut.__main__", stub)
        return calls

    def test_an_engine_without_the_hook_stops_before_it_generates(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A mutmut with no covered-lines hook cannot keep the window, so the
        engine stops with its own status, which the lane reads as an engine
        failure (exit 2), and mutmut's command line never runs."""
        calls = self._stub_engine(monkeypatch)
        window_file, record = _window_file(tmp_path, {})
        monkeypatch.setenv(md.WINDOW_ENV, str(window_file))
        assert md.engine_main(["run", "--max-children", "1"]) == md.NO_WINDOW_EXIT
        assert calls == [] and not record.exists()

    def test_the_window_is_applied_to_a_run_alone(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """`results` and `show` read what a run generated, so the window is
        not applied to them, and an engine that could not apply it still
        answers them."""
        calls = self._stub_engine(monkeypatch)
        window_file, _record = _window_file(tmp_path, {})
        monkeypatch.setenv(md.WINDOW_ENV, str(window_file))
        assert md.engine_main(["results", "--all", "true"]) == 0
        assert calls == [{"args": ["results", "--all", "true"], "prog_name": "mutmut"}]

    def test_the_default_engine_is_this_script_under_this_interpreter(self) -> None:
        assert md._default_engine() == [sys.executable, str(_SCRIPT.resolve()), md.ENGINE_ARG]


# ---------------------------------------------------------------------------
# The enclosing nodes: mutants mutmut places above the line they change
# ---------------------------------------------------------------------------


#: vera/checker/control.py's shape at 94cef528 in small: a diagnostic's
#: `error_code=` six lines below the first line of the call that passes it
#: (there, :430 below :419).
ANCHORED = _src("""
    class Checker:
        def check(self, expr):
            if expr.bad:
                self._error(
                    expr,
                    "a message",
                    rationale="why",
                    fix="how",
                    spec_ref="ch04",
                    error_code="E302",
                )
            return expr
""")

#: A `case` five lines below its `match`.
MATCHED = _src("""
    def pick(x):
        match x:
            case "a":
                return 1
            case "b":
                return 2
            case "z":
                return 26
        return 0
""")

#: One node of each of the enclosing kinds, each with text its mutants
#: change three or more lines below its first line, where no node of another
#: kind starts on that first line and spans the same lines.
ENCLOSING = _src("""
    class Shapes:
        def call(self, x):
            return self.pick(
                x,
                1,
                key="k",
            )

        def keyword(self, x):
            return dict(
                a=x,
                b=x,
                c=x,
                d=x,
            )

        def method(self, x):
            return (x
                    .strip()
                    .replace("a", "b")
                    .replace("c", "d")
                    .lower())

        def assign(self, x):
            y = [
                x,
                x * 2,
                "s",
            ]
            return y

        def annotated(self, x):
            y: list[int] = [
                x,
                2,
                3,
            ]
            return y

        def augmented(self, x):
            self.totals[
                x
                * 2
                - 3
            ] += 1
            return x

        def binary(self, x):
            return (x
                    + 1
                    + 2
                    + 3
                    + 4)

        def boolean(self, x, y, z):
            return (x
                    and y
                    and z
                    and x
                    and y)

        def comparison(self, x):
            return (self.size(x)
                    == self.limit(
                        x,
                        2,
                    ))

        def conditional(self, x):
            return (
                self.big(
                    x,
                )
                if x > 0
                else 0
            )

        def anonymous(self):
            return (lambda v:
                    self.big(
                        v,
                        1,
                    ))

        def selection(self, x):
            match x:
                case 1:
                    return "one"
                case 2:
                    return "two"
                case 3:
                    return "three"
            return "other"
""")


def _placed_mutations(path: str, source: str) -> list[tuple[str, int | None, frozenset[int], str]]:
    """Every mutation mutmut's visitor makes inside a unit of ``source``, as
    (the unit's key, the line mutmut places it on, the lines whose text it
    changes, its node's kind).

    The lines it changes are those of the non-whitespace characters its
    mutated node removes or replaces from the original node's text (an
    insertion counts on the line of the character before it), placed from
    where the original node's text starts.  Each placement is checked against
    the source, character by character, so a misplaced line fails here
    rather than hiding a mutant."""
    import difflib

    import libcst as cst
    from libcst.metadata import (
        MetadataWrapper,
        PositionProvider,
        WhitespaceInclusivePositionProvider,
    )
    from mutmut.mutation.file_mutation import create_mutations

    module, mutations, _classes, _functions = create_mutations(path, source, None)
    wrapper = MetadataWrapper(module, unsafe_skip_copy=True)
    starts = wrapper.resolve(PositionProvider)
    texts = wrapper.resolve(WhitespaceInclusivePositionProvider)
    keys: dict[Any, str] = {}
    for stmt in module.body:
        if isinstance(stmt, cst.FunctionDef):
            keys[stmt] = md._key(stmt.name.value, None)
        elif isinstance(stmt, cst.ClassDef) and isinstance(stmt.body, cst.IndentedBlock):
            keys.update({m: md._key(m.name.value, stmt.name.value) for m in stmt.body.body
                         if isinstance(m, cst.FunctionDef)})
    rows = source.splitlines()
    placed = []
    for mutation in mutations:
        unit = keys.get(mutation.contained_by_top_level_function)
        if unit is None:
            continue
        node = mutation.original_node
        where = texts[node]
        chunk = rows[where.start.line - 1:where.end.line]
        chunk[-1] = chunk[-1][:where.end.column]
        chunk[0] = chunk[0][where.start.column:]
        in_source = [(ch, n) for n, row in enumerate(chunk, start=where.start.line)
                     for ch in row if not ch.isspace()]
        chars: list[tuple[str, int]] = []
        line = where.start.line
        for ch in module.code_for_node(node):
            if ch == "\n":
                line += 1
            elif not ch.isspace():
                chars.append((ch, line))
        assert chars == in_source, f"{path}: a mutation of line {where.start.line} is misplaced"
        mutated = [ch for ch in module.code_for_node(mutation.mutated_node) if not ch.isspace()]
        changed: set[int] = set()
        opcodes = difflib.SequenceMatcher(None, [c for c, _ in chars], mutated,
                                          autojunk=False).get_opcodes()
        for tag, i1, i2, _j1, _j2 in opcodes:
            if tag != "equal":
                changed.update(n for _c, n in (chars[i1:i2] if i2 > i1 else chars[max(i1 - 1, 0):][:1]))
        start = starts.get(node)
        placed.append((unit, None if start is None else start.start.line, frozenset(changed),
                       type(node).__name__))
    return placed


def _misses(path: str, source: str) -> list[str]:
    """Each mutation that changes a line of the window of a one-line edit,
    at every line of every unit of ``source``, but that mutmut's covered-lines
    filter drops when handed the window the engine builds: the window's lines
    clipped to the unit, as the lane hands them over, and the first lines
    :func:`md.first_lines` adds for them."""
    spans = md.enclosing_spans(source)
    by_unit: dict[str, list[tuple[int | None, frozenset[int], str]]] = {}
    for unit, anchor, changed, kind in _placed_mutations(path, source):
        by_unit.setdefault(unit, []).append((anchor, changed, kind))
    found = []
    for key, unit in md.scan_units(source, path).items():
        lines = set(range(unit.start, unit.end + 1))
        for edited in sorted(lines):
            named = md.window(_change(path, {edited})) & lines
            covered = named | md.first_lines(spans, named)
            found += [f"{path}:{edited}: {kind} placed on {anchor} changes {sorted(changed)}"
                      for anchor, changed, kind in by_unit.get(key, [])
                      if changed & named and anchor is not None and anchor not in covered]
    return found


class TestTheEnclosingNodes:
    """mutmut places a mutant on the first line of the node it mutates, and
    a call's, a match's and the other enclosing kinds' mutants change text
    further down: an argument, a `case`, an operator after a long operand.
    The window holds the first line of each such node that spans one of its
    lines, so a change to those lines keeps the mutants that change them."""

    def test_a_comparison_starts_on_the_line_above_its_operator(self) -> None:
        """A comparison's operator and right operand start with the line break
        before the operator, so mutmut places its swap on the line above."""
        pytest.importorskip("libcst")
        source = _src("""
            def f(x):
                return (x
                        == 3)
        """)
        assert md.enclosing_spans(source) == [(2, 3)]

    def _generate(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, source: str,
                  edited: int) -> tuple[list[ast.FunctionDef], set[int]]:
        """mutmut's own generation of ``source`` with the window of a one-line
        edit at line ``edited`` installed, as the engine installs it: the
        mutant functions it writes, and the lines its filter was handed."""
        pytest.importorskip("mutmut")
        import mutmut.__main__ as engine
        from mutmut.configuration import reset_config

        (tmp_path / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["."]\n', encoding="utf-8")
        (tmp_path / "m.py").write_text(source, encoding="utf-8")
        (unit,) = [u for u in md.scan_units(source, "m.py").values()
                   if u.start <= edited <= u.end]
        named = md.window(_change("m.py", {edited})) & set(range(unit.start, unit.end + 1))
        window_file, _record = _window_file(tmp_path, {"m.py": sorted(named)})
        monkeypatch.chdir(tmp_path)
        monkeypatch.setattr(engine, "get_covered_lines_for_file", engine.get_covered_lines_for_file)
        reset_config()
        try:
            md.install_window(engine, window_file)
            covered = set(engine.get_covered_lines_for_file("m.py", None))
            code = engine.write_all_mutants_to_file(
                out=io.StringIO(), source=source, filename=Path("m.py")).code
        finally:
            reset_config()
        mutants = [node for node in ast.walk(ast.parse(code))
                   if isinstance(node, ast.FunctionDef) and "__mutmut_" in node.name
                   and not node.name.endswith("_orig")]
        return mutants, covered

    def test_a_changed_argument_keeps_the_mutants_its_call_places_above_repro(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """R96's repro: an edit to `error_code="E302",` keeps the argument's
        `None` and its removal, which mutmut places on `self._error(`, six
        lines up; the window of the edit's lines alone dropped both."""
        mutants, covered = self._generate(tmp_path, monkeypatch, ANCHORED,
                                          _line_of(ANCHORED, 'error_code="E302"'))
        assert _line_of(ANCHORED, "self._error(") in covered

        def error_code(fn: ast.FunctionDef) -> list[Any]:
            (call,) = [n for n in ast.walk(fn) if isinstance(n, ast.Call)
                       and isinstance(n.func, ast.Attribute) and n.func.attr == "_error"]
            return [k.value for k in call.keywords if k.arg == "error_code"]

        codes = [error_code(fn) for fn in mutants]
        assert [] in codes, "the removal of `error_code=` was not generated"
        assert any(len(c) == 1 and isinstance(c[0], ast.Constant) and c[0].value is None
                   for c in codes), "`error_code=None` was not generated"

    def test_a_changed_case_keeps_its_removal_repro(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """An edit to `case "z":` keeps the removal of that case, which
        mutmut places on the `match` line, five lines up."""
        mutants, covered = self._generate(tmp_path, monkeypatch, MATCHED,
                                          _line_of(MATCHED, 'case "z"'))
        assert _line_of(MATCHED, "match x:") in covered

        def cases(fn: ast.FunctionDef) -> list[Any]:
            (match,) = [n for n in ast.walk(fn) if isinstance(n, ast.Match)]
            return [c.pattern.value.value for c in match.cases
                    if isinstance(c.pattern, ast.MatchValue)
                    and isinstance(c.pattern.value, ast.Constant)]

        assert ["a", "b"] in [cases(fn) for fn in mutants], "the removal of `case \"z\"` was not generated"

    @pytest.mark.parametrize("target", ["ENCLOSING", "vera/checker/control.py", "vera/smt.py"])
    def test_every_mutant_that_changes_a_window_line_is_generated(self, target: str) -> None:
        """The class: at every line of every function, the window of a
        one-line edit there holds the line mutmut places each mutant on whose
        text meets the window, over the enclosing kinds in small and over two
        of the compiler's modules."""
        pytest.importorskip("mutmut")
        source = ENCLOSING if target == "ENCLOSING" else (ROOT / target).read_text(encoding="utf-8")
        misses = _misses(target, source)
        assert not misses, f"{len(misses)} dropped, the first: {misses[:5]}"

    @pytest.mark.parametrize("kind", md.ENCLOSING_KINDS)
    def test_each_enclosing_kind_keeps_mutants_no_other_kind_keeps(
        self, kind: str, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Every kind the window reads is needed: without it, a mutant of a
        node of that kind, and of no other, is dropped from a window it
        changes a line of."""
        pytest.importorskip("mutmut")
        monkeypatch.setattr(md, "ENCLOSING_KINDS", tuple(k for k in md.ENCLOSING_KINDS if k != kind))
        misses = _misses("ENCLOSING", ENCLOSING)
        assert misses and {m.split(": ", 1)[1].split(" ", 1)[0] for m in misses} == {kind}


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


STATS_FAILURE = """\
Running stats
FAILED tests/test_checker_errors.py::TestErrorCodes::test_error_code_collision_gate_is_clean - AssertionError: 13 collision(s):
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 6532 passed in 101.2s
failed to collect stats. runner returned 1
"""


class TestCopyFailure:
    def test_the_stats_pass_names_its_failing_test(self) -> None:
        assert md.copy_failure(STATS_FAILURE) == (
            "tests/test_checker_errors.py::TestErrorCodes::test_error_code_collision_gate_is_clean")

    def test_a_clean_run_names_its_failing_test(self) -> None:
        log = ("ERROR tests/test_lsp.py::TestDocuments::test_writes[a b] - FileNotFoundError: x\n"
               "Failed to run clean test\n")
        assert md.copy_failure(log) == "tests/test_lsp.py::TestDocuments::test_writes[a b]"

    def test_a_log_with_no_such_stop_names_none(self) -> None:
        assert md.copy_failure("Running mutation testing\n1.0 mutations/second\n") is None
        assert md.copy_failure("FAILED tests/test_x.py::t - y\nsomething else went wrong\n") is None


# What mutmut's log holds when its stats pass stops, read off the engine
# itself.  mutmut runs pytest with ``--tb=native``, so each report carries
# Python's own traceback.  The path prefixes are shortened and the spinner's
# frames left out; where a constant says so, the frames of pytest and pluggy
# between a report's first frame and the test's own are left out too, which
# changes nothing the lane reads: it reads a traceback from its innermost
# frame outward.

#: The night of 28 October 2026 (run 40607843242): mutmut 3.8.0's stats
#: collector reads ``item._nodeid`` at every test's teardown, which pytest
#: 9.2.0 dropped, so every test of the stats pass errors there with no mutant
#: active.  The first attempt's log of
#: ``test_mutate_sweep.py::TestEndToEnd::test_mutmut_itself_decides_a_night``,
#: reproduced under that resolution.
NIGHT_LOG = """\
    done in 40ms (1 files mutated, 1 ignored, 0 unmodified)

.E
==================================== ERRORS ====================================
_________________________ ERROR at teardown of test_f __________________________
Traceback (most recent call last):
  File "/venv/lib/python3.14/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
                             ~~~~^^
  File "/venv/lib/python3.14/site-packages/_pytest/runner.py", line 250, in <lambda>
    lambda: runtest_hook(item=item, **kwds),
            ~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.14/site-packages/pluggy/_caller.py", line 197, in __call__
    return self._hookexec(
           ~~~~~~~~~~~~~~^
        self.name, self._hookimpls.copy(), call_kwargs, firstresult
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    )
    ^
  File "/venv/lib/python3.14/site-packages/pluggy/_manager.py", line 183, in _hookexec
    return self._inner_hookexec(hook_name, methods, kwargs, firstresult)
           ~~~~~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.14/site-packages/pluggy/_execution.py", line 195, in _multicall
    raise exception
  File "/venv/lib/python3.14/site-packages/pluggy/_execution.py", line 167, in _multicall
    teardown.throw(exception)
    ~~~~~~~~~~~~~~^^^^^^^^^^^
  File "/venv/lib/python3.14/site-packages/_pytest/logging.py", line 886, in pytest_runtest_teardown
    yield
  File "/venv/lib/python3.14/site-packages/pluggy/_execution.py", line 167, in _multicall
    teardown.throw(exception)
    ~~~~~~~~~~~~~~^^^^^^^^^^^
  File "/venv/lib/python3.14/site-packages/_pytest/capture.py", line 911, in pytest_runtest_teardown
    return (yield)
            ^^^^^
  File "/venv/lib/python3.14/site-packages/pluggy/_execution.py", line 147, in _multicall
    res = hook_impl.function(*args)
  File "/venv/lib/python3.14/site-packages/mutmut/runners/harness.py", line 157, in pytest_runtest_teardown
    state().tests_by_mangled_function_name[function].add(strip_prefix(item._nodeid, prefix="mutants/"))
                                                                      ^^^^^^^^^^^^
AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'?
=========================== short test summary info ============================
ERROR tests/test_m.py::test_f - AttributeError: 'Function' object has no attr...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 passed, 1 error in 0.01s
failed to collect stats. runner returned 1

"""

#: What the night's engine named after both of its tests were deselected.
NIGHT_LAST_LOG = """\
    done in 13ms (0 files mutated, 1 ignored, 1 unmodified)
2 deselected in 0.01s
failed to collect stats. runner returned 5
"""

NIGHT_ERROR = ("AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'? "
               "(mutmut/runners/harness.py:157)")

#: mutmut's own code calling the standard library, which raises: with
#: ``max_stack_depth`` set, ``record_trampoline_hit`` resolves each frame's
#: file strictly, and code ``exec`` compiled has the file ``<string>``
#: (mutmut 3.8.1, pytest 9.2.0; pytest's and pluggy's frames left out).
ENGINE_IN_THE_STDLIB_LOG = r"""
    done in 30ms (2 files mutated, 0 ignored, 0 unmodified)

F
=================================== FAILURES ===================================
____________________________________ test_f ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 5, in test_f
    exec('from vera.m import f\nassert f(1) == 2')
  File "<string>", line 2, in <module>
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 97, in trampoline
    record_trampoline_hit(orig_qual_name, caller=caller_name)
  File "/venv/lib/python3.12/site-packages/mutmut/stats.py", line 163, in record_trampoline_hit
    file_path = Path(filename).resolve(strict=True)
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/python/lib/python3.12/pathlib.py", line 1240, in resolve
    s = self._flavour.realpath(self, strict=strict)
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "<frozen posixpath>", line 427, in realpath
  File "<frozen posixpath>", line 471, in _joinrealpath
FileNotFoundError: [Errno 2] No such file or directory: '<string>'
=========================== short test summary info ============================
FAILED tests/test_m.py::test_f - FileNotFoundError: [Errno 2] No such file or...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed in 0.01s
failed to collect stats. runner returned 1
"""

#: A test that reads a file the copy does not hold: it fails in its own
#: body, inside the standard library (mutmut 3.8.1, pytest 9.2.0; pytest's
#: and pluggy's frames left out).
BODY_FAILURE_LOG = """\
    done in 27ms (2 files mutated, 0 ignored, 0 unmodified)

.F
=================================== FAILURES ===================================
____________________________________ test_g ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 11, in test_g
    Path('not_in_the_copy.txt').read_text()
  File "/python/lib/python3.12/pathlib.py", line 1027, in read_text
    with self.open(mode='r', encoding=encoding, errors=errors) as f:
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/python/lib/python3.12/pathlib.py", line 1013, in open
    return io.open(self, mode, buffering, encoding, errors, newline)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
FileNotFoundError: [Errno 2] No such file or directory: 'not_in_the_copy.txt'
=========================== short test summary info ============================
FAILED tests/test_m.py::test_g - FileNotFoundError: [Errno 2] No such file or...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 1 passed in 0.01s
failed to collect stats. runner returned 1
"""

#: The code under test raising when a test calls it through mutmut's
#: trampoline: the engine's frames lie between the test's and the raise
#: (mutmut 3.8.1, pytest 9.2.0; pytest's and pluggy's frames left out).
TRAMPOLINED_CODE_LOG = """\
    done in 31ms (2 files mutated, 0 ignored, 0 unmodified)

.F
=================================== FAILURES ===================================
____________________________________ test_g ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 9, in test_g
    assert f(None) == 6
           ^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 100, in trampoline
    return orig_func(*call_args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/work/tree/mutants/vera/m.py", line 9, in x_f__mutmut_orig
    return x + 1
           ~~^~~
TypeError: unsupported operand type(s) for +: 'NoneType' and 'int'
=========================== short test summary info ============================
FAILED tests/test_m.py::test_g - TypeError: unsupported operand type(s) for +...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 1 passed in 0.01s
failed to collect stats. runner returned 1
"""

#: A test whose recursion through a trampolined function runs out of stack.
#: Every call through the trampoline adds the engine's two frames, so a
#: recursion the suite passes can run out in mutmut's copy, and where it runs
#: out falls wherever the stack ends: here in the engine's own frame, in one
#: of every three depths the probe tried.  The nightly sweep drops such tests
#: (``tests/test_family_naming.py``'s cap tests, whose 200-deep predicate
#: recurses through ``ExpressionsMixin._synth_expr``).  mutmut 3.8.1, pytest
#: 9.2.0; pytest's and pluggy's frames left out, and of the recursion's
#: frames the last twelve kept.
RECURSION_LOG = """\
    done in 30ms (2 files mutated, 0 ignored, 0 unmodified)

.F
=================================== FAILURES ===================================
____________________________________ test_g ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 21, in test_g
    assert h0(100000) == 100000
           ^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 100, in trampoline
    return orig_func(*call_args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/work/tree/mutants/vera/m.py", line 9, in x_deep__mutmut_orig
    return 0 if n == 0 else deep(n - 1) + 1
                            ^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 100, in trampoline
    return orig_func(*call_args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/work/tree/mutants/vera/m.py", line 9, in x_deep__mutmut_orig
    return 0 if n == 0 else deep(n - 1) + 1
                            ^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 85, in trampoline
    mutant_under_test = get_mutant_under_test()
                        ^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 54, in get_mutant_under_test
    if "MUTANT_UNDER_TEST" in os.environ:
       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
RecursionError: maximum recursion depth exceeded
=========================== short test summary info ============================
FAILED tests/test_m.py::test_g - RecursionError: maximum recursion depth exce...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 1 passed in 0.02s
failed to collect stats. runner returned 1
"""

# The next three are logs of the engine with a stats hook of its own placed
# in its installed package (``mutmut/probe_makereport.py``,
# ``mutmut/probe_recurse.py``, loaded with ``-p``), where mutmut 3.8.0's
# ``mutmut/runners/harness.py`` hooks live, and of a test that prints a
# traceback (mutmut 3.8.1, pytest 9.2.0).

#: A stats hook of the engine raising in ``pytest_runtest_makereport``,
#: outside a test's phases: pytest prints the traceback as INTERNALERROR
#: lines and exits 3 (pytest's and pluggy's frames left out).
INTERNALERROR_LOG = """\
    done in 24ms (2 files mutated, 0 ignored, 0 unmodified)

INTERNALERROR> Traceback (most recent call last):
INTERNALERROR>   File "/venv/lib/python3.12/site-packages/_pytest/main.py", line 333, in wrap_session
INTERNALERROR>     session.exitstatus = doit(config, session) or 0
INTERNALERROR>   File "/venv/lib/python3.12/site-packages/mutmut/probe_makereport.py", line 3, in pytest_runtest_makereport
INTERNALERROR>     return {item._nodeid: call}
INTERNALERROR>             ^^^^^^^^^^^^
INTERNALERROR> AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'?

no tests ran in 0.01s
failed to collect stats. runner returned 3
"""

#: A stats hook of the engine recursing in its own frames at a test's
#: teardown, the repeated frame compressed as Python prints it (pytest's and
#: pluggy's frames left out).
ENGINE_RECURSION_LOG = """\
    done in 22ms (2 files mutated, 0 ignored, 0 unmodified)

.E
==================================== ERRORS ====================================
_________________________ ERROR at teardown of test_f __________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/venv/lib/python3.12/site-packages/mutmut/probe_recurse.py", line 6, in pytest_runtest_teardown
    _walk(0)
  File "/venv/lib/python3.12/site-packages/mutmut/probe_recurse.py", line 2, in _walk
    return _walk(depth + 1)
           ^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/probe_recurse.py", line 2, in _walk
    return _walk(depth + 1)
           ^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/probe_recurse.py", line 2, in _walk
    return _walk(depth + 1)
           ^^^^^^^^^^^^^^^^
  [Previous line repeated 960 more times]
RecursionError: maximum recursion depth exceeded
=========================== short test summary info ============================
ERROR tests/test_m.py::test_f - RecursionError: maximum recursion depth exceeded
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 passed, 1 error in 0.01s
failed to collect stats. runner returned 1
"""

#: A test that fails in its own body after printing, to its captured stderr,
#: a traceback raised in the engine's trampoline (a call with one argument
#: too many); the report's own frames are pytest's, left out, then the
#: test's.
CAPTURED_LOG = """\
    done in 21ms (2 files mutated, 0 ignored, 0 unmodified)

.F
=================================== FAILURES ===================================
____________________________________ test_g ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 15, in test_g
    assert g(3) == 7
AssertionError: assert 6 == 7
 +  where 6 = g(3)
----------------------------- Captured stderr call -----------------------------
Traceback (most recent call last):
  File "/work/tree/mutants/tests/test_m.py", line 12, in test_g
    f(1, 2)
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 100, in trampoline
    return orig_func(*call_args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
TypeError: x_f__mutmut_orig() takes 1 positional argument but 2 were given
=========================== short test summary info ============================
FAILED tests/test_m.py::test_g - assert 6 == 7
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 1 passed in 0.01s
failed to collect stats. runner returned 1
"""

#: A function of the engine recursing on itself inside a test's call: the
#: test calls the code under test, which calls the engine's ``walk``.
#: Python's traceback printer prints a frame repeated in a row three times
#: and then a count of the rest, so the ten innermost printed frames reach
#: the copy's (pytest 9.2.0, a module placed at ``mutmut/rec.py``, the stop
#: line mutmut prints after it; pytest's and pluggy's frames left out).
SELF_RECURSION_LOG = """\
F
=================================== FAILURES ===================================
____________________________________ test_g ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 5, in test_g
    f()
  File "/work/tree/mutants/vera/m.py", line 5, in f
    return walk(0)
           ^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/rec.py", line 2, in walk
    return walk(n + 1)
           ^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/rec.py", line 2, in walk
    return walk(n + 1)
           ^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/rec.py", line 2, in walk
    return walk(n + 1)
           ^^^^^^^^^^^
  [Previous line repeated 963 more times]
RecursionError: maximum recursion depth exceeded
=========================== short test summary info ============================
FAILED tests/test_m.py::test_g - RecursionError: maximum recursion depth exce...
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed in 0.01s
failed to collect stats. runner returned 1
"""

#: A test that prints two banners of its own and then a traceback raised in
#: the engine's trampoline to its stdout, and fails in its own body: lines
#: shaped like pytest's rules, but not drawn its width, inside its captured
#: output (mutmut 3.8.1, pytest 9.2.0; pytest's and pluggy's frames left
#: out).
BANNER_LOG = """\
    done in 23ms (2 files mutated, 0 ignored, 0 unmodified)

.F
=================================== FAILURES ===================================
____________________________________ test_g ____________________________________
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 18, in test_g
    assert g(3) == 7
AssertionError: assert 6 == 7
 +  where 6 = g(3)
----------------------------- Captured stdout call -----------------------------
=============== the program's own banner ===============
--- a heading the program printed ---
Traceback (most recent call last):
  File "/work/tree/mutants/tests/test_m.py", line 15, in test_g
    f(1, 2)
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 172, in _trampoline_wrapper
    return trampoline(*args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/venv/lib/python3.12/site-packages/mutmut/mutation/trampoline.py", line 100, in trampoline
    return orig_func(*call_args, **kwargs)
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
TypeError: x_f__mutmut_orig() takes 1 positional argument but 2 were given
=========================== short test summary info ============================
FAILED tests/test_m.py::test_g - assert 6 == 7
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 1 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
1 failed, 1 passed in 0.01s
failed to collect stats. runner returned 1
"""

#: The night's engine (mutmut 3.8.0, pytest 9.2.0) under a test with a
#: 73-character name, whose fixture reaches a mutated function, logs a
#: warning and raises: the test's own setup error, carrying ``Captured log
#: setup``, then the engine's teardown hook raising.  pytest draws both
#: reports' rules with one fill character either side of the long title
#: (pytest's and pluggy's frames left out).
LONG_NAME_LOG = """\
    done in 21ms (2 files mutated, 0 ignored, 0 unmodified)

EE
==================================== ERRORS ====================================
_ ERROR at setup of test_a_name_vera_writes_as_a_sentence_a_name_vera_writes_as_a_sentence_a_ _
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/work/tree/mutants/tests/test_m.py", line 12, in broken
    raise RuntimeError('the fixture cannot start')
RuntimeError: the fixture cannot start
------------------------------ Captured log setup ------------------------------
WARNING  fixture:test_m.py:11 the fixture logs before it fails
_ ERROR at teardown of test_a_name_vera_writes_as_a_sentence_a_name_vera_writes_as_a_sentence_a_ _
Traceback (most recent call last):
  File "/venv/lib/python3.12/site-packages/_pytest/runner.py", line 361, in from_call
    result: TResult | None = func()
  File "/venv/lib/python3.12/site-packages/mutmut/runners/harness.py", line 157, in pytest_runtest_teardown
    state().tests_by_mangled_function_name[function].add(strip_prefix(item._nodeid, prefix="mutants/"))
                                                                      ^^^^^^^^^^^^
AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'?
------------------------------ Captured log setup ------------------------------
WARNING  fixture:test_m.py:11 the fixture logs before it fails
=========================== short test summary info ============================
ERROR tests/test_m.py::test_a_name_vera_writes_as_a_sentence_a_name_vera_writes_as_a_sentence_a_
ERROR tests/test_m.py::test_a_name_vera_writes_as_a_sentence_a_name_vera_writes_as_a_sentence_a_
!!!!!!!!!!!!!!!!!!!!!!!!!! stopping after 2 failures !!!!!!!!!!!!!!!!!!!!!!!!!!!
2 errors in 0.01s
failed to collect stats. runner returned 1
"""


class TestEngineFailure:
    """An exception the engine's own code raised stops its stats pass or its
    clean run as a failing test does, and no test is at fault: the lane
    names the exception and the engine's frame instead of a test to drop."""

    def test_the_nights_teardown_hook_is_the_engines_own_failure(self) -> None:
        assert md.engine_failure(NIGHT_LOG) == NIGHT_ERROR

    def test_a_long_exception_is_cut_to_the_records_bound_and_keeps_its_frame(self) -> None:
        """The sweep refuses a record whose ``engine_error`` is longer
        (``mutate_sweep.check_record``)."""
        log = NIGHT_LOG.replace("Did you mean: 'nodeid'?", "Did you mean: 'nodeid'? " + "x" * 1000)
        error = md.engine_failure(log)
        assert error is not None and len(error) == md.ENGINE_ERROR_CHARS == 500
        assert error.startswith("AttributeError: ") and error.endswith("x… (mutmut/runners/harness.py:157)")

    def test_the_standard_library_raising_under_the_engines_frame_is_the_engines(self) -> None:
        assert md.engine_failure(ENGINE_IN_THE_STDLIB_LOG) == (
            "FileNotFoundError: [Errno 2] No such file or directory: '<string>' (mutmut/stats.py:163)")

    def test_a_test_failing_in_its_own_body_is_no_engine_failure(self) -> None:
        assert md.engine_failure(BODY_FAILURE_LOG) is None
        assert md.copy_failure(BODY_FAILURE_LOG) == "tests/test_m.py::test_g"

    def test_the_code_under_test_raising_through_the_trampoline_is_no_engine_failure(self) -> None:
        assert md.engine_failure(TRAMPOLINED_CODE_LOG) is None
        assert md.copy_failure(TRAMPOLINED_CODE_LOG) == "tests/test_m.py::test_g"

    def test_the_engine_is_the_installed_package_not_a_directory_of_its_name(self) -> None:
        """A scratch tree under a directory named ``mutmut`` (a checkout of
        the engine, say) is still the copy: its frames are the test's."""
        log = TRAMPOLINED_CODE_LOG.replace("/work/tree/mutants/", "/home/u/mutmut/work/tree/mutants/")
        assert "/mutmut/work/tree/mutants/vera/m.py" in log
        assert md.engine_failure(log) is None

    def test_a_recursion_that_runs_out_in_the_engines_frame_is_no_engine_failure(self) -> None:
        """Where a recursion runs out of stack is where the stack ends, not
        where a fault lies: a frame of the copy among its innermost frames
        makes it the test's."""
        assert md.engine_failure(RECURSION_LOG) is None
        assert md.copy_failure(RECURSION_LOG) == "tests/test_m.py::test_g"

    def test_a_recursion_in_the_engines_own_frames_is_the_engines(self) -> None:
        """No frame of the copy among its innermost frames: the engine
        recursed in its own code."""
        assert md.engine_failure(ENGINE_RECURSION_LOG) == (
            "RecursionError: maximum recursion depth exceeded (mutmut/probe_recurse.py:2)")

    def test_an_internal_error_of_the_engines_own_hook_is_the_engines(self) -> None:
        """A hook raising outside a test's phases is pytest's INTERNALERROR:
        no report names a test, and every line of the traceback carries the
        prefix."""
        assert md.copy_failure(INTERNALERROR_LOG) is None
        assert md.engine_failure(INTERNALERROR_LOG) == (
            "AttributeError: 'Function' object has no attribute '_nodeid'. Did you mean: 'nodeid'? "
            "(mutmut/probe_makereport.py:3)")

    def test_a_traceback_in_a_tests_captured_output_decides_nothing(self) -> None:
        """The test failed in its own body; the trampoline traceback it
        printed is its captured stderr, not a report."""
        assert md.engine_failure(CAPTURED_LOG) is None
        assert md.copy_failure(CAPTURED_LOG) == "tests/test_m.py::test_g"

    def test_an_engine_traceback_outside_a_stopped_pass_is_no_engine_failure(self) -> None:
        """The lane reads a pass that stopped, the stats pass or the clean
        run: the same traceback in a log that names no stop decides
        nothing."""
        assert md.engine_failure(NIGHT_LOG.replace("failed to collect stats. runner returned 1\n", "")) is None
        assert md.engine_failure(NIGHT_LOG.replace("failed to collect stats", "Failed to run clean test")) == (
            NIGHT_ERROR)


class TestRunDropping:
    """``run_dropping`` against a stand-in for ``run_engine`` that writes,
    for each attempt, the log the engine would print given the tests the
    attempt's configuration deselects."""

    def _run(self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
             log_for: Any) -> tuple[Any, list[str], list[str]]:
        attempts: list[str] = []

        def fake_run_engine(cmd: Any, *, cwd: Path, budget_s: float, log_path: Path,
                            env: Any = None, grace_s: Any = None) -> Any:
            config = (cwd / "pyproject.toml").read_text(encoding="utf-8")
            attempts.append(config)
            log, code = log_for({line.removeprefix("--deselect=") for line in config.split()})
            log_path.write_text(log, encoding="utf-8")
            return md.EngineRun(code, None, 0.1)

        monkeypatch.setattr(md, "run_engine", fake_run_engine)
        run, _, dropped = md.run_dropping(
            ["mutmut", "run"], tree=tmp_path, pyproject=tmp_path / "pyproject.toml",
            config_for=lambda dropped: "".join(f"--deselect={t}\n" for t in dropped),
            budget_s=100.0, workdir=tmp_path, env={})
        return run, dropped, attempts

    @staticmethod
    def _night(deselected: set[str]) -> tuple[str, int]:
        """The night's engine: each of its two tests errors at teardown in
        mutmut's own hook, the first one not deselected naming the stop."""
        for test in ("test_f", "test_g"):
            if f"tests/test_m.py::{test}" not in deselected:
                return NIGHT_LOG.replace("test_f", test), 1
        return NIGHT_LAST_LOG, 1

    def test_the_engines_own_failure_stops_the_run_at_its_first_attempt_and_drops_nothing(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The night dropped both tests as failing in the copy, and its third
        attempt deselected every test (pytest's exit 5)."""
        run, dropped, attempts = self._run(tmp_path, monkeypatch, self._night)
        assert (len(attempts), dropped) == (1, [])
        assert run.returncode == 1 and run.error == NIGHT_ERROR

    def test_a_test_failing_in_its_own_body_is_dropped_and_the_run_goes_again(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        run, dropped, attempts = self._run(tmp_path, monkeypatch, lambda deselected: (
            ("", 0) if "tests/test_m.py::test_g" in deselected else (BODY_FAILURE_LOG, 1)))
        assert (len(attempts), dropped) == (2, ["tests/test_m.py::test_g"])
        assert run.returncode == 0

    def test_a_recursion_through_the_engines_frames_is_dropped_as_the_tests(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        run, dropped, attempts = self._run(tmp_path, monkeypatch, lambda deselected: (
            ("", 0) if "tests/test_m.py::test_g" in deselected else (RECURSION_LOG, 1)))
        assert (len(attempts), dropped) == (2, ["tests/test_m.py::test_g"])
        assert run.returncode == 0

    def test_a_test_whose_captured_output_holds_an_engine_traceback_is_dropped(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        run, dropped, attempts = self._run(tmp_path, monkeypatch, lambda deselected: (
            ("", 0) if "tests/test_m.py::test_g" in deselected else (CAPTURED_LOG, 1)))
        assert (len(attempts), dropped) == (2, ["tests/test_m.py::test_g"])
        assert run.returncode == 0  # an engine stop would end the first attempt, dropping nothing

    def test_an_engine_function_recursing_on_itself_in_a_tests_call_is_named_at_once(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The printed ``[Previous line repeated 963 more times]`` counts:
        the engine's frames fill the ten innermost, though the copy's are
        printed within them."""
        run, dropped, attempts = self._run(tmp_path, monkeypatch, lambda deselected: (SELF_RECURSION_LOG, 1))
        assert (len(attempts), dropped) == (1, [])
        assert run.error == "RecursionError: maximum recursion depth exceeded (mutmut/rec.py:2)"

    def test_a_banner_in_a_tests_captured_output_leaves_the_test_dropped(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Lines the program printed in the shape of pytest's rules, inside
        its captured stdout, end nothing: a rule is drawn the terminal's
        width."""
        run, dropped, attempts = self._run(tmp_path, monkeypatch, lambda deselected: (
            ("", 0) if "tests/test_m.py::test_g" in deselected else (BANNER_LOG, 1)))
        assert (len(attempts), dropped) == (2, ["tests/test_m.py::test_g"])
        assert run.returncode == 0  # an engine stop would end the first attempt, dropping nothing

    def test_an_engine_failure_behind_a_long_named_tests_setup_error_is_named_at_once(
        self, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The teardown report's rule, after the setup report's captured
        log, has one fill character either side of its long title, and ends
        that section."""
        run, dropped, attempts = self._run(tmp_path, monkeypatch, lambda deselected: (LONG_NAME_LOG, 1))
        assert (len(attempts), dropped) == (1, [])
        assert run.error == NIGHT_ERROR


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

    def test_an_edit_that_adds_a_line_is_refused(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(md, "PRAGMA", "# pragma: no mutate block\n#")
        with pytest.raises(md.NarrowError, match="moved a line"):
            md.narrow(BASE, set())

    def test_an_edit_that_changes_a_node_is_refused(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(md, "PRAGMA", "+ 1  # pragma: no mutate block")
        with pytest.raises(md.NarrowError, match="changed a node"):
            md.narrow("def one(x): return x + 1\n", set())

    def test_an_edit_that_breaks_the_syntax_is_refused(self, monkeypatch: pytest.MonkeyPatch) -> None:
        monkeypatch.setattr(md, "PRAGMA", ")  # pragma: no mutate block")
        with pytest.raises(md.NarrowError, match="syntax"):
            md.narrow("def f(x):\n    return x\n", set())

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

    def test_extra_arguments_follow_the_repositorys(self) -> None:
        out = md.rewrite_config(PYPROJECT, only_mutate=["vera/x.py"], extra_tests=[],
                                extra_args=["--deselect=tests/test_a.py::t"])
        assert tomllib.loads(out)["tool"]["mutmut"]["pytest_add_cli_args"] == [
            "--timeout=300", "--deselect=tests/test_a.py::t"]

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
        the generated file, every function's mutants inlined, and so is each
        mutated module's text: these read it and fail there with no mutant
        active."""
        deselected = {arg.removeprefix("--deselect=") for arg in self._cfg()["pytest_add_cli_args"]
                      if arg.startswith("--deselect=")}
        reads = "tests/test_verifier_refinements.py::TestANonVerdictIsAttributedToTheRightOutcome::"
        assert deselected == {
            reads + "test_no_demotion_site_hardcodes_a_solver_reason",
            reads + "test_every_possibly_unguarded_demotion_supplies_a_reason",
            # runs scripts/check_diagnostic_fields.py over the copy's vera/,
            # where each mutant repeats its function's error codes
            "tests/test_checker_errors.py::TestErrorCodes::test_error_code_collision_gate_is_clean",
            # the presence gate over the copy's vera/, and over the copy's
            # vera/checker/registration.py with its one E188 taken off
            "tests/test_diagnostic_codes_1490.py::"
            "test_the_live_tree_carries_a_code_everywhere_and_builds_none_by_hand",
            "tests/test_diagnostic_codes_1490.py::"
            "test_mutant_a_code_removed_from_one_site_fails_the_gate",
        }

    def test_every_deselected_test_exists(self) -> None:
        args = [a for a in self._cfg()["pytest_add_cli_args"] if a.startswith("--deselect=")]
        assert args
        for arg in args:
            path, _, rest = arg.removeprefix("--deselect=").partition("::")
            assert (ROOT / path).is_file(), arg
            cls, _, name = rest.partition("::")
            text = (ROOT / path).read_text(encoding="utf-8")
            if name:
                assert f"class {cls}" in text and f"def {name}(" in text, arg
            else:  # a module-level test function
                assert f"\ndef {cls}(" in text, arg


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
# Red for a defect, green for an unfinished run (the maintainer, 2026-10-21):
# 1 on a survivor, whatever else the run did; 2 when the engine fails or
# mutmut reports a mutant the lane did not map; 0 otherwise, a run the budget
# stopped and a mutant left undecided included, which the headline reports.
DECISIONS = [
    ("every mutant killed", ["killed", "killed"], None, 0),
    ("killed and timed out", ["killed", "timeout"], None, 0),
    ("caught by the type checker", ["caught by type check"], None, 0),
    ("one survivor", ["killed", "survived"], None, 1),
    ("not observable in process", ["no tests", "no tests"], None, 0),
    ("skipped by the engine", ["skipped", "killed"], None, 0),
    ("a mutant never run", ["killed", "not checked"], None, 0),
    ("an interrupted mutant", ["check was interrupted by user"], None, 0),
    ("a suspicious exit", ["suspicious"], None, 0),
    ("a killed process", ["segfault"], None, 0),
    ("a survivor in a run cut short", ["survived", "not checked"], None, 1),
    ("the budget stopped it", ["killed"], "budget", 0),
    ("the budget stopped it with every decided mutant caught",
     ["killed", "timeout", "not checked"], "budget", 0),
    ("a survivor before the budget stopped it", ["survived", "not checked"], "budget", 1),
    ("the engine stopped it", [], "engine", 2),
    ("a survivor before the engine stopped", ["survived"], "engine", 1),
    ("a mutant the lane did not map", ["killed"], "unmapped", 2),
    ("nothing to mutate", [], None, 0),
]


class TestExitCode:
    @pytest.mark.parametrize("case", DECISIONS, ids=[c[0] for c in DECISIONS])
    def test_exit_code(self, case: tuple[Any, ...]) -> None:
        _, statuses, stopped, code = case
        results = {f"{F}{i}": s for i, s in enumerate(statuses, start=1)}
        rows = md.tally([_unit("x_free")], results) if statuses else []
        assert md.exit_code(rows, stopped=stopped) == code


class TestOutcome:
    """An exit 0 says what was decided: every mutant killed or timed out, or
    no survivor with some functions no in-process test reaches."""

    def _rows(self, results: dict[str, str], *keys: str) -> list[Any]:
        return md.tally([_unit(k) for k in keys], results)

    def test_every_mutant_caught(self) -> None:
        rows = self._rows({f"{F}1": "killed", f"{F}2": "timeout"}, "x_free")
        assert md.outcome(0, rows, None) == "Pass: every mutant of the diff is killed or timed out."

    def test_one_function_caught_and_one_not_observable(self) -> None:
        results = {f"{F}1": "killed", "vera.smt.x_far__mutmut_1": "no tests",
                   "vera.smt.x_far__mutmut_2": "no tests"}
        rows = self._rows(results, "x_free", "x_far")
        assert md.exit_code(rows, stopped=None) == 0
        assert md.outcome(0, rows, None) == (
            "Pass: no mutant survived; 2 mutant(s) in 1 function(s) not observable in process.")

    def test_no_function_observable(self) -> None:
        rows = self._rows({f"{F}1": "no tests"}, "x_free")
        assert md.outcome(0, rows, None) == (
            "Pass: no mutant survived; 1 mutant(s) in 1 function(s) not observable in process.")

    def test_a_mutant_the_engine_skipped(self) -> None:
        """mutmut 3.8 assigns no mutant the `skipped` status (exit code 34),
        so the clause is pinned on a synthetic row."""
        rows = self._rows({f"{F}1": "killed", f"{F}2": "skipped"}, "x_free")
        assert md.exit_code(rows, stopped=None) == 0
        assert md.outcome(0, rows, None) == (
            "Pass: no mutant survived; 1 mutant(s) skipped by the engine.")

    def test_a_function_with_no_mutant(self) -> None:
        rows = self._rows({f"{F}1": "killed"}, "x_free", "x_bare")
        assert md.outcome(0, rows, None) == (
            "Pass: no mutant survived; 1 function(s) with no mutant.")

    def test_a_run_the_budget_stopped_passes_and_says_it_is_incomplete(self) -> None:
        rows = self._rows({f"{F}1": "killed", f"{F}2": "timeout", f"{F}3": "not checked"},
                          "x_free")
        assert md.exit_code(rows, stopped="budget") == 0
        assert md.outcome(0, rows, "budget") == (
            "Incomplete: the budget ran out before every mutant was decided.")

    def test_a_mutant_left_undecided_passes_and_says_so(self) -> None:
        rows = self._rows({f"{F}1": "killed", f"{F}2": "segfault"}, "x_free")
        assert md.exit_code(rows, stopped=None) == 0
        assert md.outcome(0, rows, None) == "Incomplete: mutants of the diff were left undecided."

    def test_a_survivor_fails_whatever_stopped_the_run(self) -> None:
        rows = self._rows({f"{F}1": "survived", f"{F}2": "not checked"}, "x_free")
        assert md.outcome(1, rows, None) == "Fail: 1 mutant(s) of the diff survive."
        assert md.outcome(1, rows, "budget") == (
            "Fail: 1 mutant(s) of the diff survive; the budget ran out before every "
            "mutant was decided.")

    def test_only_an_unfinished_pass_is_annotated(self) -> None:
        """A green check whose run did not finish carries a warning on the
        pull request; a red one, or a finished pass, says nothing more."""
        incomplete = self._rows({f"{F}1": "killed", f"{F}2": "not checked"}, "x_free")
        assert md.annotation(0, md.outcome(0, incomplete, "budget")) == (
            "::warning title=mutation (diff)::Incomplete: the budget ran out before every "
            "mutant was decided.")
        finished = self._rows({f"{F}1": "killed"}, "x_free")
        assert md.annotation(0, md.outcome(0, finished, None)) is None
        survivor = self._rows({f"{F}1": "survived"}, "x_free")
        assert md.annotation(1, md.outcome(1, survivor, "budget")) is None
        assert md.annotation(2, md.outcome(2, finished, "engine")) is None


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


class TestOraclePlugin:
    """`tests/mutation_oracle.py`, the pytest plugin `[tool.mutmut]` loads."""

    def test_a_test_that_starts_a_python_process_is_skipped_and_recorded(self, tmp_path: Path) -> None:
        (tmp_path / "test_planted.py").write_text(
            "import subprocess, sys\n\n\n"
            "def test_starts_python():\n"
            "    subprocess.run([sys.executable, '-c', 'pass'], check=True)\n\n\n"
            "def test_starts_git():\n"
            "    subprocess.run(['git', '--version'], check=True, capture_output=True)\n\n\n"
            "def test_in_process():\n"
            "    assert sum([1, 1]) == 2\n", encoding="utf-8")
        skips = tmp_path / "skips.txt"
        env = {k: v for k, v in os.environ.items()
               if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE", "PYTEST_ADDOPTS")}
        env.update(PYTHONPATH=str(ROOT), MUTATION_ORACLE_SKIPS=str(skips))
        result = subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "-p", "tests.mutation_oracle", "-p", "no:cacheprovider",
             "-o", "addopts=", "test_planted.py"],
            cwd=tmp_path, env=env, capture_output=True, text=True, encoding="utf-8", check=False)
        assert "2 passed, 1 skipped" in result.stdout, result.stdout + result.stderr
        assert skips.read_text(encoding="utf-8").splitlines() == ["test_planted.py::test_starts_python"]

    def test_a_test_a_cached_fixture_skips_is_recorded_too(self, tmp_path: Path) -> None:
        """A module-scoped fixture that starts Python skips the test that
        set it up, and pytest hands the same skip to every later test that
        uses it, which starts no process itself: each is the plugin's."""
        (tmp_path / "test_planted.py").write_text(
            "import subprocess, sys\n\nimport pytest\n\n\n"
            "@pytest.fixture(scope='module')\n"
            "def built():\n"
            "    subprocess.run([sys.executable, '-c', 'pass'], check=True)\n\n\n"
            "def test_first(built):\n    pass\n\n\n"
            "def test_second(built):\n    pass\n", encoding="utf-8")
        skips = tmp_path / "skips.txt"
        env = {k: v for k, v in os.environ.items()
               if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE", "PYTEST_ADDOPTS")}
        env.update(PYTHONPATH=str(ROOT), MUTATION_ORACLE_SKIPS=str(skips))
        result = subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "-p", "tests.mutation_oracle", "-p", "no:cacheprovider",
             "-o", "addopts=", "test_planted.py"],
            cwd=tmp_path, env=env, capture_output=True, text=True, encoding="utf-8", check=False)
        assert "2 skipped" in result.stdout, result.stdout + result.stderr
        assert skips.read_text(encoding="utf-8").splitlines() == [
            "test_planted.py::test_first", "test_planted.py::test_second"]

    def test_the_repository_config_loads_it(self) -> None:
        args = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))["tool"]["mutmut"][
            "pytest_add_cli_args"]
        i = args.index("-p")
        assert args[i + 1] == "tests.mutation_oracle"

    def test_a_skipped_test_leaves_the_record_under_mutmuts_name_for_it(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """mutmut records a test by its node id with any `mutants/` prefix
        stripped; the plugin takes it out under that name too."""
        pytest.importorskip("mutmut")
        from mutmut.state import state

        from tests import mutation_oracle

        record = state().tests_by_mangled_function_name
        monkeypatch.setattr(state(), "tests_by_mangled_function_name", type(record)(set))
        state().tests_by_mangled_function_name["pkg.m.x_f"] |= {"tests/test_m.py::test_a", "tests/test_m.py::test_b"}
        monkeypatch.setenv("MUTANT_UNDER_TEST", "stats")
        mutation_oracle._forget("mutants/tests/test_m.py::test_a")
        assert state().tests_by_mangled_function_name["pkg.m.x_f"] == {"tests/test_m.py::test_b"}

    def test_a_mutmut_without_the_record_stops_the_stats_pass(self, monkeypatch: pytest.MonkeyPatch) -> None:
        """Where mutmut keeps no `mutmut.state`, the plugin cannot take a
        skipped test out of the record, so it stops the run rather than leave
        the test there."""
        from tests import mutation_oracle

        monkeypatch.setitem(sys.modules, "mutmut.state", None)  # importing it raises ImportError
        monkeypatch.setenv("MUTANT_UNDER_TEST", "stats")
        with pytest.raises(pytest.exit.Exception):
            mutation_oracle._forget("tests/test_m.py::test_a")

    def test_a_skipped_test_is_no_oracle_for_the_functions_it_reached_first(self, tmp_path: Path) -> None:
        """mutmut's stats pass records, at each test's teardown and whatever
        its outcome, the functions the test reached.  A test the plugin skips
        after calling a mutated function must leave no such record, or mutmut
        runs it against that function's mutants, it skips again, and each
        mutant reads as a survivor where it is `no tests`."""
        pytest.importorskip("mutmut")
        engine = Path(sys.executable).with_name("mutmut")
        project = tmp_path / "project"
        (project / "pkg").mkdir(parents=True)
        (project / "tests").mkdir()
        (project / "pkg" / "__init__.py").write_text("", encoding="utf-8")
        (project / "pkg" / "m.py").write_text(
            "def reached_then_skipped(x):\n    return x + 1\n\n\n"
            "def reached_in_process(x):\n    return x * 2\n", encoding="utf-8")
        (project / "tests" / "__init__.py").write_text("", encoding="utf-8")
        (project / "tests" / "mutation_oracle.py").write_text(
            (ROOT / "tests" / "mutation_oracle.py").read_text(encoding="utf-8"), encoding="utf-8")
        (project / "tests" / "test_m.py").write_text(
            "import subprocess, sys\n\n"
            "from pkg.m import reached_in_process, reached_then_skipped\n\n\n"
            "def test_calls_then_starts_python():\n"
            "    reached_then_skipped(1)\n"
            "    subprocess.run([sys.executable, '-c', 'pass'], check=True)\n\n\n"
            "def test_in_process():\n"
            "    assert reached_in_process(3) == 6\n", encoding="utf-8")
        (project / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["pkg/"]\nuse_setproctitle = false\n'
            'pytest_add_cli_args = ["-p", "tests.mutation_oracle", "-p", "no:cacheprovider"]\n'
            'pytest_add_cli_args_test_selection = ["tests/"]\n', encoding="utf-8")
        skips = tmp_path / "skips.txt"
        env = {k: v for k, v in os.environ.items()
               if k not in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE", "PYTEST_ADDOPTS",
                            "MUTANT_UNDER_TEST")}
        env.update(PYTHONDONTWRITEBYTECODE="1", MUTATION_ORACLE_SKIPS=str(skips))
        run = subprocess.run([str(engine), "run", "--max-children", "2"], cwd=project, env=env,
                             capture_output=True, text=True, encoding="utf-8", check=False, timeout=600)
        listed = subprocess.run([str(engine), "results", "--all", "true"], cwd=project, env=env,
                                capture_output=True, text=True, encoding="utf-8", check=False,
                                timeout=300)
        statuses = md.parse_results(listed.stdout)
        by_function: dict[str, set[str]] = {}
        for name, status in statuses.items():
            by_function.setdefault(md.unit_of_mutant(name)[1], set()).add(status)
        assert by_function == {"x_reached_then_skipped": {"no tests"}, "x_reached_in_process": {"killed"}}, (
            run.stdout + run.stderr)
        # Recorded each time it skips (the stats pass, the forced-fail run); the lane lists it once.
        assert set(skips.read_text(encoding="utf-8").splitlines()) == {
            "tests/test_m.py::test_calls_then_starts_python"}


# ---------------------------------------------------------------------------
# End to end, against a stand-in engine
# ---------------------------------------------------------------------------


FAKE_ENGINE = '''
import json, os, sys
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
args = sys.argv[1:]
log = state / "calls.jsonl"
window_file = os.environ.get("MUTATE_DIFF_WINDOW")
window = json.loads(Path(window_file).read_text(encoding="utf-8")) if window_file else None
with log.open("a", encoding="utf-8") as fh:
    fh.write(json.dumps({"cwd": os.getcwd(), "args": args, "window": window,
                         "git_dir": os.environ.get("GIT_DIR"),
                         "columns": os.environ.get("COLUMNS")}) + "\\n")
if args[0] == "run" and window is not None and not os.environ.get("FAKE_NO_WINDOW"):
    # As the engine launcher does: each unit's mutants on every line and in
    # the window, here the mutants results.txt lists for it unless the test
    # names the counts.
    counts = json.loads(os.environ.get("FAKE_WINDOW_COUNTS", "null"))
    if counts is None:
        counts = {}
        listed = (state / "results.txt").read_text(encoding="utf-8").split()
        for path in window["lines"]:
            module = path[:-3].replace("/", ".")
            for token in listed:
                name = token.rstrip(":")
                if name.startswith(module + ".") and "__mutmut_" in name:
                    key = name.partition("__mutmut_")[0][len(module) + 1:]
                    unit = counts.setdefault(path, {}).setdefault(key, {"held": 0, "window": 0})
                    unit["held"] += 1
                    unit["window"] += 1
    Path(window["record"]).write_text(json.dumps({"files": counts}), encoding="utf-8")
if args[0] == "run" and os.environ.get("FAKE_RUN_LOG"):
    # A log the engine printed, as it printed it (its stats pass stopping),
    # and, once FAKE_RUN_LOG_AFTER's test (before its `|`) is deselected,
    # the log after it.
    printed = os.environ["FAKE_RUN_LOG"]
    test, _, after = os.environ.get("FAKE_RUN_LOG_AFTER", "").partition("|")
    if test and f"--deselect={test}" in Path("pyproject.toml").read_text(encoding="utf-8"):
        printed = after
    print(Path(printed).read_text(encoding="utf-8"), end="")
    sys.exit(1)
if args[0] == "run":
    failing = os.environ.get("FAKE_COPY_FAILURE", "")
    config = Path("pyproject.toml").read_text(encoding="utf-8")
    if failing and (os.environ.get("FAKE_COPY_FAILURE_STICKY") or f"--deselect={failing}" not in config):
        print("Running stats")
        print(f"FAILED {failing} - FileNotFoundError: [Errno 2] No such file or directory: 'CHANGELOG.md'")
        print("failed to collect stats. runner returned 1")
        sys.exit(1)
    skipped = os.environ.get("FAKE_ORACLE_SKIPS", "")
    if skipped and os.environ.get("MUTATION_ORACLE_SKIPS"):
        with open(os.environ["MUTATION_ORACLE_SKIPS"], "a", encoding="utf-8") as fh:
            fh.write("".join(f"{nodeid}\\n" for nodeid in skipped.split(",")))
    print(os.environ.get("FAKE_RUN_OUTPUT", ""), flush=True)
    if os.environ.get("FAKE_RUN_SLEEP"):
        import time
        time.sleep(float(os.environ["FAKE_RUN_SLEEP"]))
    sys.exit(int(os.environ.get("FAKE_RUN_EXIT", "0")))
if args[0] == "results":
    import time
    time.sleep(float(os.environ.get("FAKE_RESULTS_SLEEP", "0")))
    sys.stdout.write((state / "results.txt").read_text(encoding="utf-8"))
    sys.exit(int(os.environ.get("FAKE_RESULTS_EXIT", "0")))
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
          run_output: str = "", workdir: str | None = None,
          budget: float | None = None,
          ) -> tuple[int, dict[str, Any], list[dict[str, Any]]]:
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
            "--workdir", workdir or str(tmp_path / "work"), "--json", str(out_json),
            "--summary", str(tmp_path / "summary.md"),
            "--engine", sys.executable, str(engine),
            *(["--budget", str(budget)] if budget is not None else []),
        ])
    finally:
        del os.environ["FAKE_STATE"], os.environ["FAKE_RUN_EXIT"], os.environ["FAKE_RUN_OUTPUT"]
    log = state / "calls.jsonl"
    calls = ([json.loads(line) for line in log.read_text(encoding="utf-8").splitlines()]
             if log.exists() else [])
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

    def test_the_engines_run_is_handed_the_window_alone(self, repo: Path, tmp_path: Path) -> None:
        """The run is handed each narrowed file's window, inside the units
        the diff changes: `kept` spans lines 1 and 2, and the edit is line 2.
        `results` and `show` are not."""
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["window"]["lines"] == {"vera/m.py": [1, 2]} and run["window"]["context"] == 2
        assert all(c["window"] is None for c in calls if c["args"][0] != "run")
        assert record["window"]["lines"] == {"vera/m.py": [1, 2]}

    def test_the_engine_is_handed_eighty_columns_whatever_the_lanes_terminal(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """pytest draws its rules the terminal's width, and engine_failure
        knows a rule by that width: a narrow terminal's COLUMNS stops here."""
        monkeypatch.setenv("COLUMNS", "60")
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["columns"] == "80"

    def test_a_one_line_edit_in_a_long_function_hands_the_engine_its_lines(
        self, tmp_path: Path,
    ) -> None:
        """The lane's case: one line edited in the middle of a long function.
        The engine is handed the two lines either side of the edit, not the
        function's other lines."""
        root = tmp_path / "long"
        (root / "vera").mkdir(parents=True)
        (root / "pyproject.toml").write_text(
            '[tool.mutmut]\nsource_paths = ["vera/"]\n', encoding="utf-8")
        body = [f"    v{i} = x + {i}" for i in range(1, 20)]
        (root / "vera" / "m.py").write_text(
            "def long(x):\n" + "\n".join(body) + "\n    return x\n", encoding="utf-8")
        _git(root, "init", "-q", "-b", "main")
        _git(root, "add", "-A")
        _git(root, "commit", "-q", "-m", "base")
        body[9] = "    v10 = x - 10"  # line 11
        (root / "vera" / "m.py").write_text(
            "def long(x):\n" + "\n".join(body) + "\n    return x\n", encoding="utf-8")
        _git(root, "commit", "-q", "-am", "head")
        code, record, calls = _main(root, tmp_path, "    vera.m.x_long__mutmut_1: killed\n")
        assert code == 0
        (run,) = [c for c in calls if c["args"][0] == "run"]
        assert run["window"]["lines"] == {"vera/m.py": [9, 10, 11, 12, 13]}

    def test_an_engine_that_counted_no_window_stops_the_run_short(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """Nothing says what such an engine generated was the window's, so
        the run is the engine's failure, exit 2, whatever it decided."""
        monkeypatch.setenv("FAKE_NO_WINDOW", "1")
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert (code, record["stopped"]) == (2, "engine")
        assert "no count of the window" in record["window"]["error"]
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert "Not checked: the engine wrote no count of the window" in summary

    def test_mutants_outside_the_window_stop_the_run_short(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A unit whose generated mutants outnumber its window's was not
        generated through the window: exit 2, the unit named."""
        monkeypatch.setenv("FAKE_WINDOW_COUNTS",
                           json.dumps({"vera/m.py": {"x_kept": {"held": 5, "window": 1}}}))
        results = "    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: killed\n"
        code, record, _ = _main(repo, tmp_path, results)
        assert (code, record["stopped"]) == (2, "unmapped")
        assert record["outside_window"] == ["`vera/m.py` `kept`: 2 generated, 1 in the window"]

    def test_fewer_mutants_than_the_window_stop_the_run_short(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A unit mutmut generated with fewer mutants than its window holds
        was not generated through the window either: exit 2, the unit named,
        and the summary says the counts differ."""
        monkeypatch.setenv("FAKE_WINDOW_COUNTS",
                           json.dumps({"vera/m.py": {"x_kept": {"held": 5, "window": 3}}}))
        results = "    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: killed\n"
        code, record, _ = _main(repo, tmp_path, results)
        assert (code, record["stopped"]) == (2, "unmapped")
        assert record["outside_window"] == ["`vera/m.py` `kept`: 2 generated, 3 in the window"]
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert ("functions whose generated mutants differ in number from their window's, which "
                "stops the run short: `vera/m.py` `kept`: 2 generated, 3 in the window") in summary

    def test_a_unit_the_run_did_not_reach_is_not_judged_by_the_window(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The nearest accepted neighbour: a run the budget stopped before it
        generated a unit lists none of its mutants, which says nothing about
        the window; the run is incomplete, and green."""
        monkeypatch.setenv("FAKE_WINDOW_COUNTS",
                           json.dumps({"vera/m.py": {"x_kept": {"held": 5, "window": 2}}}))
        monkeypatch.setenv("FAKE_RUN_SLEEP", "5")
        code, record, _ = _main(repo, tmp_path, "", budget=1)
        assert (code, record["stopped"], record["outside_window"]) == (0, "budget", [])

    def test_the_summary_names_the_rule_and_what_it_measured(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The counts the next measurement of the lane needs: the functions
        selected, their mutants and the window's, what mutmut generated and
        decided, and the survivors."""
        monkeypatch.setenv("FAKE_WINDOW_COUNTS",
                           json.dumps({"vera/m.py": {"x_kept": {"held": 5, "window": 2}}}))
        results = "    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: survived\n"
        code, record, _ = _main(repo, tmp_path, results)
        assert code == 1
        assert record["window"]["selection"] == {
            "functions": 1, "held": 5, "window": 2, "generated": 2, "decided": 2, "survived": 1}
        assert [(f["held"], f["window"]) for f in record["functions"]] == [(5, 2)]
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert ("Selection: the mutants whose node starts within 2 lines of a line the diff adds "
                "or of a point where it removes lines, or on the first line of a call, match, "
                "assignment, operation, comparison, conditional expression or lambda that spans "
                "one of those lines. 1 function(s) hold 5 mutant(s), 2 of them in the window; "
                "mutmut generated 2, decided 2, and 1 survived.") in summary

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
        assert record["outcome"] == (
            "Pass: no mutant survived; 1 mutant(s) in 1 function(s) not observable in process.")
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

    def test_a_developers_diff_prefix_config_does_not_change_the_mapping(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        """`diff.noprefix` drops the `a/` and `b/` the diff parse reads, so the
        lane names its prefixes on the `git diff` call."""
        _git(repo, "config", "diff.noprefix", "true")
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0
        assert [f["qualname"] for f in record["functions"]] == ["kept"]

    def _plant_a_tree_reading_test(self, repo: Path) -> str:
        (repo / "tests" / "test_reads_tree.py").write_text(
            "import vera\nfrom pathlib import Path\n\n\ndef test_reads():\n"
            "    assert Path('CHANGELOG.md').read_text(encoding='utf-8')\n", encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "--amend", "--no-edit")
        return "tests/test_reads_tree.py::test_reads"

    def test_a_test_that_fails_in_the_copy_is_dropped_reported_and_the_run_completes(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A test that cannot pass inside mutmut's copy with no mutant active
        (here one that reads a file the copy lacks) is no oracle there: the
        lane drops it, runs again, and names it in the summary and record."""
        failing = self._plant_a_tree_reading_test(repo)
        monkeypatch.setenv("FAKE_COPY_FAILURE", failing)
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0 and record["stopped"] is None
        assert record["dropped_tests"] == [failing]
        assert "tests/test_reads_tree.py" in record["extra_tests"]
        assert len([c for c in calls if c["args"][0] == "run"]) == 2
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert f"`{failing}`" in summary and "Dropped from the oracle" in summary

    def test_a_test_that_starts_a_process_is_kept_out_and_reported(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The plugin skips, inside mutmut's copy, a test that starts a Python
        or `vera` process and records it; the lane names each one, once."""
        planted = "tests/test_cli_like.py::test_runs_the_cli"
        spaced = "tests/test_cli_like.py::test_runs_the_cli[a b]"  # a parametrised id
        monkeypatch.setenv("FAKE_ORACLE_SKIPS", f"{planted},{spaced},{planted}")
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 0 and record["stopped"] is None
        assert record["subprocess_tests"] == [planted, spaced]
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert f"`{planted}`" in summary and "Not oracles in mutmut's copy" in summary

    def test_a_relative_workdir_still_collects_the_skipped_tests(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The engine runs in the scratch tree, so the skips file it is
        handed must not be relative to the lane's own directory."""
        planted = "tests/test_cli_like.py::test_runs_the_cli"
        monkeypatch.setenv("FAKE_ORACLE_SKIPS", planted)
        monkeypatch.chdir(tmp_path)
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n", workdir="work")
        assert code == 0 and record["stopped"] is None
        assert record["subprocess_tests"] == [planted]
        assert Path(record["workdir"]).is_absolute()

    def test_a_drop_that_does_not_take_stops_the_run_short(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        failing = self._plant_a_tree_reading_test(repo)
        monkeypatch.setenv("FAKE_COPY_FAILURE", failing)
        monkeypatch.setenv("FAKE_COPY_FAILURE_STICKY", "1")
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: not checked\n")
        assert code == 2 and record["stopped"] == "engine"
        assert record["dropped_tests"] == [failing]
        assert len([c for c in calls if c["args"][0] == "run"]) == 2

    def test_the_engines_own_failure_is_named_and_drops_no_test(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The night's log: every test errors at teardown in mutmut's own
        hook.  The run stops at its first attempt, red, and the record and
        the summary name the exception and the engine's frame."""
        log = tmp_path / "night.log"
        log.write_text(NIGHT_LOG, encoding="utf-8")
        monkeypatch.setenv("FAKE_RUN_LOG", str(log))
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: not checked\n")
        assert (record["dropped_tests"], len([c for c in calls if c["args"][0] == "run"])) == ([], 1)
        assert code == 2 and record["stopped"] == "engine" and record["engine_error"] == NIGHT_ERROR
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert f"Stopped by the engine: `{NIGHT_ERROR}`." in summary
        assert "Dropped from the oracle" not in summary

    def test_an_engine_failure_after_a_drop_keeps_the_drop_and_claims_no_other(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """A test fails in its own body on the first attempt and is dropped;
        the second attempt meets the night's engine failure.  The record keeps
        the drop beside the error, and the summary claims nothing the drop
        contradicts."""
        body, night = tmp_path / "body.log", tmp_path / "night.log"
        body.write_text(BODY_FAILURE_LOG, encoding="utf-8")
        night.write_text(NIGHT_LOG, encoding="utf-8")
        monkeypatch.setenv("FAKE_RUN_LOG", str(body))
        monkeypatch.setenv("FAKE_RUN_LOG_AFTER", f"tests/test_m.py::test_g|{night}")
        code, record, calls = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: not checked\n")
        assert (record["dropped_tests"], len([c for c in calls if c["args"][0] == "run"])) == (
            ["tests/test_m.py::test_g"], 2)
        assert code == 2 and record["stopped"] == "engine" and record["engine_error"] == NIGHT_ERROR
        summary = (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert f"Stopped by the engine: `{NIGHT_ERROR}`." in summary
        assert "Dropped from the oracle" in summary and "- `tests/test_m.py::test_g`" in summary
        assert "no test was dropped" not in summary

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

    def test_a_run_the_budget_stops_with_no_survivor_passes_with_a_warning(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """#1753's final head: the budget ran out with every decided mutant
        killed or timed out and the rest not checked.  The check passes, and
        the summary and an annotation say the run did not finish."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "60")
        results = ("    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: timeout\n"
                   "    vera.m.x_kept__mutmut_3: not checked\n")
        code, record, _ = _main(repo, tmp_path, results, budget=1)
        out = capsys.readouterr().out
        assert (code, record["exit_code"], record["stopped"]) == (0, 0, "budget")
        headline = "Incomplete: the budget ran out before every mutant was decided."
        assert record["outcome"] == headline
        assert f"**{headline}**" in (tmp_path / "summary.md").read_text(encoding="utf-8")
        assert f"::warning title=mutation (diff)::{headline}" in out.splitlines()

    def test_a_survivor_the_budget_cut_short_fails(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        monkeypatch.setenv("FAKE_RUN_SLEEP", "60")
        results = "    vera.m.x_kept__mutmut_1: survived\n    vera.m.x_kept__mutmut_2: not checked\n"
        code, record, _ = _main(repo, tmp_path, results, budget=1)
        assert (code, record["exit_code"], record["stopped"]) == (1, 1, "budget")
        assert record["outcome"].startswith("Fail: 1 mutant(s) of the diff survive")
        assert "::warning" not in capsys.readouterr().out

    @pytest.mark.parametrize(
        ("results", "env", "code", "stopped"),
        [
            pytest.param("    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: not checked\n",
                         {"FAKE_RESULTS_SLEEP": "30"}, 2, "engine", id="a hung results call"),
            pytest.param("    vera.m.x_kept__mutmut_1: survived\n",
                         {"FAKE_RESULTS_EXIT": "1"}, 2, "engine",
                         id="a failing results call that lists a survivor"),
            pytest.param("    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_kept__mutmut_2: survived by proxy\n",
                         {}, 2, "engine", id="results the lane cannot read"),
            pytest.param("    vera.m.x_kept__mutmut_1: killed\n    vera.m.x_other__mutmut_1: survived\n",
                         {}, 2, "unmapped", id="a survivor of a function the lane did not map"),
            pytest.param("    vera.m.x_kept__mutmut_1: survived\n    vera.m.x_other__mutmut_1: killed\n",
                         {}, 1, "unmapped", id="a survivor of the diff and an unmapped mutant"),
        ],
    )
    def test_a_failure_after_the_budget_ran_out_is_still_red(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
        capsys: pytest.CaptureFixture[str], results: str, env: dict[str, str], code: int,
        stopped: str,
    ) -> None:
        """The budget leaves a run only incomplete.  A failure of the engine
        or of the mapping found after it outranks it, so the run is red, as
        the same failure is with no budget stop; a survivor of the diff
        outranks both."""
        monkeypatch.setenv("FAKE_RUN_SLEEP", "60")
        if "FAKE_RESULTS_SLEEP" in env:
            monkeypatch.setattr(md, "ENGINE_CALL_TIMEOUT_S", 1)
        for name, value in env.items():
            monkeypatch.setenv(name, value)
        got, record, _ = _main(repo, tmp_path, results, budget=1)
        assert (got, record["exit_code"], record["stopped"]) == (code, code, stopped)
        assert "::warning" not in capsys.readouterr().out

    def test_a_finished_run_carries_no_warning(
        self, repo: Path, tmp_path: Path, capsys: pytest.CaptureFixture[str],
    ) -> None:
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert (code, record["stopped"]) == (0, None)
        assert record["outcome"] == "Pass: every mutant of the diff is killed or timed out."
        assert "::warning" not in capsys.readouterr().out

    def test_a_status_the_lane_does_not_model_stops_the_run_short(
        self, repo: Path, tmp_path: Path,
    ) -> None:
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: survived by proxy\n")
        assert code == 2 and record["stopped"] == "engine"
        assert "survived by proxy" in record["engine_tail"][0]

    def test_a_failing_results_call_stops_the_run_short(
        self, repo: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        monkeypatch.setenv("FAKE_RESULTS_EXIT", "1")
        code, record, _ = _main(repo, tmp_path, "    vera.m.x_kept__mutmut_1: killed\n")
        assert code == 2 and record["stopped"] == "engine"

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

    def test_it_runs_on_a_pull_request_that_changes_the_compiler_the_engine_or_either_lane(self) -> None:
        """The compiler, the lock that names the engine, and each lane's
        workflow, script and self-tests: a lock bump that breaks the engine
        is red on its own pull request, before any night runs on it."""
        on = self._wf()[True]  # YAML 1.1 reads the bare key `on` as True
        assert set(on) == {"pull_request"}
        assert on["pull_request"]["paths"] == [
            "vera/**/*.py", "uv.lock",
            "scripts/mutate_diff.py", "scripts/mutate_sweep.py", "scripts/mutation_report.py",
            "tests/mutation_oracle.py", "tests/test_mutate_diff.py", "tests/test_mutate_sweep.py",
            ".github/workflows/mutation-diff.yml", ".github/workflows/mutation-nightly.yml"]

    def test_every_script_a_lane_loads_is_in_the_filter(self) -> None:
        """A lane's scripts and every sibling script they import, as
        ``scripts/mutate_sweep.py`` imports ``scripts/mutation_report.py`` at
        load (the stitch writes the badge with it)."""
        paths = set(self._wf()[True]["pull_request"]["paths"])
        loaded: set[str] = set()
        todo = ["scripts/mutate_diff.py", "scripts/mutate_sweep.py"]
        while todo:
            script = todo.pop()
            if script not in loaded:
                loaded.add(script)
                text = (ROOT / script).read_text(encoding="utf-8")
                todo += [f"scripts/{name}.py" for name in re.findall(r"^(?:from|import) (\w+)", text, re.M)
                         if (ROOT / "scripts" / f"{name}.py").exists()]
        assert "scripts/mutation_report.py" in loaded
        assert loaded <= paths, sorted(loaded - paths)

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

    def test_it_runs_python_312_and_both_lanes_self_tests_before_the_script(self) -> None:
        """The install is uv.lock's (``test_mutate_sweep.py``'s
        ``test_the_engine_installed_is_uv_locks`` holds both lanes to it);
        here the self-tests of both lanes run against it, as the nightly's
        do, before the script."""
        steps = self._job()["steps"]
        (setup,) = [s for s in steps if str(s.get("uses", "")).startswith("actions/setup-python@")]
        assert setup["with"]["python-version"] == "3.12"
        names = [s.get("name") for s in steps]
        (test,) = [s for s in steps if s.get("name") == "Test the lane against the engine it installs"]
        assert test["run"] == "pytest tests/test_mutate_sweep.py tests/test_mutate_diff.py -q"
        assert names.index("Install dependencies") < names.index(test["name"]) < names.index(
            "Mutate the functions this pull request changes")

    def test_the_script_runs_against_the_merge_base_inside_its_budget(self) -> None:
        job = self._job()
        (step,) = [s for s in job["steps"] if "scripts/mutate_diff.py" in s.get("run", "")]
        assert "${{" not in step["run"], "context values reach the shell through env only"
        assert step["env"]["BASE_SHA"] == "${{ github.event.pull_request.base.sha }}"
        assert step["env"]["HEAD_SHA"] == "${{ github.event.pull_request.head.sha }}"
        budget = int(re.search(r"--budget (\d+)", step["run"]).group(1))  # type: ignore[union-attr]
        assert job["timeout-minutes"] * 60 >= budget + 10 * 60
        assert "continue-on-error" not in job and "continue-on-error" not in step

    def test_no_step_reads_the_scripts_exit_status(self) -> None:
        """The job's status is the script's exit status and nothing else:
        no step's condition reads the script's outcome, so an exit 0 from an
        incomplete run is a green check and an exit 1 or 2 a red one."""
        steps = self._job()["steps"]
        conditions = [str(s["if"]) for s in steps if "if" in s]
        assert conditions == ["always()"]
        assert not [s for s in steps if "continue-on-error" in s]

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


def test_tail_keeps_the_head_of_a_fault_dump(tmp_path: Path) -> None:
    """A fault dump's first lines name the dying test; the window keeps them beside the last lines (#1745)."""
    log = tmp_path / "engine.log"
    rows = [f"row {n}" for n in range(100)]
    rows[30] = "Fatal Python error: Illegal instruction"
    rows[31] = "Current thread 0x1 (most recent call first):"
    rows[32] = '  File "tests/test_x.py", line 7 in test_trap'
    log.write_text("\n".join(rows) + "\n", encoding="utf-8")
    kept = md._tail(log)
    assert kept[0] == rows[30] and kept[2] == rows[32] and kept[-1] == "row 99" and len(kept) == 40
    # mutmut's spinner writes its status without a newline, so the dump's
    # first line shares a row with it (#1747).
    glued = tmp_path / "glued.log"
    rows[30] = "\r⠋ Running clean tests Fatal Python error: Illegal instruction"
    glued.write_text("\n".join(rows) + "\n", encoding="utf-8")
    kept = md._tail(glued)
    assert kept[0] == "Fatal Python error: Illegal instruction" and kept[2] == rows[32] and len(kept) == 40
    plain = tmp_path / "plain.log"
    plain.write_text("\n".join(rows[40:]) + "\n", encoding="utf-8")
    assert md._tail(plain) == rows[60:]
