"""Tests for the Vera type checker — modules (module calls, cross-module typing, visibility, builtin redefinition).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from pathlib import Path

import pytest

from vera import ast
from vera.checker import typecheck
from vera.errors import Diagnostic, ParseError
from vera.parser import parse_to_ast
from vera.resolver import ResolvedModule

from tests.checker_helpers import (
    _check_err,
    _check_ok,
    _errors,
)
from tests.module_fixture_helpers import (
    fake_resolved_module,
    resolved_module,
)
from tests.module_fixture_helpers import (
    fake_resolved_module as _resolved_module,
)


class TestModuleFixtureBuilders:
    """The contract `tests/module_fixture_helpers.py` documents (#1228).

    Both builders delete/never create the file their `file_path` names,
    which is safe only because nothing downstream reopens it — the
    checker and `compile()` work off the parsed program and the
    in-memory source.  The docstrings said `resolved_module` produced "a
    file the pipeline can open", which was never true after the unlink
    (PR #1282 review); this pins what IS true, so the wording cannot
    drift back.
    """

    SRC = (
        "module m;\n"
        "\n"
        "public fn f(@Int -> @Int)\n"
        "  requires(true) ensures(true) effects(pure)\n"
        "{ @Int.0 }\n"
    )

    def test_neither_builder_leaves_a_file_behind(self) -> None:
        real = resolved_module(("m",), self.SRC)
        fake = fake_resolved_module(("m",), self.SRC)
        assert not real.file_path.exists(), real.file_path
        assert not fake.file_path.exists(), fake.file_path

    def test_a_failed_write_leaves_no_temp_file(
        self, monkeypatch: pytest.MonkeyPatch,
    ) -> None:
        """The cleanup contract holds even when the write fails.

        `delete=False` means the file outlives the context manager, so
        anything raising between its creation and the `try` that removes
        it stranded the file — the one case the contract's own docstring
        promised could not happen (PR #1282 review).  A non-`str` source
        makes `f.write` raise inside that window without mocking.

        The evidence is the ONE path this call created — captured from
        `NamedTemporaryFile`, the way the sibling test below captures
        handles — and NOT a sweep of `gettempdir()` for `*.vera`.  The
        sweep read a directory this process does not own: under
        `pytest-xdist` every worker builds its fixtures in the same
        system temp dir, so a sibling worker's `tmp*.vera`, alive for
        the microseconds between this test's snapshot and its
        assertion, was counted as a file this test stranded.  It was —
        `AssertionError` over a `C:\\...\\tmp*.vera` on worker gw1 in
        the v0.1.10 release push, an hour after the identical tree
        passed, and reproducible on macOS at ~33%.  A name this call
        captured cannot name another worker's file, so the race is gone
        rather than relocated: no shared directory is read at all.
        """
        from tests import module_fixture_helpers as helpers

        real_ntf = helpers.tempfile.NamedTemporaryFile
        created: list[str] = []

        def recording_ntf(*a: object, **kw: object) -> object:
            handle = real_ntf(*a, **kw)  # type: ignore[arg-type]
            created.append(handle.name)
            return handle

        # `helpers` resolves `NamedTemporaryFile` through the `tempfile`
        # module at call time, so patching the attribute intercepts its
        # creation; `monkeypatch` restores it at teardown.
        monkeypatch.setattr(
            helpers.tempfile, "NamedTemporaryFile", recording_ntf,
        )
        with pytest.raises(TypeError):
            helpers.resolved_module(("m",), object())  # type: ignore[arg-type]

        # Exactly one, or the builder no longer creates its file through
        # `NamedTemporaryFile` and the survivor check below would be
        # asserting over an empty list — green for the wrong reason.
        assert len(created) == 1, created
        stranded = [n for n in created if Path(n).exists()]
        for name in stranded:  # don't become the litter being tested for
            Path(name).unlink(missing_ok=True)
        assert stranded == [], stranded

    def test_the_handle_is_closed_before_every_unlink(self) -> None:
        """Windows cannot delete a file whose handle is still open.

        The failure-path cleanup added for the leak sat INSIDE the
        `with`, so on Windows it raised `PermissionError` (WinError 32)
        instead of removing anything — green on POSIX, red on all three
        Windows cells (PR #1282 CI).  The property is an ordering, and
        an ordering is observable here: record whether the handle is
        closed at the moment each unlink is issued, on both paths.  A
        cleanup that runs too early shows `closed=False` and would raise
        there.
        """
        import pathlib as _pathlib
        import tempfile as _tempfile

        from tests import module_fixture_helpers as helpers

        real_ntf = _tempfile.NamedTemporaryFile
        real_unlink = _pathlib.Path.unlink
        handles: list[object] = []
        closed_at_unlink: list[bool] = []

        def traced_ntf(*a: object, **kw: object) -> object:
            handle = real_ntf(*a, **kw)  # type: ignore[arg-type]
            handles.append(handle)
            return handle

        def traced_unlink(
            self: _pathlib.Path, *a: object, **kw: object,
        ) -> None:
            closed_at_unlink.append(
                all(h.closed for h in handles),  # type: ignore[attr-defined]
            )
            real_unlink(self, *a, **kw)  # type: ignore[arg-type]

        helpers.tempfile.NamedTemporaryFile = traced_ntf  # type: ignore[assignment]
        _pathlib.Path.unlink = traced_unlink  # type: ignore[assignment,method-assign]
        try:
            handles.clear()
            closed_at_unlink.clear()
            helpers.resolved_module(("m",), "module m;\n")
            success = list(closed_at_unlink)

            handles.clear()
            closed_at_unlink.clear()
            with pytest.raises(TypeError):
                helpers.resolved_module(("m",), object())  # type: ignore[arg-type]
            failure = list(closed_at_unlink)
        finally:
            helpers.tempfile.NamedTemporaryFile = real_ntf  # type: ignore[assignment]
            _pathlib.Path.unlink = real_unlink  # type: ignore[method-assign]

        assert success and all(success), success
        assert failure and all(failure), failure

    def test_they_differ_by_parse_provenance_not_file_existence(
        self,
    ) -> None:
        """`resolved_module`'s path is realistic; `fake`'s is synthetic."""
        real = resolved_module(("m",), self.SRC)
        fake = fake_resolved_module(("m",), self.SRC)
        assert real.file_path.is_absolute()
        assert real.file_path.suffix == ".vera"
        assert "/fake/" not in real.file_path.as_posix(), real.file_path
        assert fake.file_path.as_posix() == "/fake/m.vera", fake.file_path

    def test_a_deleted_path_still_type_checks_against_the_module(
        self,
    ) -> None:
        """The reason the deletion is safe, exercised rather than asserted.

        If any consumer reopened `file_path`, this would fail — the file
        is gone by the time the importer is checked.
        """
        mod = resolved_module(("m",), self.SRC)
        assert not mod.file_path.exists()
        prog = parse_to_ast(
            "import m;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ m::f(1) }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert not errors, [d.description for d in errors]


# =====================================================================
# Module call diagnostics (C7a)
# =====================================================================

class TestModuleCallDiagnostics:
    """Test improved module-call diagnostic messages (C7a).

    These tests construct AST nodes manually to exercise the checker
    logic in isolation from the parser.
    """

    @staticmethod
    def _make_program_with_module_call(
        mod_path: tuple[str, ...],
        fn_name: str,
    ) -> ast.Program:
        """Build a minimal Program with a module call in the body."""
        call = ast.ModuleCall(
            path=mod_path,
            name=fn_name,
            args=(ast.IntLit(value=42),),
        )
        fn = ast.FnDecl(
            name="main",
            forall_vars=None,
            forall_constraints=None,
            params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        tld = ast.TopLevelDecl(visibility="private", decl=fn)
        return ast.Program(
            module=None,
            imports=(),
            declarations=(tld,),
        )

    def test_module_not_found_warning(self) -> None:
        """ModuleCall without resolved_modules gives 'not found' warning."""
        prog = self._make_program_with_module_call(("foo",), "bar")
        diags = typecheck(prog, source="")
        warns = [d for d in diags if d.severity == "warning"]
        assert any("not found" in w.description for w in warns)
        assert any(w.error_code == "E230" for w in warns)

    def test_module_resolved_fn_not_found(self) -> None:
        """ModuleCall with resolved empty module gives 'not found in module'."""
        from vera.resolver import ResolvedModule

        prog = self._make_program_with_module_call(("foo",), "bar")
        fake_mod = ResolvedModule(
            path=("foo",),
            file_path=Path("/fake/foo.vera"),
            program=ast.Program(
                module=None, imports=(), declarations=(),
            ),
            source="",
        )
        diags = typecheck(prog, source="", resolved_modules=[fake_mod])
        warns = [d for d in diags if d.severity == "warning"]
        assert any("not found in module" in w.description for w in warns)
        assert any(w.error_code == "E233" for w in warns)


# =====================================================================
# C7b: Cross-module type checking
# =====================================================================


class TestCrossModuleTyping:
    """Test cross-module type merging (C7b).

    These tests verify that imported function signatures are registered
    and used for type-checking.  Manual-AST ModuleCall tests are retained
    for checker isolation; parse-from-source tests in TestModuleCallParsed
    verify end-to-end parsing with :: syntax.
    """

    # Reusable module sources
    MATH_MODULE = """\
public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn larger(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 >= @Int.1 then { @Int.0 } else { @Int.1 } }
"""

    GENERIC_MODULE = """\
public forall<T> fn identity(@T -> @T)
  requires(true)
  ensures(true)
  effects(pure)
{ @T.0 }
"""

    COLLECTIONS_MODULE = """\
public data List<T> { Nil, Cons(T, List<T>) }
public data Option<T> { None, Some(T) }
"""

    # -- Bare calls (parsed normally) -----------------------------------

    def test_bare_call_resolves_type(self) -> None:
        """import m(magnitude); magnitude(42) -> no errors."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(magnitude);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ magnitude(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_bare_call_arity_mismatch(self) -> None:
        """magnitude(1, 2) where magnitude takes 1 arg -> arity error."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(magnitude);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ magnitude(@Int.0, @Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("expects 1" in e.description for e in errors)

    def test_bare_call_type_mismatch(self) -> None:
        """magnitude(true) where magnitude expects Int -> type error."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math(magnitude);
private fn main(@Bool -> @Int)
  requires(true) ensures(true) effects(pure)
{ magnitude(@Bool.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("Bool" in e.description and "Int" in e.description
                    for e in errors)

    def test_bare_call_generic_inference(self) -> None:
        """import m(identity); identity(42) -> infers Int, no errors."""
        mod = _resolved_module(("gen",), self.GENERIC_MODULE)
        prog = parse_to_ast("""\
import gen(identity);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ identity(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_wildcard_import_allows_all(self) -> None:
        """import math (no names) -> all functions available."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        prog = parse_to_ast("""\
import math;
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ larger(@Int.0, magnitude(@Int.0)) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_local_shadows_import(self) -> None:
        """Local fn magnitude shadows imported magnitude."""
        mod = _resolved_module(("math",), """\
public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }
""")
        prog = parse_to_ast("""\
import math(magnitude);
private fn magnitude(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ magnitude(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_imported_adt_constructors(self) -> None:
        """import m(List) -> Cons and Nil constructors available."""
        mod = _resolved_module(("col",), self.COLLECTIONS_MODULE)
        prog = parse_to_ast("""\
import col(List);
private fn main(@Int -> @List<Int>)
  requires(true) ensures(true) effects(pure)
{ Cons(@Int.0, Nil) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    # -- Module-qualified calls (manual AST) ----------------------------

    def test_module_call_resolves_type(self) -> None:
        """ModuleCall to resolved function -> correct type, no errors."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="magnitude",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("math",), names=("magnitude",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        warns = [d for d in diags if d.severity == "warning"]
        assert errors == [], [e.description for e in errors]
        assert not any("not found" in w.description for w in warns)

    def test_module_call_arity_mismatch(self) -> None:
        """Module-qualified call with wrong arity -> error."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="magnitude",
            args=(ast.IntLit(value=1), ast.IntLit(value=2)),
        )
        imp = ast.ImportDecl(path=("math",), names=("magnitude",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("expects 1" in e.description for e in errors)

    def test_selective_import_rejects_unimported(self) -> None:
        """Module call to name not in selective import -> error."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="larger",
            args=(ast.IntLit(value=1), ast.IntLit(value=2)),
        )
        # Only import "magnitude", not "larger"
        imp = ast.ImportDecl(path=("math",), names=("magnitude",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("not imported" in e.description for e in errors)
        assert any(e.error_code == "E231" for e in errors)

    def test_fn_not_in_module(self) -> None:
        """Module call to nonexistent function -> warning with available list."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("math",), name="nonexistent",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("math",), names=None)  # wildcard
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Unit", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        warns = [d for d in diags if d.severity == "warning"]
        assert any("not found in module" in w.description for w in warns)
        assert any("magnitude" in w.description for w in warns)  # available list

    def test_multi_segment_path(self) -> None:
        """Multi-segment module path (vera.math) works."""
        mod = _resolved_module(("vera", "math"), self.MATH_MODULE)
        call = ast.ModuleCall(
            path=("vera", "math"), name="magnitude",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("vera", "math"), names=("magnitude",))
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]


# =====================================================================
# C7c: Visibility enforcement
# =====================================================================

class TestVisibilityEnforcement:
    """Test visibility enforcement (C7c).

    Verifies that the checker:
    - Requires explicit public/private on every fn/data declaration
    - Prevents importing private declarations across module boundaries
    - Allows calling own file's private declarations freely
    """

    # Reusable module sources
    MIXED_MODULE = """\
public fn pub_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

private fn priv_fn(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

public data Color { Red, Green, Blue }

private data Secret { Hidden }
"""

    # -- Mandatory visibility -------------------------------------------

    def test_missing_visibility_on_fn(self) -> None:
        """Bare fn (no public/private) -> error citing the §8.4 rule."""
        errs = _check_err("""
fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""", "Missing visibility on 'foo'")
        # Visibility is mandated by Chapter 8 §8.4, not the stale §5.8.
        vis = [e for e in errs if "Missing visibility" in e.description]
        assert vis[0].spec_ref == 'Chapter 8, Section 8.4 "Visibility"', (
            vis[0].spec_ref
        )

    def test_missing_visibility_on_data(self) -> None:
        """Bare data (no public/private) -> error."""
        _check_err("""
data Color { Red, Green, Blue }
""", "Missing visibility on 'Color'")

    def test_private_fn_ok(self) -> None:
        """Explicit private fn -> no error."""
        _check_ok("""
private fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    def test_public_fn_ok(self) -> None:
        """Explicit public fn -> no error."""
        _check_ok("""
public fn foo(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")

    # -- Cross-module visibility (bare calls) ---------------------------

    def test_public_fn_importable(self) -> None:
        """Public fn from module can be imported and called."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(pub_fn);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ pub_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_private_fn_not_importable(self) -> None:
        """Selective import of private fn -> error."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(priv_fn);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ priv_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("private" in e.description for e in errors), (
            [e.description for e in errors]
        )

    def test_public_data_importable(self) -> None:
        """Public data type and constructors can be imported."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(Color);
private fn main(@Unit -> @Color)
  requires(true) ensures(true) effects(pure)
{ Red }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_private_data_not_importable(self) -> None:
        """Selective import of private data type -> error."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod(Secret);
private fn main(@Unit -> @Secret)
  requires(true) ensures(true) effects(pure)
{ Hidden }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("private" in e.description for e in errors), (
            [e.description for e in errors]
        )

    def test_wildcard_import_skips_private(self) -> None:
        """Wildcard import only injects public names."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod;
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ pub_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_wildcard_import_private_fn_unresolved(self) -> None:
        """Wildcard import: calling private fn -> unresolved warning."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mod;
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ priv_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        warns = [d for d in diags if d.severity == "warning"]
        assert any("Unresolved" in w.description or "not found" in w.description
                    for w in warns), [d.description for d in diags]

    # -- Module-qualified call visibility (C7c + ModuleCall AST) --------

    def test_module_call_private_fn_rejected(self) -> None:
        """ModuleCall to private function -> error."""
        mod = _resolved_module(("mod",), self.MIXED_MODULE)
        call = ast.ModuleCall(
            path=("mod",), name="priv_fn",
            args=(ast.IntLit(value=42),),
        )
        imp = ast.ImportDecl(path=("mod",), names=None)
        fn = ast.FnDecl(
            name="main", forall_vars=None, forall_constraints=None, params=(),
            return_type=ast.NamedType(name="Int", type_args=None),
            contracts=(
                ast.Requires(expr=ast.BoolLit(value=True)),
                ast.Ensures(expr=ast.BoolLit(value=True)),
            ),
            effect=ast.PureEffect(),
            body=ast.Block(statements=(), expr=call),
            where_fns=None,
        )
        prog = ast.Program(
            module=None,
            imports=(imp,),
            declarations=(ast.TopLevelDecl(visibility="private", decl=fn),),
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("private" in e.description for e in errors), (
            [e.description for e in errors]
        )
        e232 = [e for e in errors if e.error_code == "E232"]
        assert e232, [e.error_code for e in errors]
        # E232 (private qualified call) must cite the Chapter 8 visibility
        # rule, like the parallel import-visibility diagnostic E150 — not
        # the stale "Chapter 5, Section 5.8" that no longer exists.
        assert e232[0].spec_ref == 'Chapter 8, Section 8.4 "Visibility"', (
            e232[0].spec_ref
        )

    # -- Own file's declarations always accessible ----------------------

    def test_own_private_fn_callable(self) -> None:
        """Private fn in own file -> callable, no errors."""
        _check_ok("""
private fn helper(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }

private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ helper(@Int.0) }
""")

    # -- Error message quality ------------------------------------------

    def test_visibility_error_mentions_private(self) -> None:
        """Error message includes 'private', fn name, and module name."""
        mod = _resolved_module(("mymod",), self.MIXED_MODULE)
        prog = parse_to_ast("""\
import mymod(priv_fn);
private fn main(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ priv_fn(@Int.0) }
""")
        diags = typecheck(prog, source="", resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        msg = " ".join(e.description for e in errors)
        assert "private" in msg.lower()
        assert "priv_fn" in msg
        assert "mymod" in msg


# =====================================================================
# Built-in redefinition (E151) — #815 one-canonical-form
# =====================================================================


class TestBuiltinRedefinition:
    """Redefining an opaque built-in is a checker error (E151, #815).

    Per DESIGN.md "one canonical form" + fail-loud: a user/module ``fn``
    named after a verifier-modelled built-in (``abs`` / ``min`` / ``max`` /
    ``clamp`` / ``to_string`` / ``string_*`` / …) is rejected, because the
    verifier reasons with the built-in's model while codegen runs the
    user's body — a silent verifier↔runtime unsoundness.  The Option /
    Result / Json / Html *combinators* the prelude injects are exempt:
    they are real Vera functions, so a user override is sound, and the
    prelude deliberately lets the user replace them.
    """

    @staticmethod
    def _codes(errs: list[Diagnostic]) -> list[str]:
        return [e.error_code for e in errs]

    def test_redefining_abs_is_E151(self) -> None:
        errs = _errors("""
public fn abs(@Int -> @Int)
  requires(true) ensures(@Int.result < 0) effects(pure)
{ 0 - 1 }
""")
        assert "E151" in self._codes(errs), self._codes(errs)
        diag = next(e for e in errs if e.error_code == "E151")
        assert "abs" in diag.description
        assert "redefines a built-in" in diag.description
        # Instructional: states the rule, the why, and the fix.
        assert diag.rationale and diag.fix and diag.spec_ref
        assert "Chapter 9" in diag.spec_ref

    def test_redefining_clamp_is_E151(self) -> None:
        errs = _errors("""
public fn clamp(@Int, @Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert "E151" in self._codes(errs), self._codes(errs)

    def test_redefining_to_string_is_E151(self) -> None:
        errs = _errors("""
public data Color { Red, Green, Blue }
public fn to_string(@Color -> @String)
  requires(true) ensures(true) effects(pure)
{ "x" }
""")
        assert "E151" in self._codes(errs), self._codes(errs)

    def test_overriding_option_map_combinator_is_allowed(self) -> None:
        """The prelude combinators stay user-overridable — exempt from E151.

        This is the regression guard for the #815 design decision: a naive
        "reject every built-in name" rule would wrongly fire here.
        """
        errs = _errors("""
public data Option<T> { None, Some(T) }
public fn option_map(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        assert "E151" not in self._codes(errs), self._codes(errs)
        # ...but the exemption is *specific* to the prelude combinators: a
        # non-combinator built-in such as the iterative `array_map` is NOT
        # exempt and must still be rejected (boundary guard — a too-broad
        # exemption would wrongly let this through).
        arr_errs = _errors("""
public fn array_map(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        assert "E151" in self._codes(arr_errs), self._codes(arr_errs)

    def test_non_builtin_name_is_allowed(self) -> None:
        """A user fn whose name is not a built-in is unaffected."""
        errs = _errors("""
public fn saturating_abs(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }
""")
        assert "E151" not in self._codes(errs), self._codes(errs)

    def test_where_fn_redefining_builtin_is_E151(self) -> None:
        """A where-helper named after a built-in is rejected too (#815).

        Otherwise the verifier models the *call* with the built-in's
        idealized model while codegen runs the where-body — the exact
        verify-proves / run-violates desync, just one scope deeper.
        """
        errs = _errors("""
public fn caller(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ abs(@Int.0) }
where {
  fn abs(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { 0 - @Int.0 }
}
""")
        assert "E151" in self._codes(errs), self._codes(errs)

    def test_rejected_where_fn_does_not_shadow_canonical_builtin(self) -> None:
        """A rejected where-helper must not overwrite the canonical built-in
        entry in `env.functions` (#815).

        Discriminating via a *different arity*: the where-fn `abs` takes two
        args; a sibling `other` calls the one-arg built-in `abs`. If the
        two-arg helper leaked into `env.functions`, `other`'s call would hit
        a spurious arity error — so the only diagnostic must be the E151 on
        the redefinition itself, nothing attributed to `other`.
        """
        errs = _errors("""
public fn other(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ abs(@Int.0) }

public fn caller(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
where {
  fn abs(@Int, @Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 }
}
""")
        codes = self._codes(errs)
        assert "E151" in codes, codes
        # The 2-arg where-fn must not have leaked over the 1-arg built-in:
        # `other`'s call resolves to the built-in, so E151 is the *only* error.
        assert [c for c in codes if c != "E151"] == [], codes

    def test_rejected_builtin_redef_is_not_rechecked(self) -> None:
        """A rejected built-in redefinition is skipped in the check phase, so
        its own body produces no bogus secondary diagnostics (#815).

        Since the rejected `abs` is not registered (the built-in stays
        canonical), re-checking its 2-arg recursive body would resolve `abs`
        to the 1-arg built-in and emit a spurious E201 on top of the E151.
        The only diagnostic must be the E151 on the redefinition itself.
        """
        errs = _errors("""
public fn abs(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ abs(@Int.0, @Int.1) }
""")
        codes = self._codes(errs)
        assert "E151" in codes, codes
        assert [c for c in codes if c != "E151"] == [], codes

    def test_nested_helper_rejection_skips_parent_body(self) -> None:
        """A rejected where-helper must not cascade into the *parent* body (#815).

        The helper `abs` (2-arg) is rejected (E151) and stripped from
        registration. The parent `caller`'s body calls it with two args; if the
        parent body is still checked, that call resolves against the 1-arg
        built-in `abs` and emits a spurious E201. Propagating the nested
        rejection up to `caller` skips its body too, so the only diagnostic is
        the E151 on the helper. (Sibling case to
        ``test_rejected_builtin_redef_is_not_rechecked``, one scope deeper.)
        """
        errs = _errors("""
public fn caller(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ abs(@Int.0, @Int.0) }
where {
  fn abs(@Int, @Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 }
}
""")
        codes = self._codes(errs)
        assert "E151" in codes, codes
        assert [c for c in codes if c != "E151"] == [], codes

    def test_imported_module_redefining_builtin_is_E151(self) -> None:
        """An imported module that redefines a built-in is rejected in the
        importer (#815 — "user/module" scope).

        Otherwise the importer's `vera check` reports OK while its verifier
        reasons with the built-in's model and the module's body runs — the
        unsound path stays open whenever the module is imported but never
        checked standalone.
        """
        mod_src = (
            "module badmath;\n"
            "public fn abs(@Int -> @Int)\n"
            "  requires(true) ensures(@Int.result >= 0) effects(pure)\n"
            "{ 0 - 1 }\n"
        )
        mod = ResolvedModule(
            path=("badmath",),
            file_path=Path("/fake/badmath.vera"),
            program=parse_to_ast(mod_src),
            source=mod_src,
        )
        prog = parse_to_ast(
            "import badmath(abs);\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(@Int.result >= 0) effects(pure)\n"
            "{ abs(5) }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        codes = [d.error_code for d in diags]
        assert "E151" in codes, codes
        # The harvested diagnostic carries the *module's* file path (#815), so
        # `vera check --json` points at where the redefinition actually is.
        # Compare to str(mod.file_path) (not a hard-coded POSIX string) so the
        # assertion holds on Windows too, where str(Path) uses backslashes.
        e151 = next(d for d in diags if d.error_code == "E151")
        assert e151.location.file == str(mod.file_path), e151.location.file

    def test_generic_redefining_builtin_is_E151(self) -> None:
        """A generic ``forall<T>`` fn named after a built-in is rejected."""
        errs = _errors("""
public forall<T> fn abs(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
""")
        assert "E151" in self._codes(errs), self._codes(errs)

    def test_overriding_json_combinator_is_allowed(self) -> None:
        """The exemption covers *all* prelude combinators, not just
        ``option_map`` — a user ``json_get`` override is allowed.

        Regression guard for the exempt-set derivation across every
        combinator source block (a JSON block, distinct from the Option
        block ``test_overriding_option_map_combinator`` covers).
        """
        errs = _errors("""
public fn json_get(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        assert "E151" not in self._codes(errs), self._codes(errs)


# =====================================================================
# Reserved function names (E153) — #1181 one-canonical-form
# =====================================================================


class TestReservedTypePrefix:
    """User type/alias names in the prelude's `Vera` namespace are E154.

    PR #1191's spec sentence claims the prelude's internals "resolve
    through reserved names no user declaration spells"; this gate is the
    enforcing rail (CodeRabbit review finding).  `inject_prelude` skips
    any of its generated declarations whose name the user program already
    spells, so before the rail a `type VeraOptionMapFn = Int;` silently
    re-typed the prelude's combinator signatures — check-green, then a
    raw WebAssembly validation failure at run.  The reservation is
    anchored: `Vera` + an uppercase letter or digit.  The checker never
    sees the injected twins (injection is a codegen-side transform), so
    the rail cannot fire on the prelude itself.
    """

    def _codes(self, source: str) -> list[str | None]:
        diags = typecheck(parse_to_ast(source), source=source)
        return [d.error_code for d in diags]

    def _diag(self, source: str) -> Diagnostic:
        """The single E154 *source* produces (asserting there is one)."""
        diags = typecheck(parse_to_ast(source), source=source)
        e154 = [d for d in diags if d.error_code == "E154"]
        assert len(e154) == 1, [(d.error_code, d.description) for d in diags]
        return e154[0]

    def test_alias_spelling_a_twin_is_E154(self) -> None:
        codes = self._codes("type VeraOptionMapFn = Int;\n")
        assert "E154" in codes, codes

    def test_alias_with_any_reserved_shape_is_E154(self) -> None:
        """The rule is the prefix shape, not a name list."""
        codes = self._codes("type VeraZ = Int;\n")
        assert "E154" in codes, codes

    def test_data_decl_is_gated_too(self) -> None:
        codes = self._codes("data VeraBox { MkVeraBox(Int) }\n")
        assert "E154" in codes, codes

    def test_digit_follower_is_E154_with_parseable_hint(self) -> None:
        """The `[0-9]` half of the class (PR #1191 review), and the fix
        hint must suggest a name that can parse — `Vera0Fn` strips to
        `0Fn`, so the hint falls back to a `My`-prefixed form."""
        diags = typecheck(parse_to_ast("type Vera0Fn = Int;\n"), source="")
        e154 = [d for d in diags if d.error_code == "E154"]
        assert e154, [d.error_code for d in diags]
        assert "MyVera0Fn" in e154[0].fix, e154[0].fix

    def test_underscore_follower_stays_legal(self) -> None:
        """`Vera_thing` is outside the anchored class (PR #1191 review)."""
        diags = typecheck(parse_to_ast("type Vera_thing = Int;\n"), source="")
        assert "E154" not in [d.error_code for d in diags]

    def test_ordinary_words_stay_legal(self) -> None:
        """Anchoring: `Veranda` (lowercase follower) and containment."""
        for src in (
            "type Veranda = Int;\n",
            "type Vera = Int;\n",
            "type MyVeraThing = Int;\n",
        ):
            codes = self._codes(src)
            assert "E154" not in codes, (src, codes)

    def test_unprefixed_prelude_alias_shadow_stays_legal(self) -> None:
        """An unprefixed name outside the reservation is the user's.

        PR #1191 stated this as "shadowing `OptionMapFn` is fine" — the
        prelude then injected that spelling, so the declaration really
        did shadow one.  #1221 retired the six user-facing spellings into
        the reserved namespace, so `OptionMapFn` shadows nothing and the
        claim would be a tautology; what still needs a rail is that the
        reservation stops where it is anchored.  `Option` is a name the
        prelude DOES still inject (its ADT), so this keeps exercising a
        real shadow, and the reserved twin the combinators resolve
        through is the negative beside it.
        """
        codes = self._codes("type OptionMapFn = Int;\n")
        assert "E154" not in codes, codes
        codes = self._codes("data Option<T> { None, Some(T) }\n")
        assert "E154" not in codes, codes

    # -----------------------------------------------------------------
    # Type-PARAMETER binders (#1221 review, finding 1)
    # -----------------------------------------------------------------

    def test_forall_binder_in_the_reserved_namespace_is_E154(self) -> None:
        """A `forall` variable is a type binder, and binds ahead of the gate.

        `_resolve_named_type` consults `env.type_params` before it reaches
        the reserved-namespace check, so a generic declaring
        `forall<VeraOptionMapFn>` made every mention of that name resolve
        to the type variable — the reservation held at neither end.  One
        error per offending binder.
        """
        src = (
            "public forall<VeraOptionMapFn, VeraArrayMapFn> "
            "fn pick(@VeraOptionMapFn, @VeraArrayMapFn -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 1 }\n"
        )
        diags = typecheck(parse_to_ast(src), source=src)
        e154 = [d for d in diags if d.error_code == "E154"]
        assert len(e154) == 2, [d.description for d in diags]
        assert {"VeraOptionMapFn", "VeraArrayMapFn"} == {
            name for name in ("VeraOptionMapFn", "VeraArrayMapFn")
            if any(name in d.description for d in e154)
        }

    def test_where_helper_forall_binder_is_gated(self) -> None:
        """The helper declares its own `forall`, one scope deeper."""
        src = (
            "public fn outer(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ inner(@Int.0) }\n"
            "where {\n"
            "  forall<VeraT> fn inner(@VeraT -> @Int)\n"
            "    requires(true) ensures(true) effects(pure)\n"
            "  { 1 }\n"
            "}\n"
        )
        codes = self._codes(src)
        assert "E154" in codes, codes

    def test_data_and_alias_type_params_are_gated(self) -> None:
        """The other declaration surfaces that bind a type name."""
        assert "E154" in self._codes("data Box<VeraA> { MkBox(VeraA) }\n")
        assert "E154" in self._codes("type Pair<VeraA> = Option<VeraA>;\n")

    def test_effect_and_ability_type_params_are_gated(self) -> None:
        """Their parameters are type binders too, in the same namespace."""
        assert "E154" in self._codes(
            "effect Logger<VeraT> {\n  op log(VeraT -> Unit);\n}\n"
        )
        assert "E154" in self._codes(
            "ability Sized<VeraT> {\n  op size(VeraT -> Int);\n}\n"
        )

    def test_ordinary_binders_stay_legal(self) -> None:
        """The anchoring, on the binder surface: `T`, `Veranda`, `Vera`."""
        for binder in ("T", "Veranda", "Vera", "Vera_thing"):
            src = (
                f"public forall<{binder}> fn ident(@{binder} -> @Int)\n"
                "  requires(true) ensures(true) effects(pure)\n"
                "{ 1 }\n"
            )
            codes = self._codes(src)
            assert "E154" not in codes, (binder, codes)

    # -----------------------------------------------------------------
    # Effect / ability / constructor NAMES (#1260)
    # -----------------------------------------------------------------

    def test_effect_name_in_the_reserved_namespace_is_E154(self) -> None:
        """The reservation is one rule across every declaration namespace.

        #1254 left it enforced in the type namespace alone, so
        `effect VeraZed` checked clean — half a reservation, and the one
        namespace a future prelude-internal effect would have to claim.
        """
        codes = self._codes("effect VeraZed {\n  op zap(Int -> Unit);\n}\n")
        assert "E154" in codes, codes

    def test_ability_name_in_the_reserved_namespace_is_E154(self) -> None:
        codes = self._codes("ability VeraZed {\n  op size(Int -> Int);\n}\n")
        assert "E154" in codes, codes

    def test_constructor_name_in_the_reserved_namespace_is_E154(self) -> None:
        """A constructor is a name a program declares, in its own namespace."""
        codes = self._codes("public data Other { VeraZed(Int) }\n")
        assert "E154" in codes, codes

    def test_reserved_constructor_is_flagged_under_a_legal_parent(self) -> None:
        """One error per offending constructor, parent name untouched."""
        src = "public data Other { Fine(Int), VeraZed(Int), VeraOther }\n"
        diags = typecheck(parse_to_ast(src), source=src)
        e154 = [d for d in diags if d.error_code == "E154"]
        assert len(e154) == 2, [d.description for d in diags]
        assert all("Other'" not in d.description or "VeraOther" in
                   d.description for d in e154), [d.description for d in e154]

    def test_fix_text_offers_no_alias_escape_outside_the_type_namespace(
        self,
    ) -> None:
        """Principle 1: the fix must be right PER NAMESPACE (#1260).

        The type-position text offers "declare an alias outside the
        reserved namespace"; an effect, ability, or constructor has no
        alias escape, so its fix is a rename and nothing else.
        """
        for src, word in (
            ("effect VeraZed {\n  op zap(Int -> Unit);\n}\n", "Effect"),
            ("ability VeraZed {\n  op size(Int -> Int);\n}\n", "Ability"),
            ("public data Other { VeraZed(Int) }\n", "Constructor"),
        ):
            diags = typecheck(parse_to_ast(src), source=src)
            e154 = [d for d in diags if d.error_code == "E154"]
            assert e154, (src, [d.error_code for d in diags])
            assert e154[0].description.startswith(word), e154[0].description
            assert "alias" not in (e154[0].fix or ""), e154[0].fix
            assert "Zed" in (e154[0].fix or ""), e154[0].fix

    def test_rationale_is_per_rail_because_the_consequence_is(self) -> None:
        """A diagnostic must not state a consequence that cannot happen.

        The type/alias rail's rationale names a real mechanism: the
        prelude declares six reserved ALIASES, `inject_prelude` skips
        one whose name the program already spells, and the user
        declaration re-types the combinators' own signatures —
        check-green, then a WebAssembly validation failure at run.  The
        prelude declares no effect, ability or constructor in the
        namespace at all, so nothing there can be re-typed: with the
        gate bypassed, `data Other { VeraZed(Int) }` compiles AND runs.
        Those three rails state the forward reason instead (the
        namespace is reserved ahead of use).  `check_diagnostic_fields`
        checks a rationale is present, never that it is true, so this is
        the only rail against the wrong one.
        """
        occupied = self._diag("type VeraZed = Int;\n")
        assert "re-types those internals" in occupied.rationale
        assert "WebAssembly validation" in occupied.rationale

        for src, kind in (
            ("effect VeraZed {\n  op zap(Int -> Unit);\n}\n", "effect"),
            ("ability VeraZed {\n  op size(Int -> Int);\n}\n", "ability"),
            ("public data Other { VeraZed(Int) }\n", "constructor"),
        ):
            d = self._diag(src)
            assert "re-types" not in d.rationale, (kind, d.rationale)
            assert "WebAssembly validation" not in d.rationale, (
                kind, d.rationale)
            assert f"declares no {kind} there today" in d.rationale, (
                kind, d.rationale)
            assert "reserved ahead of use" in d.rationale, (kind, d.rationale)
        # Both variants keep the shared statement of WHAT the namespace is.
        assert "prelude's internal namespace" in occupied.rationale

    def test_the_prelude_occupies_the_type_namespace_only(self) -> None:
        """The premise the branch above rests on, measured not assumed.

        If the prelude ever declares an effect, ability or constructor
        in the reserved namespace, the "declares no X there today"
        rationale becomes the false one and this fails first.
        """
        from vera import prelude as prelude_mod

        found: dict[str, set[str]] = {}

        def note(kind: str, name: str) -> None:
            if name.startswith("Vera"):
                found.setdefault(kind, set()).add(name)

        for const in dir(prelude_mod):
            value = getattr(prelude_mod, const)
            if not isinstance(value, str) or "Vera" not in value:
                continue
            try:
                prog = parse_to_ast(value)
            except Exception:  # noqa: BLE001 — not every constant is a program
                continue
            for top in prog.declarations:
                d = top.decl
                note(type(d).__name__, getattr(d, "name", "") or "")
                for tp in (getattr(d, "type_params", None) or ()):
                    note("type_param", tp)
                for fv in (getattr(d, "forall_vars", None) or ()):
                    note("type_param", fv)
                if isinstance(d, ast.DataDecl):
                    for c in d.constructors:
                        note("Constructor", c.name)

        assert set(found) == {"TypeAliasDecl", "type_param"}, found
        assert found["TypeAliasDecl"], found

    def test_ordinary_names_stay_legal_in_all_three_namespaces(self) -> None:
        """The anchoring holds wherever the rule is applied."""
        for name in ("Veranda", "Vera_thing", "Vera"):
            for src in (
                f"effect {name} {{\n  op zap(Int -> Unit);\n}}\n",
                f"ability {name} {{\n  op size(Int -> Int);\n}}\n",
                f"public data Other {{ {name}(Int) }}\n",
            ):
                codes = self._codes(src)
                assert "E154" not in codes, (src, codes)

    def test_module_declaration_surfaces_E154(self) -> None:
        mod_src = "module vmod;\ntype VeraResultMapFn = Int;\n"
        mod = ResolvedModule(
            path=("vmod",),
            file_path=Path("/fake/vmod.vera"),
            program=parse_to_ast(mod_src),
            source=mod_src,
        )
        prog = parse_to_ast(
            "import vmod;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        codes = [d.error_code for d in diags]
        assert "E154" in codes, codes


class TestReservedFnName:
    """A ``fn`` named ``old`` or ``new`` is rejected at its declaration
    (E153, #1181).

    The grammar reserves ``old(`` and ``new(`` in *expression* position for
    the contract state forms — ``old_expr`` / ``new_expr`` in
    ``vera/grammar.lark``, each of which demands an effect reference, not an
    arbitrary expression.  So a *bare* ``old(5)`` can never parse as a call to
    a user function — anywhere, including inside the declaring module — and
    reaches ``[E030]``/``[E031]`` instead (#1173/#1180).  The one exception is
    a module-qualified ``mod::old(...)``, which parses through the module-call
    rule and previously DID call a module export named ``old``
    (``test_module_qualified_call_route_is_deliberately_closed`` below pins
    the shape).  The declaration used to be accepted anyway: a trap in every
    unqualified position, half-usable cross-module only.  Rejecting it at the
    declaration reserves the whole identifier — the sibling of E151 (built-in
    functions) and E152 (built-in effects), and the same DESIGN.md "one
    canonical form" / fail-loud rule.

    **Where the state-form piece sits.**  Every candidate below was probed by
    declaring ``private fn <name>(@Int -> @Int)`` and then calling
    ``<name>(3)`` from ``main``:

    * ``old``, ``new`` — declaration accepted, call rejected (E030 / E031).
      Reserved here, as ``_STATE_FORM_FN_NAMES``.
    * ``with``, ``in``, ``effect``, ``op``, ``data``, ``type``, ``import``,
      ``public``, ``private``, ``requires``, ``ensures``, ``effects``,
      ``decreases``, ``where``, ``then``, ``else``, ``pure``, ``invariant``,
      ``module``, ``ability``, ``result`` — declaration *and* call both
      accepted, and this row long read "Not reserved; nothing is wrong with
      them".  Something is: spec §1.4 reserves them and nothing held the
      MUST, so the specification and the implementation disagreed about
      which programs are legal (#1296).  Being callable is what removed the
      *unreachability* argument, not the reservation.  They are reserved as
      ``_CONTEXTUAL_KEYWORD_FN_NAMES`` — derived from ``grammar.lark`` rather
      than listed, which is how ``ability``/``effects``/``op``/``result``
      joined despite §1.4 never naming them — and
      :class:`TestReservedContextualKeywordFnName` owns that piece.
      (``throw`` was on this row and is not a keyword in the grammar at all,
      so it stays an ordinary function name.)
    * ``resume`` — declaration and call both accepted here too, which is why
      this probe row once read "nothing is wrong with it".  Something is: the
      accepted declaration collides with the resumption binding every handler
      clause body carries, and breaks handlers elsewhere in the file.  It is
      reserved as ``_HANDLER_OPERATOR_FN_NAMES`` and
      :class:`TestReservedResumeFnName` owns that piece.
    * ``assert``, ``assume``, ``forall``, ``exists``, ``match``, ``if``,
      ``let``, ``fn``, ``true``, ``false`` — the keyword class, reserved by
      #1187 as ``_KEYWORD_FN_NAMES``; ``handle`` is carved back out as a
      host-invoked entry point.  :class:`TestReservedKeywordFnName` below
      owns that half of the gate.
    """

    @staticmethod
    def _codes(errs: list[Diagnostic]) -> list[str]:
        return [e.error_code for e in errs]

    def test_fn_named_old_is_E153(self) -> None:
        errs = _errors("""
public fn old(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ 5 }
""")
        assert "E153" in self._codes(errs), self._codes(errs)
        diag = next(e for e in errs if e.error_code == "E153")
        # Names the identifier and the reason it can never be called.
        assert "old" in diag.description
        assert "reserved" in diag.description.lower()
        # Instructional: states the rule, the why, and the fix.
        assert diag.rationale and diag.fix and diag.spec_ref
        assert "Chapter 5" in diag.spec_ref
        # The fix is to rename, so it must say so.
        assert "rename" in diag.fix.lower()

    def test_fn_named_new_is_E153(self) -> None:
        errs = _errors("""
public fn new(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ 5 }
""")
        assert "E153" in self._codes(errs), self._codes(errs)
        diag = next(e for e in errs if e.error_code == "E153")
        assert "new" in diag.description

    def test_private_fn_named_old_is_E153(self) -> None:
        """The gate is visibility-independent — a `private fn old` is just as
        unreachable as a public one."""
        errs = _errors("""
private fn old(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ 5 }
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_generic_fn_named_new_is_E153(self) -> None:
        """A generic ``forall<T>`` fn named after a reserved form is rejected
        too — the grammar reservation is on the *call* spelling, which a type
        parameter does not change."""
        errs = _errors("""
public forall<T> fn new(@T -> @T)
  requires(true) ensures(true) effects(pure)
{ @T.0 }
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_where_helper_named_old_is_E153(self) -> None:
        """A where-helper named ``old`` is rejected too.

        Helpers are called in expression position exactly like top-level
        functions, so ``old(...)`` inside the parent body hits the same
        ``old_expr`` grammar rule — the helper is unreachable one scope
        deeper.  Without this the gate would leave the identical dead
        declaration legal in a ``where`` block.
        """
        errs = _errors("""
public fn caller(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Int.0 }
where {
  fn old(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { 5 }
}
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_where_helper_named_new_is_E153(self) -> None:
        errs = _errors("""
public fn caller(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Int.0 }
where {
  fn new(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { 5 }
}
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_E153_is_the_only_diagnostic(self) -> None:
        """The rejection must not cascade.

        The rejected ``old`` is not registered, so nothing else in the
        program may pick up a secondary error from its absence — the whole
        report is the one E153 on the declaration.
        """
        errs = _errors("""
public fn old(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ 5 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        codes = self._codes(errs)
        assert "E153" in codes, codes
        assert [c for c in codes if c != "E153"] == [], codes

    def test_names_merely_containing_a_reserved_word_are_allowed(self) -> None:
        """Prefix/suffix false-positive guard.

        The reservation is on the whole identifier, not a substring: the
        grammar only reserves the exact tokens ``old`` and ``new`` before a
        ``(``.  ``older(3)`` and ``renew(3)`` parse as ordinary calls, so
        those declarations must stay legal — a naive ``startswith`` /
        ``in`` test would break every one of them.
        """
        for name in ("older", "renew", "news", "newton", "oldest", "newt"):
            errs = _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{ {name}(3) }}
""")
            assert self._codes(errs) == [], (name, self._codes(errs))

    def test_imported_module_fn_named_old_is_E153(self) -> None:
        """An imported module declaring ``fn old`` is rejected in the importer.

        Same surfacing mechanism as E151/E152: a module imported but never
        checked standalone would otherwise carry the trapped declaration
        silently.  Note the importer COULD previously call it — but only via
        the qualified ``mod::old(...)`` route; the deliberate closure of that
        route is pinned by
        ``test_module_qualified_call_route_is_deliberately_closed`` below.
        """
        mod_src = (
            "module stale;\n"
            "public fn old(@Int -> @Int)\n"
            "  requires(true) ensures(@Int.result >= 0) effects(pure)\n"
            "{ 5 }\n"
        )
        mod = ResolvedModule(
            path=("stale",),
            file_path=Path("/fake/stale.vera"),
            program=parse_to_ast(mod_src),
            source=mod_src,
        )
        prog = parse_to_ast(
            "import stale;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        codes = [d.error_code for d in diags]
        assert "E153" in codes, codes
        # The harvested diagnostic carries the *module's* file path, as E151
        # does, so `vera check --json` points at the real declaration.  Compare
        # against str(mod.file_path) so the assertion holds on Windows too.
        e153 = next(d for d in diags if d.error_code == "E153")
        assert e153.location.file == str(mod.file_path), e153.location.file

    def test_module_qualified_call_route_is_deliberately_closed(self) -> None:
        """E153 fires even when a qualified call site proves reachability.

        Adversarial-review finding on PR #1188: before the gate, this exact
        program — module export named ``old``, importer calling it as
        ``stale::old(5)`` — type-checked AND ran (``vera run`` printed 6).
        The qualified route goes through the module-call rule, not the
        reserved ``old_expr`` state form, so "no program could reach it" was
        false for module exports.  The reservation is on the whole
        identifier anyway (one-canonical-form, as E151/E152): a name that
        is a trap in every unqualified position — its own module cannot
        bare-call it — is refused outright rather than left half-usable.
        This test pins that the previously-working shape now gets E153 at
        the module declaration, i.e. the breakage is loud and located.
        """
        mod_src = (
            "module stale;\n"
            "public fn old(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 + 1 }\n"
        )
        mod = ResolvedModule(
            path=("stale",),
            file_path=Path("/fake/stale.vera"),
            program=parse_to_ast(mod_src),
            source=mod_src,
        )
        prog = parse_to_ast(
            "import stale;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ stale::old(5) }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        codes = [d.error_code for d in diags]
        assert "E153" in codes, codes
        e153 = next(d for d in diags if d.error_code == "E153")
        assert e153.location.file == str(mod.file_path), e153.location.file

    def test_effect_op_named_old_never_reaches_the_gate(self) -> None:
        """Boundary pin: ``op old(...)`` is already refused by the grammar.

        The gate covers ``fn`` declarations only.  It does not need to cover
        effect operations, because ``op old(@Int -> @Int)`` is parsed as the
        ``old_expr`` state form and fails at parse with ``[E030]`` — an
        effect named-operation ``old`` cannot be written in the first place.
        Pinning that here so a future grammar change that admits the ``op``
        spelling shows up as a failure to widen the gate, rather than
        silently reopening #1181 one construct across.
        """
        with pytest.raises(ParseError) as exc:
            parse_to_ast("""
effect Renamer {
  op old(@Int -> @Int)
}
""")
        assert exc.value.diagnostic.error_code == "E030"


# =====================================================================
# Reserved keyword function names (E153) — #1187
# =====================================================================


class TestReservedKeywordFnName:
    """A ``fn`` named after a grammar keyword is rejected (E153, #1187).

    Lark's contextual lexer re-lexes each of these keywords as
    ``LOWER_IDENT`` in *declaration* position, so ``private fn match(...)``
    declares happily.  None of them can be written in *expression* position:
    a bare ``match(3)`` fails to parse (``[E005]``), and ``assert(3)`` /
    ``assume(3)`` are read as the statement forms and collide
    (``[E121]`` + ``[E172]``/``[E173]``).  Every one is therefore a
    declarable trap, and #1187 refuses it at the declaration — the same
    one-canonical-form rule as ``old``/``new`` (E153, #1181), E151 (built-in
    functions) and E152 (built-in effects).

    **Probe record** (run against the pre-#1187 tree, one row per name,
    ``private fn <name>(@Int -> @Int)`` plus ``<name>(3)`` in ``main``):

    * ``assert``, ``assume`` — declaration accepted, bare call reaches the
      statement form and fails ``[E121]`` + ``[E172]``/``[E173]``.
    * ``forall``, ``exists``, ``match``, ``if``, ``let``, ``fn``, ``true``,
      ``false``, ``handle`` — declaration accepted, bare call ``[E005]``
      (does not parse as a call at all).
    * A module-qualified ``mod::<name>(5)`` type-checked **and ran** for
      every one of the eleven (``vera run`` printed 6 for ``match``) —
      exactly the half-usable-cross-module shape #1181 found for ``old``.
      Reserving the name closes it deliberately; see
      ``test_module_qualified_keyword_call_route_is_closed``.
    * ``op <name>(...)`` inside an ``effect`` block does *not* parse
      (``[E005]``), so no effect-operation carve-out is needed; pinned by
      ``test_effect_op_named_match_never_reaches_the_gate``.

    ``handle`` is the one carve-out: ``public fn handle(@Request ->
    @Response)`` is the host-invoked ``vera serve`` / ``wasi:http`` entry
    point (spec §9.5.6), called by the host rather than from Vera source, so
    "uncallable from expression position" does not make it dead code.  It
    lives in a named ``_HOST_INVOKED_FN_NAMES`` set subtracted from the
    reservation, pinned by ``test_handle_stays_legal``.
    """

    #: Every keyword the reservation covers (``handle`` deliberately absent).
    KEYWORDS = (
        "assert", "assume", "forall", "exists", "match",
        "if", "let", "fn", "true", "false",
    )

    @staticmethod
    def _codes(errs: list[Diagnostic]) -> list[str]:
        return [e.error_code for e in errs]

    def test_keyword_tuple_matches_checker_set(self) -> None:
        """``KEYWORDS`` mirrors the checker's reserved keyword set exactly.

        Pins ``set(KEYWORDS) == _KEYWORD_FN_NAMES - _HOST_INVOKED_FN_NAMES``
        so a keyword added to the checker's set without a matching
        per-keyword ``E153`` test here fails this pin instead of silently
        escaping coverage.  The subtraction preserves the deliberate
        omission of ``handle`` (the host-invoked carve-out).
        """
        from vera.checker.registration import (
            _HOST_INVOKED_FN_NAMES,
            _KEYWORD_FN_NAMES,
        )

        assert (
            set(self.KEYWORDS)
            == _KEYWORD_FN_NAMES - _HOST_INVOKED_FN_NAMES
        )

    @pytest.mark.parametrize("name", KEYWORDS)
    def test_keyword_fn_name_is_E153(self, name: str) -> None:
        """Each reserved keyword is refused at the declaration site."""
        errs = _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}
""")
        assert "E153" in self._codes(errs), (name, self._codes(errs))
        diag = next(e for e in errs if e.error_code == "E153")
        assert name in diag.description, diag.description
        assert "reserved" in diag.description.lower(), diag.description
        # Instructional on the keyword branch too (check_diagnostic_fields).
        assert diag.rationale and diag.fix and diag.spec_ref
        assert "Chapter 5" in diag.spec_ref, diag.spec_ref
        assert "rename" in diag.fix.lower(), diag.fix

    @pytest.mark.parametrize("name", KEYWORDS)
    def test_private_keyword_fn_name_is_E153(self, name: str) -> None:
        """Visibility-independent, as the ``old``/``new`` branch is."""
        errs = _errors(f"""
private fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}
""")
        assert "E153" in self._codes(errs), (name, self._codes(errs))

    def test_keyword_rationale_is_not_the_state_form_rationale(self) -> None:
        """The two branches explain themselves differently.

        ``old``/``new`` are reserved because they are *contract state forms*;
        a keyword is reserved because the grammar claims the spelling in
        expression position.  Reusing the state-form wording for ``match``
        would tell the reader a falsehood about why their program is wrong,
        so pin that the keyword branch says neither.
        """
        kw = next(
            e for e in _errors("""
public fn match(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }
""") if e.error_code == "E153"
        )
        assert "state form" not in kw.rationale.lower(), kw.rationale
        assert "keyword" in kw.rationale.lower(), kw.rationale
        # And the old/new branch keeps its own explanation.
        state = next(
            e for e in _errors("""
public fn old(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }
""") if e.error_code == "E153"
        )
        assert "state form" in state.rationale.lower(), state.rationale

    def test_handle_stays_legal(self) -> None:
        """``handle`` is carved out — CRITICAL positive control.

        ``public fn handle(@Request -> @Response)`` is the ``vera serve`` /
        ``wasi:http`` entry point (spec §9.5.6), invoked by the *host*, so it
        is legitimate despite being uncallable from Vera source.  This is the
        shape of ``examples/http_server.vera`` and
        ``tests/conformance/ch09_http_server.vera``; if the reservation ever
        swallows it, both break and `vera serve` loses its entry point.
        """
        errs = _errors("""
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) ->
      Response(200, map_new(), @String.0)
  }
}
""")
        assert self._codes(errs) == [], self._codes(errs)

    def test_where_helper_named_match_is_E153(self) -> None:
        """The where-helper recursion covers keywords too.

        A helper is called in expression position exactly like a top-level
        function, so ``match(...)`` in the parent body hits the same grammar
        wall one scope deeper.  Inherited from the set-driven gate; pinned so
        a future refactor that splits the branches cannot drop it.
        """
        errs = _errors("""
public fn caller(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ @Int.0 }
where {
  fn match(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { 5 }
}
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_keyword_E153_is_the_only_diagnostic(self) -> None:
        """The rejection must not cascade into secondary errors."""
        errs = _errors("""
public fn match(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ 5 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ 0 }
""")
        codes = self._codes(errs)
        assert "E153" in codes, codes
        assert [c for c in codes if c != "E153"] == [], codes

    def test_names_merely_beginning_with_a_keyword_are_allowed(self) -> None:
        """Whole-identifier matching, not prefix matching.

        The grammar reserves the exact tokens only, so ``matched(3)`` and
        friends parse as ordinary calls and must stay legal — a naive
        ``startswith`` would break every one of them.
        """
        for name in ("matched", "iffy", "letter", "asserting", "forall2",
                     "existsp", "fnord", "truthy", "falsey", "assumed",
                     "handler"):
            errs = _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{ {name}(3) }}
""")
            assert self._codes(errs) == [], (name, self._codes(errs))

    def test_imported_module_fn_named_match_is_E153(self) -> None:
        """A module declaring ``fn match`` surfaces E153 into its importer,
        carrying the *module's* file path — same mechanism as E151/E152 and
        the ``old``/``new`` branch."""
        mod_src = (
            "module lexy;\n"
            "public fn match(@Int -> @Int)\n"
            "  requires(true) ensures(@Int.result >= 0) effects(pure)\n"
            "{ 5 }\n"
        )
        mod = _resolved_module(("lexy",), mod_src)
        prog = parse_to_ast(
            "import lexy;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        codes = [d.error_code for d in diags]
        assert "E153" in codes, codes
        e153 = next(d for d in diags if d.error_code == "E153")
        assert e153.location.file == str(mod.file_path), e153.location.file

    def test_module_qualified_keyword_call_route_is_closed(self) -> None:
        """E153 fires even where a qualified call site proved reachability.

        Probed on the pre-#1187 tree: this exact program — module export
        named ``match``, importer calling ``lexy::match(5)`` — type-checked
        AND ran, printing 6.  The qualified route parses through the
        module-call rule rather than any keyword rule, so "no program can
        reach it" was false for module exports, exactly as #1181 found for
        ``old``.  The reservation closes the route deliberately (breaking for
        such an export) and the breakage is loud and located at the module's
        declaration.
        """
        mod_src = (
            "module lexy;\n"
            "public fn match(@Int -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ @Int.0 + 1 }\n"
        )
        mod = _resolved_module(("lexy",), mod_src)
        prog = parse_to_ast(
            "import lexy;\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ lexy::match(5) }\n"
        )
        diags = typecheck(prog, source="", resolved_modules=[mod])
        codes = [d.error_code for d in diags]
        assert "E153" in codes, codes
        e153 = next(d for d in diags if d.error_code == "E153")
        assert e153.location.file == str(mod.file_path), e153.location.file

    @pytest.mark.parametrize("name", [*KEYWORDS, "handle"])
    def test_effect_op_named_match_never_reaches_the_gate(
        self, name: str,
    ) -> None:
        """Boundary pin: ``op <keyword>(...)`` is refused by the grammar.

        The contextual lexer admits a keyword as a ``fn`` name but not as an
        ``op`` name, so ``op match(@Int -> @Int)`` fails at parse with
        ``[E005]`` and the gate — which covers ``fn`` declarations only —
        never has to see it.  ``handle`` is included: its carve-out is for
        ``fn`` declarations, and does not (and need not) extend to ``op``.
        Pinned so a grammar change admitting the ``op`` spelling shows up as
        a failure to widen the gate rather than a silent reopening.
        """
        with pytest.raises(ParseError) as exc:
            parse_to_ast(f"""
effect Renamer {{
  op {name}(@Int -> @Int)
}}
""")
        assert exc.value.diagnostic.error_code == "E005"


class TestReservedResumeFnName:
    """A ``fn`` named ``resume`` is rejected at its declaration (E153).

    ``resume`` is unlike both earlier pieces.  It is not a grammar keyword —
    ``vera/grammar.lark`` has no ``RESUME`` terminal, and ``resume`` lexes as
    an ordinary ``LOWER_IDENT`` in every position — so the declaration parses
    *and* unqualified calls to it resolve and run outside a handler clause.
    It is not a declarable trap; it is a name collision.

    Inside a handler clause body the checker binds ``resume`` to the
    effect-resumption operator (``vera/checker/control.py``), typed from the
    handled operation's return type.  One spelling would therefore mean two
    different things depending on position — and worse, measured against the
    pre-reservation tree, a top-level ``private fn resume(@Int -> @Int)``
    made the clause bodies of an *otherwise valid* ``handle[State<Int>]``
    resolve against the user's signature: ``put(@Int) -> { resume(()) }``
    was rejected ``[E202]`` "has type Unit, expected Int", and with the
    declaration removed the identical handler checked clean.  Declaring the
    name broke working code elsewhere in the file.

    Spec §1.4 already listed ``resume`` among the identifiers that MUST NOT
    be used as function names; nothing enforced it.
    """

    @staticmethod
    def _codes(errs: list[Diagnostic]) -> list[str]:
        return [e.error_code for e in errs]

    def test_fn_named_resume_is_E153(self) -> None:
        errs = _errors("""
public fn resume(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{ 5 }
""")
        assert "E153" in self._codes(errs), self._codes(errs)
        diag = next(e for e in errs if e.error_code == "E153")
        assert "resume" in diag.description
        assert "reserved" in diag.description.lower()
        assert diag.rationale and diag.fix and diag.spec_ref
        assert "Chapter 5" in diag.spec_ref
        assert "rename" in diag.fix.lower()

    def test_private_fn_named_resume_is_E153(self) -> None:
        """Visibility-independent: the collision is with the handler binding,
        which a ``private`` declaration reaches just as well."""
        errs = _errors("""
private fn resume(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_where_helper_named_resume_is_E153(self) -> None:
        """A ``where``-helper named ``resume`` is rejected one scope deeper.

        ``tests/probes/state_handlers/dispatch_paths/w_resume.vera`` is the
        adversarial-review probe for exactly this shape.
        """
        errs = _errors("""
private fn outer(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ resume(@Int.0) }
where {
  fn resume(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 }
}
""")
        assert "E153" in self._codes(errs), self._codes(errs)

    def test_rationale_does_not_claim_resume_is_a_keyword(self) -> None:
        """The keyword branch's reason would be false here.

        It says the declaration parses only because the lexer reads the name
        after ``fn``, and that in a body the spelling is always the keyword so
        no unqualified call site can reach the declaration.  Both are false of
        ``resume``: it is never a keyword token, and a bare ``resume(7)``
        outside a handler resolved to the declaration and ran.  The diagnostic
        must give the collision reason instead.
        """
        errs = _errors("""
public fn resume(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ 5 }
""")
        diag = next(e for e in errs if e.error_code == "E153")
        assert diag.rationale is not None
        reason = diag.rationale.lower()
        assert "keyword the grammar reserves" not in reason, diag.rationale
        assert "no unqualified call site" not in reason, diag.rationale
        assert "contract state form" not in reason, diag.rationale
        assert "handler" in reason, diag.rationale

    def test_resume_stays_available_inside_handler_clauses(self) -> None:
        """The reservation is on *declarations* only.

        The handler-clause binding is injected by the checker, not declared,
        so every existing ``resume(...)`` call site is untouched.  This is the
        blast-radius pin: reserving the name must not disturb the machinery
        the name exists for.
        """
        _check_ok("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(5) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""")

    def test_wrong_typed_resume_argument_in_a_clause_is_still_E202(self) -> None:
        """The clause binding stays type-checked, not merely present.

        The companion to
        :meth:`test_resume_stays_available_inside_handler_clauses`: that one
        shows a correctly-typed ``resume`` still checks, this one shows a
        wrongly-typed one is still caught.  A binding that accepted anything
        would satisfy the first test alone.  ``State<Int>``'s ``get`` returns
        ``Int``, so the clause's ``resume`` takes an ``Int`` and a ``String``
        argument is E202.
        """
        errs = _errors("""
public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume("bad") },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""")
        assert "E202" in self._codes(errs), self._codes(errs)
        diag = next(e for e in errs if e.error_code == "E202")
        assert "resume" in diag.description, diag.description

    def test_a_rejected_resume_declaration_does_not_accuse_a_valid_handler(
        self,
    ) -> None:
        """E153 is the whole story; the handler in the same file is innocent.

        The rejected declaration used to stay in ``env.functions``, where the
        lexically-scoped call lookup preferred it over the binding the clause
        installs, so `put(@Int) -> { resume(()) }` — correct code — drew a
        second error reading "has type Unit, expected Int", whose stated fix
        would have broken it.  Same reason E151 and E152 skip registering what
        they reject: one fault, one diagnostic, at the declaration.
        """
        errs = _errors("""
private fn resume(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 }

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(5) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
""")
        assert self._codes(errs) == ["E153"], [
            (e.error_code, e.description) for e in errs
        ]

    def test_a_rejected_resume_where_helper_does_not_accuse_its_handler(
        self,
    ) -> None:
        """The same, one scope deeper.

        A where-helper is registered by the shared ``register_fn`` walk, so
        stripping it at the top level alone would leave the cascade in place
        here.
        """
        errs = _errors("""
private fn outer(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  handle[State<Int>](@Int = 1) {
    get(@Unit) -> { resume(5) },
    put(@Int) -> { resume(()) }
  } in {
    get(())
  }
}
where {
  fn resume(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  { @Int.0 }
}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ outer(()) }
""")
        assert self._codes(errs) == ["E153"], [
            (e.error_code, e.description) for e in errs
        ]

    def test_resume_set_is_its_own_named_piece(self) -> None:
        """``resume`` must not be filed under the keyword or state-form sets.

        Both carry a rationale that would be false for it, and
        ``TestReservedKeywordFnName.test_keyword_tuple_matches_checker_set``
        pins the keyword set against a per-keyword test list ``resume`` has no
        business joining.
        """
        from vera.checker.registration import (
            _HANDLER_OPERATOR_FN_NAMES,
            _KEYWORD_FN_NAMES,
            _RESERVED_FN_NAMES,
            _STATE_FORM_FN_NAMES,
        )

        assert _HANDLER_OPERATOR_FN_NAMES == frozenset({"resume"})
        assert "resume" not in _KEYWORD_FN_NAMES
        assert "resume" not in _STATE_FORM_FN_NAMES
        assert "resume" in _RESERVED_FN_NAMES


# =====================================================================
# Reserved CONTEXTUAL keyword function names (E153) — #1296
# =====================================================================

class TestReservedContextualKeywordFnName:
    """A ``fn`` named after a *contextual* grammar keyword is rejected
    (E153, #1296).

    The fourth piece of :data:`_RESERVED_FN_NAMES`, and the one whose
    members are **not** declarable traps.  Every name here declares, type
    checks, verifies, compiles, runs, and round-trips ``vera fmt``; a
    bare call reaches it and returns its value.  Lark's contextual lexer
    admits the spelling as ``LOWER_IDENT`` wherever a name is expected and
    reads it as the keyword only where the keyword's own construct is being
    parsed, so nothing collides.

    **Probe record** (run against the pre-#1296 tree, ``private fn
    <name>(@Int -> @Int)`` declared and called from ``main``; 21 names ×
    six positions plus four interaction shapes):

    * All 21 — declaration accepted, bare call accepted, ``vera verify``
      proves the contracts, ``vera run`` returns the computed value, and
      ``vera fmt --check`` is clean.  Still accepted when called from
      inside a contract clause, from an ``if``/``then``/``else`` branch,
      from a function that itself carries a ``where { }`` block, and after
      a ``let``.  No positional ambiguity: unlike ``resume`` these do not
      shadow an injected binding, and unlike ``match`` they parse at a call
      site.
    * ``data`` / ``type`` / constructor positions — refused ``[E005]`` for
      every name, but by the *case* rail rather than by any reservation:
      the grammar binds every type-namespace name as ``UPPER_IDENT`` and
      every keyword is lowercase, so spec §1.4's "type names" half is
      vacuous by construction and only the function-name half can be
      violated.  Pinned by ``test_type_namespace_half_is_vacuous``.

    So the reservation cannot rest on unreachability — that claim is false
    for all 21 — and this branch must never reuse the #1187 wording.  It
    rests on spec §1.4 reserving the identifier, DESIGN principle 1
    (an unenforced MUST is a spec/implementation divergence, whatever the
    program does at runtime) and principle 6 (fewer valid programs).
    ``test_rationale_makes_no_unreachability_claim`` is the pin.

    **Derived, not hand-listed.**  The set comes from ``vera/grammar.lark``
    itself, the shape :func:`builtin_effect_names` already uses for E152, so
    a keyword added to the grammar is gated the moment it is added.  Four of
    the 21 — ``ability``, ``effects``, ``op`` and ``result`` — are grammar
    keywords spec §1.4 never listed, and were found by the derivation rather
    than by the issue.  ``test_reserved_set_is_derived_from_the_grammar``
    pins the derivation against the grammar file.
    """

    #: The names this branch newly reserves (all 21; ``handle`` excluded as
    #: the host-invoked carve-out, and the #1187/#1181 pieces excluded as
    #: they keep their own rationales).
    CONTEXTUAL = (
        # The seventeen spec §1.4 lists and nothing enforced (#1296).
        "then", "else", "data", "type", "module", "import", "public",
        "private", "requires", "ensures", "invariant", "decreases",
        "effect", "with", "in", "where", "pure",
        # Four the grammar reserves that spec §1.4 never listed.
        "ability", "effects", "op", "result",
    )

    #: Wording from the #1187 keyword branch that is FALSE for these names.
    FALSE_CLAIMS = (
        "no unqualified call site can reach",
        "does not parse as a call",
        "could never be called",
        "always lexed as the keyword",
        "dead code",
    )

    @staticmethod
    def _codes(errs: list[Diagnostic]) -> list[str]:
        return [e.error_code for e in errs]

    def test_reserved_set_is_derived_from_the_grammar(self) -> None:
        """The reservation is computed from ``grammar.lark``, not hand-listed.

        Reads the grammar file independently of the checker and asserts that
        every identifier-shaped string literal it claims — minus the
        host-invoked carve-out — is reserved.  This is the mutation-catching
        pin: replacing the derivation with a hand-list and dropping any one
        keyword fails here, which is exactly how #1296 arose (a hand-list
        that had silently fallen 21 names behind the grammar).

        ``_`` is excluded because the wildcard pattern is not a valid
        ``LOWER_IDENT`` and so can never be a function name.
        """
        import re

        from vera.checker.registration import (
            _HOST_INVOKED_FN_NAMES,
            _RESERVED_FN_NAMES,
        )
        from vera.parser import _GRAMMAR_PATH

        src = re.sub(r"//[^\n]*", "", _GRAMMAR_PATH.read_text(encoding="utf-8"))
        literals = {
            lit for lit in re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', src)
            if re.fullmatch(r"[a-z][A-Za-z0-9_]*", lit)
        }
        # The grammar really does claim these, so the pin has teeth.
        assert {"with", "where", "op", "result"} <= literals, sorted(literals)
        missing = (literals - _HOST_INVOKED_FN_NAMES) - _RESERVED_FN_NAMES
        assert missing == set(), sorted(missing)

    def test_contextual_tuple_matches_checker_set(self) -> None:
        """``CONTEXTUAL`` mirrors the checker's contextual piece exactly.

        The sibling of ``test_keyword_tuple_matches_checker_set``: a name
        entering the derived set without a per-name cell here fails this pin
        instead of silently escaping coverage.
        """
        from vera.checker.registration import _CONTEXTUAL_KEYWORD_FN_NAMES

        assert set(self.CONTEXTUAL) == _CONTEXTUAL_KEYWORD_FN_NAMES

    @pytest.mark.parametrize("name", CONTEXTUAL)
    def test_contextual_keyword_fn_name_is_E153(self, name: str) -> None:
        """Each contextual keyword is refused at the declaration site,
        fully tagged per spec §0.5.1."""
        errs = _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}
""")
        assert "E153" in self._codes(errs), (name, self._codes(errs))
        diag = next(e for e in errs if e.error_code == "E153")
        assert name in diag.description, diag.description
        assert "reserved" in diag.description.lower(), diag.description
        assert diag.rationale and diag.fix and diag.spec_ref
        assert "Chapter 5" in diag.spec_ref, diag.spec_ref
        assert "rename" in diag.fix.lower(), diag.fix

    @pytest.mark.parametrize("name", CONTEXTUAL)
    def test_private_contextual_keyword_fn_name_is_E153(
        self, name: str,
    ) -> None:
        """Visibility-independent, as every other branch is."""
        errs = _errors(f"""
private fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}
""")
        assert "E153" in self._codes(errs), (name, self._codes(errs))

    @pytest.mark.parametrize("name", CONTEXTUAL)
    def test_where_helper_contextual_keyword_is_E153(self, name: str) -> None:
        """The where-helper recursion covers this branch too.

        The pre-fix sweep found the helper position mirroring the top-level
        one for all 21 (declared, called, ran), so the gate must reach it
        identically or the reservation is half-applied.
        """
        errs = _errors(f"""
public fn caller(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ @Int.0 }}
where {{
  fn {name}(@Int -> @Int)
    requires(true) ensures(true) effects(pure)
  {{ @Int.0 }}
}}
""")
        assert "E153" in self._codes(errs), (name, self._codes(errs))

    @pytest.mark.parametrize("name", CONTEXTUAL)
    def test_rationale_makes_no_unreachability_claim(self, name: str) -> None:
        """CRITICAL: the branch must not ship the #1187 wording.

        Every phrase in ``FALSE_CLAIMS`` is true of ``match`` and false of
        these names — each one is callable, and the pre-fix probe ran them.
        A diagnostic asserting otherwise would tell the reader a falsehood
        about their own program, which the diagnostic-fields contract
        (spec §0.5.1, #955) does not waive for any field.
        """
        diag = next(
            e for e in _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{{ 5 }}
""") if e.error_code == "E153"
        )
        text = f"{diag.rationale} {diag.fix}".lower()
        for claim in self.FALSE_CLAIMS:
            assert claim not in text, (name, claim, diag.rationale)
        # It must still say WHY: the identifier is reserved by the spec.
        assert "reserved" in text, (name, diag.rationale)
        # And it must not borrow either sibling branch's explanation.
        assert "state form" not in diag.rationale.lower(), diag.rationale
        assert "resumes a suspended" not in diag.rationale.lower(), (
            diag.rationale
        )

    @pytest.mark.parametrize("name", CONTEXTUAL)
    def test_fix_suggests_a_usable_replacement(self, name: str) -> None:
        """The fix names a concrete replacement that is not itself reserved.

        DESIGN principle 1 asks for "an instruction, not a status report".
        A bare ``{name}_fn`` template produces ``in_fn`` / ``type_fn`` /
        ``pure_fn``, which is advice no author would take, so the branch
        carries a per-name suggestion where the generic suffix misleads.
        Pinned by property — the suggested identifier must be a legal Vera
        function name, must not be reserved, and must not be that generic
        template — rather than by exact wording, so the table can be
        improved without churning the test.  The suggestion is read from
        the clause that makes it, not swept out of the whole fix text:
        the sweep's other catches are boilerplate, so it went green for a
        table entry that had been deleted.
        """
        import re

        from vera.checker.registration import (
            _builtin_reject_names,
            _RESERVED_FN_NAMES,
        )

        diag = next(
            e for e in _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{{ 5 }}
""") if e.error_code == "E153"
        )
        # ANCHORED to the sentence that makes the suggestion.  A sweep for
        # every quoted lowercase word in `diag.fix` also collects the
        # substring example (`'{name}_value'`) and `'handle'` (offered as
        # the one surviving keyword, not as a replacement), both of which
        # are boilerplate present whatever the per-name table says — so a
        # table entry replaced by a prose word, or deleted outright, left
        # the sweep with two words that pass every check below.
        m = re.search(
            r"Rename the function to an identifier that is not a keyword"
            r" — '([a-z][A-Za-z0-9_]*)'",
            diag.fix,
        )
        assert m is not None, diag.fix
        suggestion = m.group(1)
        assert suggestion != name, diag.fix
        # Not the generic `{name}_fn` template: that is the fallback this
        # branch's per-name table exists to replace, and `in_fn` / `type_fn`
        # / `pure_fn` is the advice the docstring above calls unusable.
        assert suggestion != f"{name}_fn", (name, diag.fix)
        # Not reserved (E153 again) and not a built-in (E151 instead) —
        # advice that trades one error for another is not a fix.
        assert suggestion not in _RESERVED_FN_NAMES, (name, suggestion,
                                                      diag.fix)
        assert suggestion not in _builtin_reject_names(), (name, suggestion,
                                                           diag.fix)

    def test_handle_stays_legal(self) -> None:
        """NEGATIVE CONTROL: the carve-out survives a derived set.

        Deriving from the grammar pulls ``handle`` in with every other
        keyword, so the subtraction is what keeps ``vera serve`` its entry
        point.  If the derivation ever forgets it, ``examples/http_server
        .vera`` and ``ch09_http_server`` break together.
        """
        errs = _errors("""
public fn handle(@Request -> @Response)
  requires(true) ensures(true) effects(<HttpServer>)
{
  match @Request.0 {
    Request(@String, @String, @Map<String, String>, @String) ->
      Response(200, map_new(), @String.0)
  }
}
""")
        assert self._codes(errs) == [], self._codes(errs)

    def test_names_merely_containing_a_contextual_keyword_are_allowed(
        self,
    ) -> None:
        """NEGATIVE CONTROL: the reservation is the whole identifier.

        A substring test would reject a large share of ordinary Vera —
        ``with_it``, ``then_value`` and ``older`` are unremarkable function
        names, and ``in`` is a substring of a great many words.
        """
        for name in (
            "then_value", "older", "with_it", "invariants", "typed",
            "public_key", "purity", "wherever", "import_path", "results",
            "operation", "effective", "ability_of", "indexed", "dataset",
        ):
            errs = _errors(f"""
public fn {name}(@Int -> @Int)
  requires(true) ensures(@Int.result >= 0) effects(pure)
{{ 5 }}

public fn main(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{{ {name}(3) }}
""")
            assert self._codes(errs) == [], (name, self._codes(errs))

    def test_type_namespace_half_is_vacuous(self) -> None:
        """Spec §1.4's "type names" half cannot be violated by construction.

        Every type-namespace binder in the grammar is ``UPPER_IDENT`` and
        every keyword is lowercase, so ``data with`` / ``type with = Int;``
        fail at *parse* — and would fail identically for any lowercase name.
        Pinned so the spec's corrected wording ("function names") stays
        backed by the grammar, and so a future grammar change admitting a
        lowercase type name shows up here rather than reopening the hole.
        """
        for src in ("private data with {\n  MkX(Int)\n}\n",
                    "type with = Int;\n",
                    "private data Holder {\n  with(Int)\n}\n"):
            with pytest.raises(ParseError):
                parse_to_ast(src)
        # Control: an ordinary LOWERCASE name fails the same way, proving the
        # rejection is the case rail and not the reservation.  All THREE
        # positions are controlled — without the constructor one, nothing
        # showed that `Holder { with(Int) }` above failed at the case rail
        # rather than at the function-name reservation, which is the exact
        # confusion this test exists to rule out.
        for src in ("private data helper {\n  MkX(Int)\n}\n",
                    "type helper = Int;\n",
                    "private data Holder {\n  helper(Int)\n}\n"):
            with pytest.raises(ParseError):
                parse_to_ast(src)


# =====================================================================
# Module-qualified call parse tests (#95)
# =====================================================================

class TestModuleCallParsed:
    """Module-qualified call tests using parsed :: syntax (#95)."""

    MATH_MODULE = """\
public fn magnitude(@Int -> @Int)
  requires(true)
  ensures(@Int.result >= 0)
  effects(pure)
{ if @Int.0 < 0 then { 0 - @Int.0 } else { @Int.0 } }

public fn larger(@Int, @Int -> @Int)
  requires(true)
  ensures(true)
  effects(pure)
{ if @Int.0 > @Int.1 then { @Int.0 } else { @Int.1 } }

public fn tag(@Int, @String -> @String)
  requires(true)
  ensures(true)
  effects(pure)
{ @String.0 }
"""

    def test_parsed_module_call_typechecks(self) -> None:
        """Parsed :: syntax produces ModuleCall that type-checks."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        source = """\
import math(magnitude);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ math::magnitude(@Int.0) }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_parsed_multi_segment_path(self) -> None:
        """Multi-segment path vera.math::magnitude type-checks."""
        mod = _resolved_module(("vera", "math"), self.MATH_MODULE)
        source = """\
import vera.math(magnitude);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ vera.math::magnitude(@Int.0) }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_parsed_module_call_arity_error(self) -> None:
        """Parsed :: call with wrong arity produces error."""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        source = """\
import math(magnitude);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ math::magnitude(@Int.0, @Int.0) }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert any("argument" in e.description.lower() for e in errors)

    def test_pipe_into_module_call_typechecks(self) -> None:
        """Pipe into module-qualified call type-checks without E201. (#326)"""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        source = """\
import math(magnitude);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> math::magnitude() }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_pipe_chained_module_calls_typechecks(self) -> None:
        """Chained pipes into module-qualified calls type-check. (#326)"""
        mod = _resolved_module(("math",), self.MATH_MODULE)
        source = """\
import math(magnitude);
private fn f(@Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> math::magnitude() |> math::magnitude() }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]

    def test_pipe_module_call_arg_order_regression(self) -> None:
        """LHS is prepended as first arg, not appended. (#326)

        @Int.0 |> math::tag("ok") must desugar to math::tag(value, "ok"),
        not math::tag("ok", value). tag has signature (@Int, @String -> @String),
        so if the LHS were appended the checker would see String where Int is
        expected and emit a type error — making the prepend/append distinction
        type-observable.
        """
        mod = _resolved_module(("math",), self.MATH_MODULE)
        source = """\
import math(tag);
private fn f(@Int -> @String)
  requires(true) ensures(true) effects(pure)
{ @Int.0 |> math::tag("ok") }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]


# =====================================================================
# Built-in effect redeclaration in a module (E152) — #1149
# =====================================================================


class TestModuleBuiltinEffectRedeclaration1149:
    """A module redeclaring a built-in effect surfaces E152 into its importer.

    Same reasoning as E151 for module functions (#815): the importer compiles
    the module's bodies, and codegen routes every qualified ``IO.op(...)`` to
    the fixed host import regardless of the declaration.  A module checked
    only as a dependency would otherwise carry a divergent redeclaration
    through to invalid WASM with no diagnostic anywhere.
    """

    MODULE_SRC = """\
effect IO {
  op print(String, String -> Unit);
}

public fn shout(@String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(@String.0, "!") }
"""

    def test_module_effect_redeclaration_surfaces_to_importer(self) -> None:
        mod = _resolved_module(("shouty",), self.MODULE_SRC)
        source = """\
import shouty(shout);
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ shouty::shout("hi") }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        # EXACTLY what `vera check shouty.vera` reports standalone, which
        # since #1244 is what an importer reports too — the module's bodies
        # are checked under the module's own import filter regardless of
        # entry point, so its `IO.print(a, b)` is diagnosed here as well.
        # E203 is the load-bearing half: it names the CANONICAL built-in's
        # arity ("expects 1 argument(s), got 2"), so the pre-#1244 property
        # this case was written for — the rejected block is not registered —
        # is asserted more directly than by its absence.
        codes = [d.error_code for d in diags if d.severity == "error"]
        assert codes == ["E152", "E203"], [
            (d.error_code, d.description) for d in diags
        ]
        assert any(
            "expects 1 argument" in d.description
            for d in diags if d.error_code == "E203"
        ), [d.description for d in diags]

    def test_module_user_effect_still_accepted(self) -> None:
        """The negative control: a module's own effect name is untouched."""
        mod = _resolved_module(("logger",), """\
effect Logger {
  op log(String -> Unit);
}

public fn shout(@String -> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{ Logger.log(@String.0) }
""")
        # An effect declaration is module-local (spec §8.4.1), so the
        # importer names `Logger` in its row through its own copy — without
        # one the row names nothing in scope (E338, #1489).
        source = """\
import logger(shout);
effect Logger {
  op log(String -> Unit);
}
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{ logger::shout("hi") }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]
