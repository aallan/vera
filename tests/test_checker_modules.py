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


def _resolved_module(path: tuple[str, ...], source: str) -> ResolvedModule:
    """Build a ResolvedModule from source text (shared test helper)."""
    prog = parse_to_ast(source)
    return ResolvedModule(
        path=path,
        file_path=Path(f"/fake/{'/'.join(path)}.vera"),
        program=prog,
        source=source,
    )


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
        """PR #1191's core guarantee: shadowing `OptionMapFn` is fine."""
        codes = self._codes("type OptionMapFn = Int;\n")
        assert "E154" not in codes, codes

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
    * ``resume``, ``throw``, ``with``, ``in``, ``effect``, ``op``, ``data``,
      ``type``, ``import``, ``public``, ``private``, ``requires``,
      ``ensures``, ``effects``, ``decreases``, ``where``, ``then``, ``else``,
      ``pure``, ``invariant`` — declaration *and* call both accepted.  Not
      reserved; nothing is wrong with them.
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
        # Exactly E152, not merely "E152 among others": the module's own
        # divergent `IO.print(a, b)` call must NOT cascade a second diagnostic
        # into the importer.  Only E151/E152 are harvested from the module's
        # isolated check, so a cascade here would mean the rejected block had
        # been registered after all.
        codes = [d.error_code for d in diags if d.severity == "error"]
        assert codes == ["E152"], [
            (d.error_code, d.description) for d in diags
        ]

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
        source = """\
import logger(shout);
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<Logger>)
{ logger::shout("hi") }
"""
        prog = parse_to_ast(source)
        diags = typecheck(prog, source=source, resolved_modules=[mod])
        errors = [d for d in diags if d.severity == "error"]
        assert errors == [], [e.description for e in errors]
