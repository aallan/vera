"""Tests for the Vera type checker — modules (module calls, cross-module typing, visibility, builtin redefinition).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from pathlib import Path

from vera import ast
from vera.checker import typecheck
from vera.errors import Diagnostic
from vera.parser import parse_to_ast
from vera.resolver import ResolvedModule

from tests.checker_helpers import (
    _check_err,
    _check_ok,
    _errors,
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

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        from vera.resolver import ResolvedModule as RM
        prog = parse_to_ast(source)
        return RM(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

    # -- Bare calls (parsed normally) -----------------------------------

    def test_bare_call_resolves_type(self) -> None:
        """import m(magnitude); magnitude(42) -> no errors."""
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("gen",), self.GENERIC_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), """\
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
        mod = self._resolved(("col",), self.COLLECTIONS_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("vera", "math"), self.MATH_MODULE)
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

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str,
    ) -> ResolvedModule:
        """Build a ResolvedModule from source text."""
        from vera.resolver import ResolvedModule as RM
        prog = parse_to_ast(source)
        return RM(
            path=path,
            file_path=Path(f"/fake/{'/'.join(path)}.vera"),
            program=prog,
            source=source,
        )

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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mod",), self.MIXED_MODULE)
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
        mod = self._resolved(("mymod",), self.MIXED_MODULE)
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

    @staticmethod
    def _resolved(
        path: tuple[str, ...], source: str
    ) -> "ResolvedModule":
        from vera.resolver import ResolvedModule
        prog = parse_to_ast(source)
        return ResolvedModule(
            path=path, file_path=Path("/fake"), program=prog, source=source,
        )

    def test_parsed_module_call_typechecks(self) -> None:
        """Parsed :: syntax produces ModuleCall that type-checks."""
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("vera", "math"), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
        mod = self._resolved(("math",), self.MATH_MODULE)
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
