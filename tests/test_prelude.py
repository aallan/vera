"""Tests for vera.prelude — Option/Result combinator injection."""

from __future__ import annotations

from vera import ast
from vera.parser import parse
from vera.transform import transform
from vera.prelude import inject_prelude


def _make_program(src: str) -> ast.Program:
    tree = parse(src)
    return transform(tree)


class TestPreludeDetection:
    """Tests for ADT detection and conditional injection."""

    def test_option_detected(self) -> None:
        """Option combinators injected when Option<T> defined."""
        prog = _make_program(
            "public data Option<T> { None, Some(T) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        fn_names = {
            tld.decl.name
            for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
        }
        assert "option_unwrap_or" in fn_names
        assert "option_map" in fn_names
        assert "option_and_then" in fn_names

    def test_result_detected(self) -> None:
        """Result combinators injected when Result<T, E> defined."""
        prog = _make_program(
            "public data Result<T, E> { Ok(T), Err(E) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        fn_names = {
            tld.decl.name
            for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
        }
        assert "result_unwrap_or" in fn_names
        assert "result_map" in fn_names
        # Option combinators not injected (no Option defined)
        assert "option_map" not in fn_names

    def test_no_injection_without_adt(self) -> None:
        """No Option/Result injection when neither defined.

        Array operations (map, filter, fold) are always injected
        regardless of Option/Result declarations.
        """
        prog = _make_program(
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        orig_len = len(prog.declarations)
        inject_prelude(prog)
        # 9 array declarations: 3 type aliases + 6 functions
        assert len(prog.declarations) == orig_len + 9

    def test_non_standard_option_ignored(self) -> None:
        """Non-standard Option (missing Some) not detected.

        Array operations are still injected (always available).
        """
        prog = _make_program(
            "public data Option<T> { None, Just(T) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        orig_len = len(prog.declarations)
        inject_prelude(prog)
        # Only array declarations injected (9), not Option combinators
        assert len(prog.declarations) == orig_len + 9


class TestPreludeShadowing:
    """Tests for user-defined function shadowing."""

    def test_user_fn_shadows_combinator(self) -> None:
        """User-defined option_map is not overwritten."""
        prog = _make_program(
            "public data Option<T> { None, Some(T) }\n"
            "public fn option_map(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        # The user's option_map should still be there, unmodified
        user_fns = [
            tld.decl
            for tld in prog.declarations
            if isinstance(tld.decl, ast.FnDecl)
            and tld.decl.name == "option_map"
        ]
        assert len(user_fns) >= 1
        # The user-defined one has no forall_vars
        assert any(fn.forall_vars is None for fn in user_fns)


class TestPreludeTypeAliases:
    """Tests for type alias injection."""

    def test_type_aliases_injected(self) -> None:
        """OptionMapFn and OptionBindFn injected with Option."""
        prog = _make_program(
            "public data Option<T> { None, Some(T) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        alias_names = {
            tld.decl.name
            for tld in prog.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }
        assert "OptionMapFn" in alias_names
        assert "OptionBindFn" in alias_names

    def test_result_alias_injected(self) -> None:
        """ResultMapFn injected with Result."""
        prog = _make_program(
            "public data Result<T, E> { Ok(T), Err(E) }\n"
            "public fn main(@Unit -> @Int)\n"
            "  requires(true) ensures(true) effects(pure)\n"
            "{ 0 }\n"
        )
        inject_prelude(prog)
        alias_names = {
            tld.decl.name
            for tld in prog.declarations
            if isinstance(tld.decl, ast.TypeAliasDecl)
        }
        assert "ResultMapFn" in alias_names


class TestPreludeEndToEnd:
    """End-to-end tests verifying combinators compile and run."""

    def test_option_unwrap_or_some(self) -> None:
        """option_unwrap_or(Some(42), 0) returns 42."""
        from tests.test_codegen_closures import _run
        src = """\
public data Option<T> { None, Some(T) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(Some(42), 0)
}
"""
        assert _run(src, "test") == 42

    def test_option_map_some(self) -> None:
        """option_map(Some(10), +1) returns Some(11)."""
        from tests.test_codegen_closures import _run
        src = """\
public data Option<T> { None, Some(T) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(
    option_map(Some(10), fn(@Int -> @Int) effects(pure) { @Int.0 + 1 }),
    0
  )
}
"""
        assert _run(src, "test") == 11

    def test_option_and_then_some(self) -> None:
        """option_and_then(Some(5), *2) returns Some(10)."""
        from tests.test_codegen_closures import _run
        src = """\
public data Option<T> { None, Some(T) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  option_unwrap_or(
    option_and_then(Some(5), fn(@Int -> @Option<Int>) effects(pure) {
      Some(@Int.0 * 2)
    }),
    0
  )
}
"""
        assert _run(src, "test") == 10

    def test_result_unwrap_or_ok(self) -> None:
        """result_unwrap_or(Ok(77), 0) returns 77."""
        from tests.test_codegen_closures import _run
        src = """\
public data Result<T, E> { Ok(T), Err(E) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  result_unwrap_or(Ok(77), 0)
}
"""
        assert _run(src, "test") == 77

    def test_result_map_ok(self) -> None:
        """result_map(Ok(100), -1) returns Ok(99)."""
        from tests.test_codegen_closures import _run
        src = """\
public data Result<T, E> { Ok(T), Err(E) }
public fn test(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  result_unwrap_or(
    result_map(Ok(100), fn(@Int -> @Int) effects(pure) { @Int.0 - 1 }),
    0
  )
}
"""
        assert _run(src, "test") == 99
