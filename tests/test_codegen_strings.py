"""Tests for vera.codegen — strings (string literals + IO bindings, WAT escaping, signatures, format, core string ops, char classification, string utilities).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations

import json

import pytest

from vera.codegen import (
    compile,
    execute,
)
from vera.codegen.api import WasmTrapError
from vera.parser import parse_file
from vera.transform import transform

from tests.codegen_helpers import (
    _IO_PRELUDE,
    _assert_no_host_imports_for_inline_builtins,
    _compile_ok,
    _run,
    _run_io,
)


class TestStringLitIO:
    def test_hello_world(self) -> None:
        """First light: Hello, World!"""
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World!") }
"""
        assert _run_io(source, fn="main") == "Hello, World!"

    def test_empty_string(self) -> None:
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("") }
"""
        assert _run_io(source, fn="main") == ""

    def test_multiple_prints(self) -> None:
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("Hello, ");
  IO.print("World!")
}
"""
        assert _run_io(source, fn="main") == "Hello, World!"

    def test_string_dedup(self) -> None:
        """Identical strings should be deduplicated in the data section."""
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print("abc");
  IO.print("abc")
}
"""
        result = _compile_ok(source)
        # The string "abc" should appear only once in the data section
        assert result.wat.count('"abc"') == 1
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "abcabc"

    def test_special_characters(self) -> None:
        """Strings with punctuation and spaces."""
        source = _IO_PRELUDE + """\
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("Hello, World! 123 @#$") }
"""
        assert _run_io(source, fn="main") == "Hello, World! 123 @#$"

    def test_io_with_pure_functions(self) -> None:
        """IO functions coexist with pure functions in the same module."""
        source = _IO_PRELUDE + """\
public fn add(@Int, @Int -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.1 + @Int.0 }

public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("hello") }
"""
        result = _compile_ok(source)
        assert "add" in result.exports
        assert "main" in result.exports
        assert _run_io(source, fn="main") == "hello"

    def test_hello_world_example_file(self) -> None:
        """The actual examples/hello_world.vera compiles and runs."""
        from pathlib import Path
        example_path = Path(__file__).parent.parent / "examples" / "hello_world.vera"
        source = example_path.read_text(encoding="utf-8")
        tree = parse_file(str(example_path))
        ast = transform(tree)
        result = compile(ast, source=source, file=str(example_path))
        assert result.ok
        exec_result = execute(result, fn_name="main")
        assert exec_result.stdout == "Hello, World!"


# =====================================================================
# String escape sequences — unit tests for WAT escaping
# =====================================================================


class TestWatStringEscaping:
    """Unit tests for the _escape_wat_string helper that escapes
    special characters for WAT data section string literals."""

    @staticmethod
    def _escape(s: str) -> str:
        """Call the WAT string escaper."""
        from vera.codegen import CodeGenerator
        return CodeGenerator._escape_wat_string(s)

    def test_plain_ascii(self) -> None:
        assert self._escape("Hello, World!") == "Hello, World!"

    def test_double_quote(self) -> None:
        """Double quotes must be escaped in WAT."""
        assert self._escape('say "hi"') == "say \\22hi\\22"

    def test_backslash(self) -> None:
        """Backslashes must be escaped in WAT."""
        assert self._escape("a\\b") == "a\\\\b"

    def test_newline(self) -> None:
        """Newline characters escape to \\n in WAT."""
        assert self._escape("line1\nline2") == "line1\\nline2"

    def test_tab(self) -> None:
        """Tab characters escape to \\t in WAT."""
        assert self._escape("col1\tcol2") == "col1\\tcol2"

    def test_unicode_emoji(self) -> None:
        """Non-ASCII chars are encoded as hex bytes in WAT."""
        # '😀' is U+1F600, encoded as 4 UTF-8 bytes: f0 9f 98 80
        result = self._escape("😀")
        assert result == "\\f0\\9f\\98\\80"

    def test_mixed_special_chars(self) -> None:
        """Mix of special characters."""
        result = self._escape('a"b\\c\nd')
        assert result == "a\\22b\\\\c\\nd"

    def test_empty_string(self) -> None:
        """Empty string produces empty output."""
        assert self._escape("") == ""


# =====================================================================
# String escape sequences — end-to-end (Vera source → WASM execution)
# =====================================================================


class TestStringEscapeE2E:
    """End-to-end tests: Vera escape sequences through compile + execute."""

    def test_newline_in_print(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("line1\nline2") }
'''
        assert _run_io(source, fn="main") == "line1\nline2"

    def test_tab_in_print(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("col1\tcol2") }
'''
        assert _run_io(source, fn="main") == "col1\tcol2"

    def test_backslash_roundtrip(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("a\\b") }
'''
        assert _run_io(source, fn="main") == "a\\b"

    def test_unicode_basic(self) -> None:
        source = _IO_PRELUDE + r'''
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print("\u{41}\u{42}\u{43}") }
'''
        assert _run_io(source, fn="main") == "ABC"

    def test_string_length_with_escapes(self) -> None:
        """Escaped \\n is one character, so length should be 3."""
        source = r'''
public fn len(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_length("a\nb") }
'''
        assert _run(source, fn="len") == 3

    def test_string_length_non_ascii_counts_utf8_bytes(self) -> None:
        """#802: string_length counts UTF-8 BYTES at runtime — "é" (U+00E9) is
        2 bytes and "😀" (U+1F600) is 4 bytes, each a single code point.  This
        pins the runtime premise the verifier's literal byte-model relies on:
        if codegen regressed to code-point counting, the verifier-side
        soundness tests (test_string_length_soundness.py) would stay green but
        this would catch it."""
        two = r'''
public fn len(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_length("\u{e9}") }
'''
        assert _run(two, fn="len") == 2
        four = r'''
public fn len(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ string_length("\u{1F600}") }
'''
        assert _run(four, fn="len") == 4

    def test_string_length_deferred_contract_enforced_at_runtime(self) -> None:
        """#802 soundness loop: a slot-arg string_length contract that `vera
        verify` DEFERS to Tier 3 is still enforced at runtime — the false
        `ensures(@Int.result == 1)` over "é" (2 bytes) raises a postcondition
        violation.  This proves the deferral is *sound* (the runtime catches the
        false contract verify could not prove), not merely imprecise — it closes
        the loop the verifier-side deferral tests in
        tests/test_string_length_soundness.py leave open."""
        source = r'''
public fn f(@String -> @Int)
  requires(true) ensures(@Int.result == 1) effects(pure)
{ string_length(@String.0) }
'''
        result = _compile_ok(source)
        # Pin the *exact* observable: execute() normalises every wasmtime trap
        # into a WasmTrapError, so a broad raises((WasmtimeError, Trap,
        # RuntimeError)) would green-pass on any failure — a compile/setup
        # error or a regression that traps for a different reason.  Assert the
        # contract-violation kind so the test fails iff this specific deferral
        # stops being caught.
        with pytest.raises(WasmTrapError) as excinfo:
            execute(result, fn_name="f", raw_args=["é"])
        assert excinfo.value.kind == "contract_violation"


# =====================================================================
# C6.5e: String and Array types in function signatures
# =====================================================================


class TestStringArraySignatures:
    """Tests for String and Array types in function parameters and returns."""

    def test_string_param(self) -> None:
        """Function taking a String param compiles with pair params."""
        src = """
public fn say(@String -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(@String.0) }
"""
        result = _compile_ok(src)
        assert "say" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat

    def test_string_return(self) -> None:
        """Function returning a String compiles with (result i32 i32)."""
        src = '''
public fn greeting(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        assert "greeting" in result.exports
        assert "(result i32 i32)" in result.wat

    def test_string_param_and_return(self) -> None:
        """String param + String return: identity-like function."""
        src = """
public fn echo(@String -> @String)
  requires(true) ensures(true) effects(pure)
{ @String.0 }
"""
        result = _compile_ok(src)
        assert "echo" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(result i32 i32)" in result.wat

    def test_string_call_chain(self) -> None:
        """String-returning fn called by another fn via IO.print."""
        src = '''
public fn greeting(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello world" }

public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(greeting()) }
'''
        result = _compile_ok(src)
        exec_result = execute(result)
        assert exec_result.stdout == "hello world"

    def test_array_param(self) -> None:
        """Function taking an Array<Int> param compiles with pair params."""
        src = """
public fn get_len(@Array<Int> -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(@Array<Int>.0) }
"""
        result = _compile_ok(src)
        assert "get_len" in result.exports
        assert "(param $p0_ptr i32)" in result.wat
        assert "(param $p0_len i32)" in result.wat

    def test_array_return(self) -> None:
        """Function returning an Array literal compiles."""
        src = """
public fn nums(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3] }
"""
        result = _compile_ok(src)
        assert "nums" in result.exports
        assert "(result i32 i32)" in result.wat

    def test_mixed_params(self) -> None:
        """Function with both pair and primitive params."""
        src = """
public fn add_to(@Int, @String -> @Int)
  requires(true) ensures(true) effects(pure)
{ @Int.0 + 1 }
"""
        result = _compile_ok(src)
        assert "add_to" in result.exports
        # Int param is plain i64, String param is pair
        assert "(param $p0 i64)" in result.wat
        assert "(param $p1_ptr i32)" in result.wat
        assert "(param $p1_len i32)" in result.wat
        # Can execute with Int=10, String ptr=0, len=0
        exec_result = execute(result, fn_name="add_to", args=[10, 0, 0])
        assert exec_result.value == 11

    def test_string_return_execution(self) -> None:
        """Executing a String-returning function decodes the (ptr, len) pair
        back into the original Python str (not a bare heap pointer).

        Pre-fix this test asserted ``isinstance(value, int)`` because the
        CLI displayed only the first half of the i32_pair return.  After
        the alias-codegen burndown PR (v0.0.135), execute() decodes the
        UTF-8 bytes from linear memory so `vera run` on a String-returning
        `main` shows the actual string instead of a confusing pointer.
        """
        src = '''
public fn hello(-> @String)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="hello")
        assert exec_result.value == "hello"

    def test_string_alias_return_execution(self) -> None:
        """Aliased String returns decode the same way as direct String —
        `type Greeting = String` participates in `fn_string_returns`
        because `_return_type_is_string` resolves aliases.  Locks in the
        cooperation between #583's alias work and the String-decode path.
        """
        src = '''
type Greeting = String;

public fn hello(-> @Greeting)
  requires(true) ensures(true) effects(pure)
{ "hello" }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="hello")
        assert exec_result.value == "hello"

    def test_array_return_unchanged(self) -> None:
        """Array<T> returns deliberately keep the bare-pointer fallback —
        their bytes-at-ptr aren't UTF-8 and decoding them would require
        element-type-aware formatting (separate scope).  Locks in the
        intentional asymmetry with String returns.
        """
        src = '''
public fn nums(-> @Array<Int>)
  requires(true) ensures(true) effects(pure)
{ [1, 2, 3] }
'''
        result = _compile_ok(src)
        exec_result = execute(result, fn_name="nums")
        assert isinstance(exec_result.value, int)


class TestFormatExpr:
    """Unit tests for ast.format_expr and related helpers."""

    def test_int_lit(self) -> None:
        from vera.ast import IntLit, format_expr
        assert format_expr(IntLit(value=42)) == "42"

    def test_bool_lit(self) -> None:
        from vera.ast import BoolLit, format_expr
        assert format_expr(BoolLit(value=True)) == "true"
        assert format_expr(BoolLit(value=False)) == "false"

    def test_slot_ref(self) -> None:
        from vera.ast import SlotRef, format_expr
        expr = SlotRef(type_name="Int", type_args=None, index=1)
        assert format_expr(expr) == "@Int.1"

    def test_slot_ref_with_type_args(self) -> None:
        from vera.ast import NamedType, SlotRef, format_expr
        expr = SlotRef(
            type_name="Option",
            type_args=(NamedType(name="Int", type_args=None),),
            index=0,
        )
        assert format_expr(expr) == "@Option<@Int>.0"

    def test_result_ref(self) -> None:
        from vera.ast import ResultRef, format_expr
        expr = ResultRef(type_name="Int", type_args=None)
        assert format_expr(expr) == "@Int.result"

    def test_binary_le(self) -> None:
        from vera.ast import BinOp, BinaryExpr, SlotRef, format_expr
        expr = BinaryExpr(
            op=BinOp.LE,
            left=SlotRef(type_name="Int", type_args=None, index=1),
            right=SlotRef(type_name="Int", type_args=None, index=2),
        )
        assert format_expr(expr) == "@Int.1 <= @Int.2"

    def test_unary_not(self) -> None:
        from vera.ast import BoolLit, UnaryExpr, UnaryOp, format_expr
        expr = UnaryExpr(op=UnaryOp.NOT, operand=BoolLit(value=True))
        assert format_expr(expr) == "!true"

    def test_unary_neg(self) -> None:
        from vera.ast import IntLit, UnaryExpr, UnaryOp, format_expr
        expr = UnaryExpr(op=UnaryOp.NEG, operand=IntLit(value=5))
        assert format_expr(expr) == "-5"

    def test_fn_call(self) -> None:
        from vera.ast import FnCall, IntLit, format_expr
        expr = FnCall(name="abs", args=(IntLit(value=3),))
        assert format_expr(expr) == "abs(3)"

    def test_format_fn_signature(self) -> None:
        from vera.ast import (
            BoolLit, FnDecl, NamedType, format_fn_signature,
        )
        decl = FnDecl(
            name="clamp",
            forall_vars=None,
            forall_constraints=None,
            params=(
                NamedType(name="Int", type_args=None),
                NamedType(name="Int", type_args=None),
                NamedType(name="Int", type_args=None),
            ),
            return_type=NamedType(name="Int", type_args=None),
            contracts=(),
            effect=(),
            body=(BoolLit(value=True),),
            where_fns=None,
        )
        assert format_fn_signature(decl) == "clamp(@Int, @Int, @Int -> @Int)"


# =====================================================================
# String operations
# =====================================================================


class TestStringLength:
    def test_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length("hello")
}
"""
        assert _run(src) == 5

    def test_empty(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length("")
}
"""
        assert _run(src) == 0

    def test_in_let(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Int = string_length("abc");
  @Int.0
}
"""
        assert _run(src) == 3


class TestStringConcat:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("hello", " world"))
}
"""
        assert _run_io(src) == "hello world"

    def test_empty_left(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("", "world"))
}
"""
        assert _run_io(src) == "world"

    def test_empty_right(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("hello", ""))
}
"""
        assert _run_io(src) == "hello"

    def test_both_empty(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat("", ""))
}
"""
        assert _run_io(src) == ""

    def test_concat_length(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_concat("abc", "def"))
}
"""
        assert _run(src) == 6


class TestStringSlice:
    def test_basic(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello world", 6, 11))
}
"""
        assert _run_io(src) == "world"

    def test_prefix(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 0, 3))
}
"""
        assert _run_io(src) == "hel"

    def test_empty_slice(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_slice("hello", 2, 2))
}
"""
        assert _run_io(src) == ""

    def test_slice_length(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  string_length(string_slice("hello world", 0, 5))
}
"""
        assert _run(src) == 5

    def test_slice_then_concat(self) -> None:
        src = """
effect IO { op print(String -> Unit); }
public fn main(@Unit -> @Unit)
  requires(true) ensures(true) effects(<IO>)
{
  IO.print(string_concat(
    string_slice("abcdef", 0, 3),
    string_slice("abcdef", 3, 6)
  ))
}
"""
        assert _run_io(src) == "abcdef"


class TestStringCharCode:
    def test_uppercase_a(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code("A", 0);
  @Nat.0
}
"""
        assert _run(src) == 65

    def test_digit_zero(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code("0", 0);
  @Nat.0
}
"""
        assert _run(src) == 48

    def test_second_char(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code("AB", 1);
  @Nat.0
}
"""
        assert _run(src) == 66

    def test_space(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(" ", 0);
  @Nat.0
}
"""
        assert _run(src) == 32


class TestStringFromCharCode:
    """string_from_char_code creates a single-character string from a code point."""

    def test_uppercase_a(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(string_from_char_code(65), 0);
  @Nat.0
}
"""
        assert _run(src) == 65

    def test_digit(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(string_from_char_code(48), 0);
  @Nat.0
}
"""
        assert _run(src) == 48

    def test_space(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_char_code(string_from_char_code(32), 0);
  @Nat.0
}
"""
        assert _run(src) == 32

    def test_length_is_one(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_from_char_code(65));
  @Nat.0
}
"""
        assert _run(src) == 1

    def test_concat_builds_string(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  let @String = string_concat(string_from_char_code(65), string_from_char_code(66));
  string_starts_with(@String.0, "AB")
}
"""
        assert _run(src) == 1


class TestStringRepeat:
    """string_repeat repeats a string N times."""

    def test_basic(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_repeat("ab", 3));
  @Nat.0
}
"""
        assert _run(src) == 6

    def test_single_char(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  string_starts_with(string_repeat("x", 5), "xxxxx")
}
"""
        assert _run(src) == 1

    def test_zero_count(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_repeat("hello", 0));
  @Nat.0
}
"""
        assert _run(src) == 0

    def test_one_count(self) -> None:
        src = """
public fn f(-> @Bool) requires(true) ensures(true) effects(pure) {
  string_starts_with(string_repeat("hello", 1), "hello")
}
"""
        assert _run(src) == 1

    def test_empty_string(self) -> None:
        src = """
public fn f(-> @Int) requires(true) ensures(true) effects(pure) {
  let @Nat = string_length(string_repeat("", 100));
  @Nat.0
}
"""
        assert _run(src) == 0


class TestCharClassification:
    """#471 — the six ASCII classifiers + two case converters.

    Each classifier loads the first byte and tests against one or
    more ASCII ranges (subtract + unsigned-less-than trick for
    ``is_digit``/`is_alpha`/`is_upper`/`is_lower`; direct equality
    OR for ``is_whitespace``; OR'd pair for ``is_alphanumeric``).
    Empty-string convention: always false.
    """

    def _run_bool(self, src: str) -> int:
        """Compile a classifier call and return the i32 result."""
        return _run(src)

    def test_no_host_imports_for_inline_builtins(self) -> None:
        """Compile a program that uses all 16 #470/#471 built-ins and
        assert none of them is routed through a host import.

        Catches regressions in either direction: a refactor that
        adds a host import for one of these (the documented
        contract is "inline WAT, no host calls"), or a sibling
        builtin renamed to collide with one of our 16 names.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Bool = is_digit("5");
  let @Bool = is_alpha("A");
  let @Bool = is_alphanumeric("0");
  let @Bool = is_whitespace(" ");
  let @Bool = is_upper("A");
  let @Bool = is_lower("a");
  let @String = char_to_upper("a");
  let @String = char_to_lower("A");
  let @String = string_reverse("ab");
  let @String = string_trim_start("  x");
  let @String = string_trim_end("x  ");
  let @String = string_pad_start("x", 3, "0");
  let @String = string_pad_end("x", 3, "0");
  let @Array<String> = string_chars("ab");
  let @Array<String> = string_lines("a\\nb");
  let @Array<String> = string_words("a b");
  0
}
"""
        result = _compile_ok(src)
        _assert_no_host_imports_for_inline_builtins(result.wat)

    def test_is_digit(self) -> None:
        """is_digit: '5' true, 'x' false, '' false, '9' true, '0' true."""
        for s, expected in [("5", 1), ("x", 0), ("", 0), ("9", 1), ("0", 1)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_digit({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_digit({json.dumps(s)}) != {expected}"

    def test_is_alpha(self) -> None:
        """is_alpha: ASCII A-Z and a-z only."""
        for s, expected in [("a", 1), ("Z", 1), ("0", 0), ("!", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_alpha({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_alpha({json.dumps(s)}) != {expected}"

    def test_is_alphanumeric(self) -> None:
        """is_alphanumeric: letter OR digit."""
        for s, expected in [("a", 1), ("5", 1), ("Z", 1), (" ", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_alphanumeric({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_alphanumeric({json.dumps(s)}) != {expected}"

    def test_is_whitespace(self) -> None:
        """is_whitespace: Python str.isspace() ASCII set — space(32),
        tab(9), LF(10), VT(11), FF(12), CR(13).  Non-whitespace and
        empty string return 0.

        Vera's lexer only recognizes \\n / \\t / \\r / \\0 as simple
        escapes (see `_SIMPLE_ESCAPES` in vera/transform.py); VT and
        FF are written as `\\u{0B}` / `\\u{0C}` unicode escapes.
        """
        cases = [
            (" ", 1),
            ("\t", 1),
            ("\n", 1),
            ("\u000b", 1),  # VT — spelled "\u{0B}" in Vera source
            ("\u000c", 1),  # FF — spelled "\u{0C}" in Vera source
            ("\r", 1),
            ("a", 0),
            ("0", 0),
            ("", 0),
        ]
        _VERA_ESCAPES = {"\u000b": '"\\u{0B}"', "\u000c": '"\\u{0C}"'}
        for s, expected in cases:
            literal = _VERA_ESCAPES.get(s, json.dumps(s))
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_whitespace({literal}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_whitespace({literal}) != {expected}"

    def test_is_upper(self) -> None:
        """is_upper: 'A'..'Z' only."""
        for s, expected in [("A", 1), ("Z", 1), ("a", 0), ("5", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_upper({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_upper({json.dumps(s)}) != {expected}"

    def test_is_lower(self) -> None:
        """is_lower: 'a'..'z' only."""
        for s, expected in [("a", 1), ("z", 1), ("A", 0), ("5", 0), ("", 0)]:
            src = f"""\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{{ if is_lower({json.dumps(s)}) then {{ 1 }} else {{ 0 }} }}
"""
            assert _run(src) == expected, f"is_lower({json.dumps(s)}) != {expected}"

    def test_char_to_upper_first_only(self) -> None:
        """char_to_upper converts first char only; others untouched."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_upper("abc")) }
"""
        assert _run_io(src) == "Abc"

    def test_char_to_upper_non_letter_pass_through(self) -> None:
        """char_to_upper on non-letter first char: pass through."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_upper("5xy")) }
"""
        assert _run_io(src) == "5xy"

    def test_char_to_lower_first_only(self) -> None:
        """char_to_lower converts first char only; others untouched."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_lower("ABC")) }
"""
        assert _run_io(src) == "aBC"

    def test_char_to_upper_empty(self) -> None:
        """Empty string passes through."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_upper("")) }
"""
        assert _run_io(src) == ""

    def test_char_to_lower_empty(self) -> None:
        """Empty string passes through (mirror of char_to_upper)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(char_to_lower("")) }
"""
        assert _run_io(src) == ""


class TestStringUtilities:
    """#470 — string_chars, lines, words, pad_start, pad_end, reverse,
    trim_start, trim_end.

    All inline WAT.  The Array<String>-returning ones (chars, lines,
    words) allocate each slice independently via ``$alloc`` rather
    than slicing into a shared backing buffer; the GC mark phase
    rejects interior pointers, so per-slice allocation is required
    for elements to stay reachable across collections triggered
    after the function returns.
    """

    def test_string_reverse(self) -> None:
        """Reverse bytes."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_reverse("hello")) }
"""
        assert _run_io(src) == "olleh"

    def test_string_reverse_empty(self) -> None:
        """Empty reverses to empty."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_reverse("")) }
"""
        assert _run_io(src) == ""

    def test_string_trim_start(self) -> None:
        """Strip leading whitespace only."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_start("  hi  ")) }
"""
        assert _run_io(src) == "hi  "

    def test_string_trim_end(self) -> None:
        """Strip trailing whitespace only."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_end("  hi  ")) }
"""
        assert _run_io(src) == "  hi"

    def test_string_trim_vt_ff_full_set(self) -> None:
        """Full Python isspace() ASCII set is recognised by both trim
        ends — exercises the same predicate _translate_trim shares
        with is_whitespace and string_strip.  VT (0x0B) and FF (0x0C)
        are spelled with unicode escapes since Vera's lexer doesn't
        recognise \\v / \\f as simple escapes.
        """
        # trim_start drops " \t\n\v\f\r" prefix; trim_end keeps only
        # the leading whitespace.
        src_start = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_start(" \\t\\n\\u{0B}\\u{0C}\\rhi ")) }
"""
        assert _run_io(src_start) == "hi "
        src_end = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_trim_end(" hi \\t\\n\\u{0B}\\u{0C}\\r")) }
"""
        assert _run_io(src_end) == " hi"

    def test_string_trim_all_whitespace(self) -> None:
        """A string of only whitespace → empty (either variant).

        Check via length since an IO.print of an empty string leaves
        stdout empty too (indistinguishable from "print was never
        called" at the assertion layer).
        """
        src_start = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(string_length(string_trim_start("   "))) }
"""
        src_end = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(string_length(string_trim_end("   "))) }
"""
        assert _run(src_start) == 0
        assert _run(src_end) == 0

    def test_string_pad_start(self) -> None:
        """Left-pad with fill, cycling if needed."""
        # single-char fill
        src1 = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("x", 5, "0")) }
"""
        assert _run_io(src1) == "0000x"
        # multi-char fill cycles
        src2 = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("xx", 7, "ab")) }
"""
        # pad_len = 5, fill pattern a,b,a,b,a
        assert _run_io(src2) == "ababaxx"

    def test_string_pad_end(self) -> None:
        """Right-pad with fill, cycling."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_end("xx", 7, "ab")) }
"""
        assert _run_io(src) == "xxababa"

    def test_string_pad_no_change_when_longer(self) -> None:
        """If input is already >= target, no pad."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("hello", 3, "*")) }
"""
        assert _run_io(src) == "hello"

    def test_string_pad_end_no_change_when_longer(self) -> None:
        """Mirror: pad_end also returns input unchanged when too long."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_end("hello", 3, "*")) }
"""
        assert _run_io(src) == "hello"

    def test_string_pad_empty_fill(self) -> None:
        """Empty fill string: no pad, input returned."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_start("x", 5, "")) }
"""
        assert _run_io(src) == "x"

    def test_string_pad_end_empty_fill(self) -> None:
        """Mirror: pad_end with empty fill is a no-op too."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_pad_end("x", 5, "")) }
"""
        assert _run_io(src) == "x"

    def test_string_chars_length(self) -> None:
        """chars length == byte length."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_chars("abcde"))) }
"""
        assert _run(src) == 5

    def test_string_chars_empty(self) -> None:
        """chars of empty string is empty array."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_chars(""))) }
"""
        assert _run(src) == 0

    def test_string_chars_content(self) -> None:
        """Reassemble via join — chars + join should be identity."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_chars("abc"), "-")) }
"""
        assert _run_io(src) == "a-b-c"

    def test_string_lines_simple(self) -> None:
        """Basic \\n-separated lines."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\nb\\nc"))) }
"""
        assert _run(src) == 3

    def test_string_lines_crlf(self) -> None:
        """\\r\\n is one terminator (not two)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\r\\nb\\r\\nc"))) }
"""
        assert _run(src) == 3

    def test_string_lines_cr_only(self) -> None:
        """Bare \\r is a terminator."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\rb\\rc"))) }
"""
        assert _run(src) == 3

    def test_string_lines_trailing_newline(self) -> None:
        """Trailing \\n does not add an empty final segment (splitlines)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\nb\\n"))) }
"""
        assert _run(src) == 2

    def test_string_lines_empty(self) -> None:
        """Empty input → empty array (length 0)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines(""))) }
"""
        assert _run(src) == 0

    def test_string_lines_content_via_join(self) -> None:
        """Lines + join with \\n should give back the source (modulo trailing \\n)."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_lines("foo\\nbar\\nbaz"), ",")) }
"""
        assert _run_io(src) == "foo,bar,baz"

    def test_string_lines_trailing_cr(self) -> None:
        """Trailing \\r: splitlines semantics — no empty trailing segment."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\r"))) }
"""
        # Just "a\r" → ["a"], length 1.
        assert _run(src) == 1

    def test_string_lines_trailing_crlf(self) -> None:
        """Trailing \\r\\n: splitlines semantics — no empty trailing segment.

        Distinct from ``test_string_lines_trailing_newline`` because
        CRLF is a two-byte terminator and the scanner advances past
        both in a single step.  Ensures that optimisation doesn't
        accidentally yield an extra empty segment.
        """
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_lines("a\\r\\nb\\r\\n"))) }
"""
        # ["a", "b"] — length 2, no empty trailing.
        assert _run(src) == 2

    def test_string_lines_interior_blank_lf(self) -> None:
        """Consecutive \\n preserves the empty interior line."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_lines("a\\n\\nb"), "|")) }
"""
        # "a\n\nb" → ["a", "", "b"] — join with "|" → "a||b".
        assert _run_io(src) == "a||b"

    def test_string_lines_interior_blank_cr(self) -> None:
        """Consecutive \\r also preserves an empty interior line."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_lines("a\\r\\rb"), "|")) }
"""
        # "a\r\rb" → ["a", "", "b"] — join with "|" → "a||b".
        assert _run_io(src) == "a||b"

    def test_string_words_simple(self) -> None:
        """Basic split on whitespace runs."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words("foo bar baz"))) }
"""
        assert _run(src) == 3

    def test_string_words_runs(self) -> None:
        """Multiple whitespace chars count as one separator."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words("  foo    bar  baz  "))) }
"""
        assert _run(src) == 3

    def test_string_words_empty(self) -> None:
        """Empty input → empty array."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words(""))) }
"""
        assert _run(src) == 0

    def test_string_words_only_whitespace(self) -> None:
        """All-whitespace input → empty array (no words to emit)."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words("   \\t\\n  "))) }
"""
        assert _run(src) == 0

    def test_string_words_vt_ff_separators(self) -> None:
        """VT (0x0B) and FF (0x0C) act as word separators too."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_words(" \\u{0B}foo\\u{0C}bar "), "|")) }
"""
        assert _run_io(src) == "foo|bar"

    def test_string_words_only_vt_ff(self) -> None:
        """All VT/FF input → empty array (matches Python str.split())."""
        src = """\
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ nat_to_int(array_length(string_words(" \\u{0B}\\u{0C} "))) }
"""
        assert _run(src) == 0

    def test_string_words_content_via_join(self) -> None:
        """Words + join should give a canonicalised single-space-separated version."""
        src = """\
public fn main(-> @Unit)
  requires(true) ensures(true) effects(<IO>)
{ IO.print(string_join(string_words("  foo\\tbar\\n\\nbaz  "), "|")) }
"""
        assert _run_io(src) == "foo|bar|baz"
