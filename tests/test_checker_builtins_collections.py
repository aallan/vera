"""Tests for the Vera type checker — builtins_collections (Map/Set/Decimal/Json/Html/Http/Inference builtin type-checking).

Split from tests/test_checker.py (#420). Shared helpers live in tests/checker_helpers.py.
"""
from __future__ import annotations

from tests.checker_helpers import (
    _check_err,
    _check_ok,
)


# =====================================================================
# Map collection (#62)
# =====================================================================

class TestMapCollection:

    def test_map_insert_and_size(self) -> None:
        """map_insert + map_size type-check cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), "hello", 42)) }
""")

    def test_map_get_returns_option(self) -> None:
        """map_get returns Option<V>."""
        _check_ok("""
private fn foo(@Unit -> @Nat)
  requires(true) ensures(true) effects(pure)
{ option_unwrap_or(map_get(map_insert(map_new(), "k", 7), "k"), 0) }
""")

    def test_map_contains_returns_bool(self) -> None:
        """map_contains returns Bool."""
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ map_contains(map_insert(map_new(), "k", 1), "k") }
""")

    def test_map_remove_returns_map(self) -> None:
        """map_remove returns Map<K, V>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_remove(map_insert(map_new(), "k", 1), "k")) }
""")

    def test_map_keys_returns_array(self) -> None:
        """map_keys returns Array<K>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_keys(map_insert(map_new(), "k", 1))) }
""")

    def test_map_values_returns_array(self) -> None:
        """map_values returns Array<V>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(map_values(map_insert(map_new(), "k", 1))) }
""")

    def test_map_int_keys(self) -> None:
        """Map with Int keys type-checks cleanly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), 1, "hello")) }
""")

    def test_map_let_binding(self) -> None:
        """Map can be bound with let @Map<K, V>."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_insert(map_new(), "k", 42);
  map_size(@Map<String, Nat>.0)
}
""")

    def test_map_wrong_arity(self) -> None:
        """map_insert with wrong number of args produces error."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ map_size(map_insert(map_new(), "k")) }
""", "expects")

    def test_map_new_infers_from_let(self) -> None:
        """Bare map_new() resolves type vars from let binding context."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_new();
  map_size(@Map<String, Nat>.0)
}
""")

    def test_map_insert_wrong_value_type(self) -> None:
        """map_insert rejects a value whose type does not match V."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, Nat> = map_new();
  map_size(map_insert(@Map<String, Nat>.0, "k", "oops"))
}
""", "type")


class TestSetChecker:

    def test_set_new_type_checks(self) -> None:
        """set_new() in a let binding with Set<Int> type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Int> = set_new();
  set_size(@Set<Int>.0)
}
""")

    def test_set_add_type_checks(self) -> None:
        """set_add(set_new(), 1) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new(), 1)) }
""")

    def test_set_contains_type_checks(self) -> None:
        """set_contains returns Bool."""
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ set_contains(set_add(set_new(), 1), 1) }
""")

    def test_set_remove_type_checks(self) -> None:
        """set_remove type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_remove(set_add(set_new(), 1), 1)) }
""")

    def test_set_size_type_checks(self) -> None:
        """set_size returns Int."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new(), 42)) }
""")

    def test_set_to_array_type_checks(self) -> None:
        """set_to_array type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(set_to_array(set_add(set_new(), 1))) }
""")

    def test_set_wrong_arity(self) -> None:
        """set_add with wrong number of args produces error."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ set_size(set_add(set_new())) }
""", "expects")

    def test_set_new_infers_from_let(self) -> None:
        """let @Set<String> = set_new() infers correctly."""
        _check_ok("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<String> = set_new();
  set_size(@Set<String>.0)
}
""")

    def test_set_add_wrong_element_type(self) -> None:
        """set_add rejects an element whose type does not match T."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Set<Nat> = set_new();
  set_size(set_add(@Set<Nat>.0, "oops"))
}
""", "expected Nat")


class TestDecimalChecker:

    def test_decimal_from_int(self) -> None:
        """decimal_from_int(@Int -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_int(42) }
""")

    def test_decimal_add(self) -> None:
        """decimal_add(@Decimal, @Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_add(decimal_from_int(1), decimal_from_int(2)) }
""")

    def test_decimal_eq(self) -> None:
        """decimal_eq(@Decimal, @Decimal -> @Bool) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ decimal_eq(decimal_from_int(1), decimal_from_int(1)) }
""")

    def test_decimal_to_string(self) -> None:
        """decimal_to_string(@Decimal -> @String) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ decimal_to_string(decimal_from_int(42)) }
""")

    def test_decimal_to_float(self) -> None:
        """decimal_to_float(@Decimal -> @Float64) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Float64)
  requires(true) ensures(true) effects(pure)
{ decimal_to_float(decimal_from_int(42)) }
""")

    def test_decimal_wrong_arity(self) -> None:
        """decimal_add with 1 arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_add(decimal_from_int(1)) }
""", "expects")

    def test_decimal_wrong_type(self) -> None:
        """decimal_add with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_add(1, 2) }
""", "type")

    def test_decimal_from_string(self) -> None:
        """decimal_from_string(@String -> @Option<Decimal>) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_from_string("3.14") }
""")

    def test_decimal_div(self) -> None:
        """decimal_div(@Decimal, @Decimal -> @Option<Decimal>) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_div(decimal_from_int(10), decimal_from_int(3)) }
""")

    def test_decimal_compare(self) -> None:
        """decimal_compare(@Decimal, @Decimal -> @Ordering) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Ordering)
  requires(true) ensures(true) effects(pure)
{ decimal_compare(decimal_from_int(1), decimal_from_int(2)) }
""")

    def test_decimal_round(self) -> None:
        """decimal_round(@Decimal, @Int -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_round(decimal_from_int(3), 2) }
""")

    def test_decimal_neg(self) -> None:
        """decimal_neg(@Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_neg(decimal_from_int(42)) }
""")

    def test_decimal_abs(self) -> None:
        """decimal_abs(@Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_abs(decimal_from_int(42)) }
""")

    # Happy-path tests for remaining operations
    def test_decimal_from_float(self) -> None:
        """decimal_from_float(@Float64 -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_float(3.14) }
""")

    def test_decimal_sub(self) -> None:
        """decimal_sub(@Decimal, @Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_sub(decimal_from_int(5), decimal_from_int(3)) }
""")

    def test_decimal_mul(self) -> None:
        """decimal_mul(@Decimal, @Decimal -> @Decimal) type checks OK."""
        _check_ok("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_mul(decimal_from_int(2), decimal_from_int(3)) }
""")

    # Wrong-type tests
    def test_decimal_from_float_wrong_type(self) -> None:
        """decimal_from_float with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_from_float(42) }
""", "type")

    def test_decimal_sub_wrong_type(self) -> None:
        """decimal_sub with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_sub(1, 2) }
""", "type")

    def test_decimal_mul_wrong_type(self) -> None:
        """decimal_mul with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_mul(1, 2) }
""", "type")

    def test_decimal_neg_wrong_type(self) -> None:
        """decimal_neg with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_neg(42) }
""", "type")

    def test_decimal_abs_wrong_type(self) -> None:
        """decimal_abs with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_abs(42) }
""", "type")

    def test_decimal_round_wrong_type(self) -> None:
        """decimal_round with wrong arg types produces error."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ decimal_round("2", 2) }
""", "type")

    def test_decimal_compare_wrong_type(self) -> None:
        """decimal_compare with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Ordering)
  requires(true) ensures(true) effects(pure)
{ decimal_compare(1, 2) }
""", "type")

    def test_decimal_div_wrong_type(self) -> None:
        """decimal_div with Int args produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_div(1, 2) }
""", "type")

    def test_decimal_from_string_wrong_type(self) -> None:
        """decimal_from_string with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<Decimal>)
  requires(true) ensures(true) effects(pure)
{ decimal_from_string(42) }
""", "type")

    def test_decimal_rejects_type_args(self) -> None:
        """Decimal<Int> is rejected — Decimal is not parameterised."""
        _check_err("""
private fn foo(@Unit -> @Decimal)
  requires(true) ensures(true) effects(pure)
{ let @Decimal<Int> = decimal_from_int(1); @Decimal.0 }
""", "type arg")


class TestJsonChecker:
    """Json ADT and built-in function type checking."""

    def test_json_null(self) -> None:
        """JNull constructor type-checks as Json."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JNull }
""")

    def test_json_bool(self) -> None:
        """JBool(Bool) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JBool(true) }
""")

    def test_json_number(self) -> None:
        """JNumber(Float64) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JNumber(3.14) }
""")

    def test_json_string(self) -> None:
        """JString(String) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JString("hello") }
""")

    def test_json_array(self) -> None:
        """JArray(Array<Json>) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JArray([JNull, JBool(false)]) }
""")

    def test_json_object(self) -> None:
        """JObject(Map<String, Json>) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ JObject(map_insert(map_new(), "key", JNull)) }
""")

    def test_json_parse(self) -> None:
        """json_parse returns Result<Json, String>."""
        _check_ok("""
private fn foo(@Unit -> @Result<Json, String>)
  requires(true) ensures(true) effects(pure)
{ json_parse("{}") }
""")

    def test_json_stringify(self) -> None:
        """json_stringify returns String."""
        _check_ok("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ json_stringify(JNull) }
""")

    def test_json_get(self) -> None:
        """json_get returns Option<Json>."""
        _check_ok("""
private fn foo(@Json -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_get(@Json.0, "key") }
""")

    def test_json_has_field(self) -> None:
        """json_has_field returns Bool."""
        _check_ok("""
private fn foo(@Json -> @Bool)
  requires(true) ensures(true) effects(pure)
{ json_has_field(@Json.0, "key") }
""")

    def test_json_type_fn(self) -> None:
        """json_type returns String."""
        _check_ok("""
private fn foo(@Json -> @String)
  requires(true) ensures(true) effects(pure)
{ json_type(@Json.0) }
""")

    def test_json_array_get(self) -> None:
        """json_array_get returns Option<Json>."""
        _check_ok("""
private fn foo(@Json -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_array_get(@Json.0, 0) }
""")

    def test_json_array_length(self) -> None:
        """json_array_length returns Int."""
        _check_ok("""
private fn foo(@Json -> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(@Json.0) }
""")

    def test_json_keys(self) -> None:
        """json_keys returns Array<String>."""
        _check_ok("""
private fn foo(@Json -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ json_keys(@Json.0) }
""")

    def test_json_parse_wrong_type(self) -> None:
        """json_parse with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Result<Json, String>)
  requires(true) ensures(true) effects(pure)
{ json_parse(42) }
""", "type")

    def test_json_stringify_wrong_type(self) -> None:
        """json_stringify with String arg produces error."""
        _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ json_stringify("not json") }
""", "type")

    def test_json_array_length_wrong_type(self) -> None:
        """json_array_length with non-Json arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Int)
  requires(true) ensures(true) effects(pure)
{ json_array_length(42) }
""", "type")

    def test_json_keys_wrong_type(self) -> None:
        """json_keys with non-Json arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Array<String>)
  requires(true) ensures(true) effects(pure)
{ json_keys(42) }
""", "type")

    def test_json_array_get_wrong_index_type(self) -> None:
        """json_array_get with String index produces error."""
        _check_err("""
private fn foo(@Json -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_array_get(@Json.0, "0") }
""", "type")

    def test_json_get_wrong_type(self) -> None:
        """json_get with non-Json first arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<Json>)
  requires(true) ensures(true) effects(pure)
{ json_get(42, "key") }
""", "type")

    def test_json_has_field_wrong_type(self) -> None:
        """json_has_field with non-Json first arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Bool)
  requires(true) ensures(true) effects(pure)
{ json_has_field(42, "key") }
""", "type")

    def test_json_type_wrong_type(self) -> None:
        """json_type with non-Json arg produces error."""
        _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ json_type(42) }
""", "type")

    def test_json_custom_data_shadows_prelude(self) -> None:
        """User-defined data Json with non-standard constructors shadows prelude."""
        _check_ok("""
private data Json { MyNode(Int) }
private fn foo(@Unit -> @Json)
  requires(true) ensures(true) effects(pure)
{ MyNode(42) }
""")


class TestHtmlChecker:
    """HtmlNode ADT and built-in function type checking."""

    def test_html_element(self) -> None:
        """HtmlElement constructor type-checks as HtmlNode."""
        _check_ok("""
private fn foo(@Unit -> @HtmlNode)
  requires(true) ensures(true) effects(pure)
{ HtmlElement("div", map_new(), []) }
""")

    def test_html_text(self) -> None:
        """HtmlText(String) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @HtmlNode)
  requires(true) ensures(true) effects(pure)
{ HtmlText("hello") }
""")

    def test_html_comment(self) -> None:
        """HtmlComment(String) type-checks."""
        _check_ok("""
private fn foo(@Unit -> @HtmlNode)
  requires(true) ensures(true) effects(pure)
{ HtmlComment("a comment") }
""")

    def test_html_parse(self) -> None:
        """html_parse returns Result<HtmlNode, String>."""
        _check_ok("""
private fn foo(@Unit -> @Result<HtmlNode, String>)
  requires(true) ensures(true) effects(pure)
{ html_parse("<p>hello</p>") }
""")

    def test_html_to_string(self) -> None:
        """html_to_string returns String."""
        _check_ok("""
private fn foo(@HtmlNode -> @String)
  requires(true) ensures(true) effects(pure)
{ html_to_string(@HtmlNode.0) }
""")

    def test_html_query(self) -> None:
        """html_query returns Array<HtmlNode>."""
        _check_ok("""
private fn foo(@HtmlNode -> @Array<HtmlNode>)
  requires(true) ensures(true) effects(pure)
{ html_query(@HtmlNode.0, "p") }
""")

    def test_html_text_fn(self) -> None:
        """html_text returns String."""
        _check_ok("""
private fn foo(@HtmlNode -> @String)
  requires(true) ensures(true) effects(pure)
{ html_text(@HtmlNode.0) }
""")

    def test_html_attr(self) -> None:
        """html_attr returns Option<String>."""
        _check_ok("""
private fn foo(@HtmlNode -> @Option<String>)
  requires(true) ensures(true) effects(pure)
{ html_attr(@HtmlNode.0, "href") }
""")

    def test_html_parse_wrong_type(self) -> None:
        """html_parse with Int arg produces error."""
        _check_err("""
private fn foo(@Unit -> @Result<HtmlNode, String>)
  requires(true) ensures(true) effects(pure)
{ html_parse(42) }
""", "type")

    def test_html_to_string_wrong_type(self) -> None:
        """html_to_string with String arg produces error."""
        _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ html_to_string("not a node") }
""", "type")

    def test_html_query_wrong_node_type(self) -> None:
        """html_query with Int as node produces error."""
        _check_err("""
private fn foo(@Unit -> @Array<HtmlNode>)
  requires(true) ensures(true) effects(pure)
{ html_query(42, "div") }
""", "type")

    def test_html_query_wrong_selector_type(self) -> None:
        """html_query with Int as selector produces error."""
        _check_err("""
private fn foo(@HtmlNode -> @Array<HtmlNode>)
  requires(true) ensures(true) effects(pure)
{ html_query(@HtmlNode.0, 42) }
""", "type")

    def test_html_text_wrong_type(self) -> None:
        """html_text with String arg produces error."""
        _check_err("""
private fn foo(@Unit -> @String)
  requires(true) ensures(true) effects(pure)
{ html_text("not a node") }
""", "type")

    def test_html_attr_wrong_node_type(self) -> None:
        """html_attr with Int as node produces error."""
        _check_err("""
private fn foo(@Unit -> @Option<String>)
  requires(true) ensures(true) effects(pure)
{ html_attr(42, "href") }
""", "type")

    def test_html_attr_wrong_name_type(self) -> None:
        """html_attr with Int as attribute name produces error."""
        _check_err("""
private fn foo(@HtmlNode -> @Option<String>)
  requires(true) ensures(true) effects(pure)
{ html_attr(@HtmlNode.0, 42) }
""", "type")


class TestHttpChecker:
    """Http effect type checking."""

    def test_http_get_type_checks(self) -> None:
        """Http.get with String arg, effects(<Http>), returns Result<String, String>."""
        _check_ok("""
public fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.get(@String.0) }
""")

    def test_http_post_type_checks(self) -> None:
        """Http.post with two String args type-checks."""
        _check_ok("""
public fn post(@String, @String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.post(@String.0, @String.1) }
""")

    def test_http_get_wrong_arity(self) -> None:
        """Http.get() with no args is an error."""
        _check_err("""
public fn fetch(@Unit -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.get() }
""", "argument")

    def test_http_get_wrong_type(self) -> None:
        """Http.get(42) with Int arg is a type error."""
        _check_err("""
public fn fetch(@Unit -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.get(42) }
""", "type")

    def test_http_missing_effect(self) -> None:
        """Http.get without effects(<Http>) is an error."""
        _check_err("""
public fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ Http.get(@String.0) }
""", "effect")

    def test_http_post_wrong_type(self) -> None:
        """Http.post(42, "body") with Int URL is a type error."""
        _check_err("""
public fn post(@Unit -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.post(42, "body") }
""", "type")

    def test_http_with_io(self) -> None:
        """effects(<Http, IO>) composes correctly."""
        _check_ok("""
public fn fetch_and_print(@String -> @Unit)
  requires(true) ensures(true) effects(<Http, IO>)
{
  let @Result<String, String> = Http.get(@String.0);
  IO.println("done")
}
""")


class TestInferenceChecker:
    """Inference effect type checking."""

    def test_inference_complete_type_checks(self) -> None:
        """Inference.complete with String arg, effects(<Inference>), returns Result<String, String>."""
        _check_ok("""
public fn classify(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Inference>)
{ Inference.complete(@String.0) }
""")

    def test_inference_complete_wrong_arity(self) -> None:
        """Inference.complete() with no args is an error."""
        _check_err("""
public fn classify(@Unit -> @Result<String, String>)
  requires(true) ensures(true) effects(<Inference>)
{ Inference.complete() }
""", "argument")

    def test_inference_complete_wrong_type(self) -> None:
        """Inference.complete(42) with Int arg is a type error."""
        _check_err("""
public fn classify(@Unit -> @Result<String, String>)
  requires(true) ensures(true) effects(<Inference>)
{ Inference.complete(42) }
""", "type")

    def test_inference_missing_effect(self) -> None:
        """Inference.complete without effects(<Inference>) is an error."""
        _check_err("""
public fn classify(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(pure)
{ Inference.complete(@String.0) }
""", "effect")

    def test_inference_with_io(self) -> None:
        """effects(<Inference, IO>) composes correctly."""
        _check_ok("""
public fn classify_and_print(@String -> @Unit)
  requires(true) ensures(true) effects(<Inference, IO>)
{
  let @Result<String, String> = Inference.complete(@String.0);
  IO.println("done")
}
""")

    def test_inference_with_http(self) -> None:
        """effects(<Http, Inference>) composes correctly."""
        _check_ok("""
public fn fetch_and_classify(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http, Inference>)
{
  let @Result<String, String> = Http.get(@String.0);
  match @Result<String, String>.0 {
    Ok(@String) -> Inference.complete(@String.0),
    Err(@String) -> Err(@String.0)
  }
}
""")
