"""Tests for vera.codegen — host_effects (Html/Http/Inference host effects, provider dispatch, postcondition host-import propagation).

Split from tests/test_codegen.py (#419). Shared helpers live in tests/codegen_helpers.py.
"""
from __future__ import annotations


from vera.codegen import (
    execute,
)

from tests.codegen_helpers import (
    _compile_ok,
    _run,
    _run_float,
)


class TestHtmlCollection:
    """HtmlNode ADT built-in operations: html_parse, html_to_string,
    html_query, html_text, html_attr."""

    def test_html_parse_valid(self) -> None:
        """html_parse of valid HTML returns Ok."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hello</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> 1,
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 1

    def test_html_text_extraction(self) -> None:
        """html_text extracts text content from parsed HTML."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hello</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_text(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 5

    def test_html_to_string_roundtrip(self) -> None:
        """html_to_string serializes back to HTML."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hi</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_to_string(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
"""
        assert _run(source) > 0

    def test_html_query_by_tag(self) -> None:
        """html_query finds elements by tag name."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div><p>a</p><p>b</p></div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "p")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 2

    def test_html_attr_present(self) -> None:
        """html_attr returns Some for present attributes."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<a href=\\"url\\">link</a>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> match html_attr(@HtmlNode.0, "href") {
      Some(@String) -> string_length(@String.0),
      None -> 0
    },
    Err(@String) -> 0 - 1
  }
}
'''
        assert _run(source) == 3

    def test_html_attr_absent(self) -> None:
        """html_attr returns None for missing attributes."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>text</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> match html_attr(@HtmlNode.0, "class") {
      Some(@String) -> 1,
      None -> 0
    },
    Err(@String) -> 0 - 1
  }
}
"""
        assert _run(source) == 0

    def test_html_parse_invalid(self) -> None:
        """Malformed HTML still parses leniently (best-effort)."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>unclosed");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> 1,
    Err(@String) -> 0
  }
}
"""
        assert _run(source) == 1

    def test_html_parse_wat_import(self) -> None:
        """html_parse generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>x</p>");
  1
}
"""
        result = _compile_ok(source)
        assert '"html_parse"' in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_query"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_to_string_wat_import(self) -> None:
        """html_to_string generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlText("x"))) }
"""
        result = _compile_ok(source)
        assert '"html_to_string"' in result.wat
        assert '"html_parse"' not in result.wat
        assert '"html_query"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_query_wat_import(self) -> None:
        """html_query generates a WASM host import without html_parse."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ array_length(html_query(HtmlElement("div", map_new(), [HtmlText("x")]), "div")) }
"""
        result = _compile_ok(source)
        assert '"html_query"' in result.wat
        assert '"html_parse"' not in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_text_wat_import(self) -> None:
        """html_text generates a WASM host import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_text(HtmlText("hello"))) }
"""
        result = _compile_ok(source)
        assert '"html_text"' in result.wat
        assert '"html_parse"' not in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_query"' not in result.wat

    def test_html_query_by_class(self) -> None:
        """html_query with class selector."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div class=\\"foo\\">a</div><div>b</div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, ".foo")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_html_query_by_id(self) -> None:
        """html_query with ID selector."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p id=\\"main\\">hi</p><p>bye</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "#main")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_html_query_descendant(self) -> None:
        """html_query with descendant selector."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div><p>a</p><p>b</p></div><p>c</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "div p")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 2

    def test_html_no_imports_when_unused(self) -> None:
        """Programs not using html builtins have no Html imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"html_parse"' not in result.wat
        assert '"html_to_string"' not in result.wat
        assert '"html_query"' not in result.wat
        assert '"html_text"' not in result.wat

    def test_html_comment_roundtrip(self) -> None:
        """HtmlComment serializes to <!-- ... --> via html_to_string."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlComment("a comment"))) }
"""
        # "<!--a comment-->" = 16 chars
        assert _run(source) == 16

    def test_html_text_escaping(self) -> None:
        """html_to_string escapes & < > in text content."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlText("a&b"))) }
'''
        # "a&amp;b" = 7 chars
        assert _run(source) == 7

    def test_html_attr_value_escaping(self) -> None:
        """html_to_string escapes quotes in attribute values."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Map<String, String> = map_insert(map_new(), "title", "a\\"b");
  string_length(html_to_string(HtmlElement("p", @Map<String, String>.0, [])))
}
'''
        # <p title="a&quot;b"></p> = 24 chars (quote escaped as &quot;)
        assert _run(source) == 24

    def test_html_query_attr_selector(self) -> None:
        """html_query with attribute presence selector [href]."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<a href=\\"x\\">link</a><span>no</span>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "[href]")),
    Err(@String) -> 0
  }
}
'''
        assert _run(source) == 1

    def test_html_parse_with_attributes(self) -> None:
        """Parsed element attributes are accessible via html_query + html_attr."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div class=\\"main\\">content</div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> {
      let @Array<HtmlNode> = html_query(@HtmlNode.0, ".main");
      if array_length(@Array<HtmlNode>.0) > 0 then {
        match @Array<HtmlNode>.0[0] {
          HtmlElement(@String, @Map<String, String>, @Array<HtmlNode>) ->
            match map_get(@Map<String, String>.0, "class") {
              Some(@String) -> string_length(@String.0),
              None -> 0
            },
          HtmlText(@String) -> 0,
          HtmlComment(@String) -> 0
        }
      } else { 0 }
    },
    Err(@String) -> 0
  }
}
'''
        # "main" = 4 chars
        assert _run(source) == 4

    def test_html_void_element(self) -> None:
        """Void elements (br, img) serialize without closing tag."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ string_length(html_to_string(HtmlElement("br", map_new(), []))) }
"""
        # "<br>" = 4 chars
        assert _run(source) == 4

    def test_html_parse_comment_roundtrip(self) -> None:
        """Parsed HTML comments survive roundtrip through html_to_string."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<!-- hello --><p>text</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_to_string(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
'''
        result = _run(source)
        assert result > 0  # roundtrip produces non-empty HTML

    def test_html_query_empty_result(self) -> None:
        """html_query with no matches returns empty array."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<p>hello</p>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> array_length(html_query(@HtmlNode.0, "div")),
    Err(@String) -> 0 - 1
  }
}
'''
        assert _run(source) == 0

    def test_html_nested_elements(self) -> None:
        """html_text extracts text from nested elements."""
        source = '''
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{
  let @Result<HtmlNode, String> = html_parse("<div><span>hello</span> <em>world</em></div>");
  match @Result<HtmlNode, String>.0 {
    Ok(@HtmlNode) -> string_length(html_text(@HtmlNode.0)),
    Err(@String) -> 0
  }
}
'''
        result = _run(source)
        assert result > 0  # extracts "hello world" text


class TestHttpCollection:
    """Http effect: host-import compilation and mocked execution."""

    def test_http_get_compiles(self) -> None:
        """Http.get generates a WASM host import."""
        source = """
public fn fetch(@String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.get(@String.0) }
"""
        result = _compile_ok(source)
        assert '"http_get"' in result.wat

    def test_http_post_compiles(self) -> None:
        """Http.post generates a WASM host import."""
        source = """
public fn post(@String, @String -> @Result<String, String>)
  requires(true) ensures(true) effects(<Http>)
{ Http.post(@String.0, @String.1) }
"""
        result = _compile_ok(source)
        assert '"http_post"' in result.wat

    def test_http_get_only_imports_get(self) -> None:
        """Program using only Http.get does not import http_post."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("http://example.com");
  42
}
"""
        result = _compile_ok(source)
        assert '"http_get"' in result.wat
        assert '"http_post"' not in result.wat

    def test_http_post_only_imports_post(self) -> None:
        """Program using only Http.post does not import http_get."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.post("http://example.com", "body");
  42
}
"""
        result = _compile_ok(source)
        assert '"http_post"' in result.wat
        assert '"http_get"' not in result.wat

    def test_http_no_imports_when_unused(self) -> None:
        """Program without Http has no http imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"http_get"' not in result.wat
        assert '"http_post"' not in result.wat

    def test_http_declared_but_unused(self) -> None:
        """effects(<Http>) declared but no Http ops used — no imports."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"http_get"' not in result.wat
        assert '"http_post"' not in result.wat

    def test_http_get_mocked_success(self) -> None:
        """Mocked Http.get returns Ok with response body."""
        from unittest.mock import MagicMock, patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("http://example.com");
  match @Result<String, String>.0 {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""
        result = _compile_ok(source)
        mock_resp = MagicMock()
        mock_resp.read.return_value = b"hello"
        mock_resp.__enter__ = lambda s: s
        mock_resp.__exit__ = MagicMock(return_value=False)
        with patch("urllib.request.urlopen", return_value=mock_resp):
            exec_result = execute(result)
            assert exec_result.value == 5

    def test_http_get_mocked_failure(self) -> None:
        """Mocked Http.get failure returns Err."""
        from unittest.mock import patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("http://example.com");
  match @Result<String, String>.0 {
    Ok(@String) -> 0,
    Err(@String) -> string_length(@String.0)
  }
}
"""
        result = _compile_ok(source)
        with patch(
            "urllib.request.urlopen",
            side_effect=Exception("connection refused"),
        ):
            exec_result = execute(result)
            assert exec_result.value is not None
            assert exec_result.value > 0

    def test_http_post_mocked(self) -> None:
        """Mocked Http.post returns Ok with response body."""
        from unittest.mock import MagicMock, patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.post("http://example.com", "data");
  match @Result<String, String>.0 {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""
        result = _compile_ok(source)
        mock_resp = MagicMock()
        mock_resp.read.return_value = b"created"
        mock_resp.__enter__ = lambda s: s
        mock_resp.__exit__ = MagicMock(return_value=False)
        with patch("urllib.request.urlopen", return_value=mock_resp):
            exec_result = execute(result)
            assert exec_result.value == 7

    def test_http_url_scheme_predicate(self) -> None:
        """#789: `_is_allowed_http_url` admits only http/https (case-
        insensitive) and rejects file://, ftp://, data:, schemeless, etc.,
        so the host callbacks never hand a non-HTTP(S) URL to urlopen."""
        from vera.runtime.http import _is_allowed_http_url

        assert _is_allowed_http_url("http://example.com/x")
        assert _is_allowed_http_url("https://example.com/x")
        assert _is_allowed_http_url("HTTPS://EXAMPLE.com")
        assert not _is_allowed_http_url("file:///etc/passwd")
        assert not _is_allowed_http_url("ftp://example.com/x")
        assert not _is_allowed_http_url("data:text/plain,hi")
        assert not _is_allowed_http_url("javascript:alert(1)")
        assert not _is_allowed_http_url("/relative/path")
        assert not _is_allowed_http_url("")

    def test_http_get_rejects_file_scheme_end_to_end(self) -> None:
        """A compiled `Http.get` on a file:// URL returns Err AND never reaches
        urlopen — the scheme guard short-circuits before any I/O (#789).

        Mocking urlopen and asserting it is never called proves the guard runs
        first, independent of whether `file:///etc/passwd` exists on the host
        (it doesn't on Windows, where a failing urlopen would mask a removed
        guard by also producing an Err)."""
        from unittest.mock import patch

        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Http>)
{
  let @Result<String, String> = Http.get("file:///etc/passwd");
  match @Result<String, String>.0 {
    Ok(@String) -> 1,
    Err(@String) -> 0
  }
}
"""
        result = _compile_ok(source)
        with patch("urllib.request.urlopen") as mock_urlopen:
            exec_result = execute(result)
        assert exec_result.value == 0  # Err branch — scheme rejected
        mock_urlopen.assert_not_called()  # guard short-circuited before urlopen


class TestInferenceCollection:
    """Inference effect: host-import compilation and mocked execution."""

    _CLASSIFY_SOURCE = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference>)
{
  let @Result<String, String> = Inference.complete("Is this positive?");
  match @Result<String, String>.0 {
    Ok(@String) -> string_length(@String.0),
    Err(@String) -> 0
  }
}
"""

    def test_inference_complete_compiles(self) -> None:
        """Inference.complete generates a WASM host import."""
        result = _compile_ok(self._CLASSIFY_SOURCE)
        assert '"inference_complete"' in result.wat

    def test_inference_no_import_when_unused(self) -> None:
        """Program without Inference has no inference_complete import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(pure)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"inference_complete"' not in result.wat

    def test_inference_declared_but_unused(self) -> None:
        """effects(<Inference>) declared but no Inference ops used — no import."""
        source = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference>)
{ 42 }
"""
        result = _compile_ok(source)
        assert '"inference_complete"' not in result.wat

    def test_inference_complete_mocked_success(self) -> None:
        """Mocked Inference.complete returns Ok with completion."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            return_value="Positive",
        ):
            exec_result = execute(result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-test"})
            assert exec_result.value == 8  # len("Positive")

    def test_inference_complete_mocked_failure(self) -> None:
        """Mocked Inference.complete raises exception — returns Err."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=Exception("timeout"),
        ):
            exec_result = execute(result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-test"})
            assert exec_result.value == 0  # Err branch returns 0

    def test_inference_no_api_key_returns_err(self) -> None:
        """Inference.complete with no API key configured returns Err."""
        result = _compile_ok(self._CLASSIFY_SOURCE)
        exec_result = execute(result, env_vars={})
        assert exec_result.value == 0  # Err branch returns 0

    def test_inference_openai_auto_detect(self) -> None:
        """OpenAI key auto-detected when no VERA_INFERENCE_PROVIDER set."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            return_value="Positive",
        ) as mock_provider:
            exec_result = execute(result, env_vars={"VERA_OPENAI_API_KEY": "sk-openai-test"})
            assert exec_result.value == 8  # len("Positive")
            assert mock_provider.call_args[0][0] == "openai"

    def test_inference_moonshot_auto_detect(self) -> None:
        """Moonshot key auto-detected when no other keys are set."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            return_value="Neutral",
        ) as mock_provider:
            exec_result = execute(result, env_vars={"VERA_MOONSHOT_API_KEY": "sk-moonshot-test"})
            assert exec_result.value == 7  # len("Neutral")
            assert mock_provider.call_args[0][0] == "moonshot"

    def test_inference_explicit_provider_override(self) -> None:
        """VERA_INFERENCE_PROVIDER overrides auto-detection."""
        from unittest.mock import patch

        result = _compile_ok(self._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            return_value="ok",
        ) as mock_provider:
            execute(result, env_vars={
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
                "VERA_OPENAI_API_KEY": "sk-openai-test",
                "VERA_INFERENCE_PROVIDER": "openai",
            })
            assert mock_provider.call_args[0][0] == "openai"


class TestInferenceProviderDispatch:
    """Unit tests for _call_inference_provider — covers all provider branches."""

    def _make_response(self, body: str) -> object:
        """Build a minimal mock urllib response."""
        from unittest.mock import MagicMock
        resp = MagicMock()
        resp.read.return_value = body.encode("utf-8")
        resp.__enter__ = lambda s: s
        resp.__exit__ = MagicMock(return_value=False)
        return resp

    def test_anthropic_provider(self) -> None:
        """Anthropic branch uses correct endpoint, headers, and request body shape."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.runtime.inference import _call_inference_provider

        body = json.dumps({"content": [{"text": "hello"}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("anthropic", "prompt", "", "sk-ant")
        assert result == "hello"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == "https://api.anthropic.com/v1/messages"
        # Anthropic-style auth: x-api-key header, not Bearer
        assert req.get_header("X-api-key") == "sk-ant"
        assert req.get_header("Anthropic-version") == "2023-06-01"
        assert req.get_header("Authorization") is None
        sent_body = json.loads(req.data.decode())
        # Anthropic body: includes max_tokens; no "choices" key
        assert "max_tokens" in sent_body
        assert "messages" in sent_body
        assert sent_body["max_tokens"] == 1024

    def test_openai_provider(self) -> None:
        """OpenAI branch uses correct endpoint, bearer auth, and OpenAI-compatible body."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.runtime.inference import _call_inference_provider, _PROVIDERS

        body = json.dumps({"choices": [{"message": {"content": "world"}}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("openai", "prompt", "", "sk-openai")
        assert result == "world"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == _PROVIDERS["openai"].url
        # Bearer auth, not Anthropic-style key header
        assert req.get_header("Authorization") == "Bearer sk-openai"
        assert req.get_header("X-api-key") is None
        assert req.get_header("Content-type") == "application/json"
        sent_body = json.loads(req.data.decode())
        assert sent_body["model"] == _PROVIDERS["openai"].default_model
        assert "messages" in sent_body
        assert "max_tokens" not in sent_body

    def test_moonshot_provider(self) -> None:
        """Moonshot branch uses correct endpoint, default model, OpenAI-compatible format."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.runtime.inference import _call_inference_provider

        body = json.dumps({"choices": [{"message": {"content": "moonshot"}}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("moonshot", "prompt", "", "sk-moon")
        assert result == "moonshot"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == "https://api.moonshot.ai/v1/chat/completions"
        sent_body = json.loads(req.data.decode())
        assert sent_body["model"] == "kimi-k2-0905-preview"

    def test_mistral_provider(self) -> None:
        """Mistral branch uses correct endpoint, default model, OpenAI-compatible format."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.runtime.inference import _call_inference_provider

        body = json.dumps({"choices": [{"message": {"content": "mistral"}}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            result = _call_inference_provider("mistral", "prompt", "", "sk-mistral")
        assert result == "mistral"
        req = mock_urlopen.call_args[0][0]
        assert req.full_url == "https://api.mistral.ai/v1/chat/completions"
        # Bearer auth (OpenAI-compatible), not Anthropic-style key header
        assert req.get_header("Authorization") == "Bearer sk-mistral"
        assert req.get_header("X-api-key") is None
        sent_body = json.loads(req.data.decode())
        assert sent_body["model"] == "mistral-small-latest"
        # OpenAI-compatible body: has "messages", no Anthropic "max_tokens"
        assert "messages" in sent_body
        assert "max_tokens" not in sent_body

    def test_mistral_auto_detect(self) -> None:
        """Mistral key auto-detected when no other keys are set."""
        from unittest.mock import patch

        result_src = _compile_ok(TestInferenceCollection._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            return_value="ok",
        ) as mock_provider:
            execute(result_src, env_vars={"VERA_MISTRAL_API_KEY": "sk-mistral-test"})
            assert mock_provider.call_args[0][0] == "mistral"

    def test_multi_key_auto_detect_respects_provider_order(self) -> None:
        """When multiple keys are set, _PROVIDERS insertion order determines which wins.

        The auto-detection loop scans _PROVIDERS in order and picks the first
        provider whose key is present in the environment.  With anthropic first
        in the registry, setting both VERA_ANTHROPIC_API_KEY and
        VERA_MOONSHOT_API_KEY must resolve to 'anthropic'.
        """
        from unittest.mock import patch
        from vera.runtime.inference import _PROVIDERS

        first_provider = next(iter(_PROVIDERS))  # "anthropic" per current registry
        first_cfg = _PROVIDERS[first_provider]
        second_provider = list(_PROVIDERS)[1]    # "openai"
        second_cfg = _PROVIDERS[second_provider]

        result_src = _compile_ok(TestInferenceCollection._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            return_value="ok",
        ) as mock_provider:
            execute(result_src, env_vars={
                first_cfg.env_key: "sk-first",
                second_cfg.env_key: "sk-second",
            })
            assert mock_provider.call_args[0][0] == first_provider

    def test_explicit_provider_missing_key_returns_err(self) -> None:
        """Provider set via VERA_INFERENCE_PROVIDER but key env var absent → Err branch.

        Patches _call_inference_provider to confirm the early-fail guard fires
        *before* any provider invocation — exec_result.value == 0 alone is not
        sufficient because the Err branch is also reached on a network failure.
        """
        from unittest.mock import patch

        result_src = _compile_ok(TestInferenceCollection._CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=AssertionError("should not be called"),
        ) as mock_provider:
            exec_result = execute(
                result_src,
                env_vars={"VERA_INFERENCE_PROVIDER": "mistral"},
            )
        # Early-fail guard returned Err before reaching the provider
        assert exec_result.value == 0
        mock_provider.assert_not_called()

    def test_custom_model_passed_through(self) -> None:
        """VERA_INFERENCE_MODEL is forwarded to the provider."""
        import json
        from unittest.mock import patch, MagicMock
        from vera.runtime.inference import _call_inference_provider

        body = json.dumps({"content": [{"text": "ok"}]})
        mock_urlopen = MagicMock(return_value=self._make_response(body))
        with patch("urllib.request.urlopen", mock_urlopen):
            _call_inference_provider("anthropic", "hi", "claude-opus-4-6", "sk-ant")
        import json as _json
        sent = _json.loads(mock_urlopen.call_args[0][0].data.decode())
        assert sent["model"] == "claude-opus-4-6"

    def test_unknown_provider_raises(self) -> None:
        """Unknown provider string raises ValueError."""
        from vera.runtime.inference import _call_inference_provider
        import pytest
        with pytest.raises(ValueError, match="Unknown inference provider"):
            _call_inference_provider("unknown", "p", "", "")


class TestPostconditionHostImportPropagation823:
    """A host-import builtin or an allocation used *only* inside an
    ``ensures(...)`` postcondition must still get its import / memory / GC
    declaration.

    Codegen propagates a function's accumulated host-import and resource flags
    from the per-function ``ctx`` to the module *after* lowering postconditions
    (``functions.py``).  Propagating earlier — the historical position, before
    ``_compile_postconditions`` — dropped any flag a builtin or allocation set
    while lowering an ``ensures(...)`` predicate, so the import / memory / GC
    declaration was omitted and the orphaned ``call``/``global.get`` failed WAT
    compilation.  #808 surfaced this (its new ``vera.overflow_trap`` was the
    first import to expose it) and fixed the general ordering for every
    host-import family and ``$alloc`` (#823).

    Each fixture's BODY is a plain slot — no arithmetic, no allocation — so the
    flag is set ONLY while lowering the postcondition.  These would compile fine
    if the propagation ran before postconditions only because the body happened
    to need the same import; the scalar body rules that out.
    """

    def test_math_host_import_in_postcondition_compiles(self) -> None:
        # `sin` lowers to `call $vera.sin`; the body returns the slot unchanged,
        # so the import is needed only because of the ensures() predicate.
        src = (
            "public fn h(@Float64 -> @Float64) "
            "requires(true) ensures(sin(@Float64.result) <= 2.0) "
            "effects(pure) { @Float64.0 }"
        )
        assert _run_float(src, "h", [0.5]) == 0.5

    def test_alloc_in_postcondition_compiles(self) -> None:
        # `int_to_string` allocates → needs_alloc / needs_memory and the GC
        # shadow-stack globals ($gc_sp); the scalar body never allocates, so the
        # allocation is reachable only via the ensures() predicate.
        src = (
            "public fn f(@Int -> @Int) "
            "requires(true) "
            "ensures(string_length(int_to_string(@Int.result)) > 0) "
            "effects(pure) { @Int.0 }"
        )
        assert _run(src, "f", [5]) == 5

    def test_regex_host_import_in_postcondition_compiles(self) -> None:
        # `regex_*` (and `md_*`) host imports are registered ONLY by the body
        # pre-scan — they have no per-function `ctx` set-site — and that scan
        # was body-only, so a regex builtin reachable only via an `ensures(...)`
        # emitted an orphaned `call $vera.regex_match` with no import.  The
        # `match` scrutinee always evaluates the builtin; both arms are `true`
        # so the postcondition holds regardless of the regex result.
        src = (
            "public fn f(-> @Bool) requires(true) "
            'ensures(match regex_match("ab", "a") '
            "{ Ok(@Bool) -> true, Err(@String) -> true }) "
            "effects(pure) { true }"
        )
        assert _run(src, "f") == 1

    def test_md_host_import_in_postcondition_compiles(self) -> None:
        # Markdown sibling of the regex case — same body-only-pre-scan gap.
        src = (
            "public fn g(-> @Bool) requires(true) "
            'ensures(match md_parse("# H") '
            "{ Ok(@MdBlock) -> true, Err(@String) -> true }) "
            "effects(pure) { true }"
        )
        assert _run(src, "g") == 1
