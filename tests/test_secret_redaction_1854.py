"""No part of a secret the host holds reaches a message (#1854).

The host holds one kind of secret: each inference provider's configured API
key (`vera.runtime.inference._PROVIDERS`), beside which a provider or a
proxy may quote a credential-shaped token the host was never given.  Text
from outside reaches a message, the `Err` of `Inference.complete`, from a
provider's HTTP error body (read under a 64 KiB cap, then bounded to 200
characters), a response body that is not JSON, the fields a shape report
quotes, and an exception the transport raises.  Before #1854 the cap cut the
body and redaction ran after it, so a key the cap split left its first part
in the message, and an exception's text was quoted unredacted, so a key
holding a line end reached the `Err` whole (`Invalid header value
b'<key>\\r\\n'`).

The matrix: every provider, by each secret (the configured key, and a
credential-shaped token it did not configure), by each place, by the
secret's position against the cut (wholly before the cap, ending at it,
across it at every split, wholly after it).  The assertion is on the
message: no run of the secret longer than three characters appears in it.
"""
from __future__ import annotations

import dataclasses
import email.message
import html
import io
import json
import random
import urllib.error
from collections.abc import Iterator
from unittest.mock import MagicMock, patch

import pytest

from tests import pipeline
from tests.codegen_helpers import _compile_ok
from vera.runtime import inference
from vera.runtime.inference import _ERROR_BODY_CAP, InferenceError

pytestmark = pytest.mark.matrix(decides=["vera/runtime/inference.py"])

_RNG = random.Random(1854)
_ALNUM = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789"

#: The configured key: no recognisable prefix (Mistral's form), so only the
#: configured-key rule can redact it.
KEY = "".join(_RNG.choice(_ALNUM) for _ in range(40))
#: A credential-shaped token the host did not configure: only the pattern
#: rule can redact it.
TOKEN = "sk-" + "".join(_RNG.choice(_ALNUM) for _ in range(37))

SECRETS = {"configured": (KEY, KEY), "unconfigured": (TOKEN, "Cfg" + KEY[3:])}


def assert_no_part_of(secret: str, text: str) -> None:
    """No run of *secret* longer than three characters is in *text*."""
    runs = [secret[i:i + 4] for i in range(len(secret) - 3)]
    found = [r for r in runs if r in text]
    assert not found, (found, text)


def _http_error(body: bytes) -> urllib.error.HTTPError:
    return urllib.error.HTTPError(
        url="https://example.invalid", code=401, msg="Unauthorized",
        hdrs=email.message.Message(), fp=io.BytesIO(body))


def _message(provider: str, key: str, *, raises: BaseException | None = None,
             body: bytes | None = None) -> str:
    """The message `_call_inference_provider` gives for one exchange."""
    if raises is not None:
        transport = MagicMock(side_effect=raises)
    else:
        resp = MagicMock()
        resp.read.return_value = body
        resp.__enter__ = lambda s: s
        resp.__exit__ = MagicMock(return_value=False)
        transport = MagicMock(return_value=resp)
    with patch("urllib.request.urlopen", transport):
        try:
            return inference._call_inference_provider(provider, "hi", "", key)
        except InferenceError as exc:
            return str(exc)


# --- An HTTP error body, by the secret's position against the cap -----------

def _positions(secret: str) -> Iterator[tuple[str, int]]:
    """(name, index of the secret's first character in the body)."""
    n = len(secret)
    yield "wholly-before", _ERROR_BODY_CAP - n - 1
    yield "ending-at-the-cap", _ERROR_BODY_CAP - n
    for k in range(1, n):
        yield f"across-{k}-before", _ERROR_BODY_CAP - k
    yield "wholly-after", _ERROR_BODY_CAP


CAP_CELLS = [
    pytest.param(provider, which, name, start,
                 id=f"{provider}-{which}-{name}")
    for provider in inference._PROVIDERS
    for which, (secret, _) in SECRETS.items()
    for name, start in _positions(secret)
]


@pytest.mark.parametrize(("provider", "which", "name", "start"), CAP_CELLS)
def test_a_secret_at_every_position_against_the_cap(
    provider: str, which: str, name: str, start: int,
) -> None:
    """Spaces up to the secret, so the 200-character window that follows
    the cut reaches it wherever it sits."""
    secret, key = SECRETS[which]
    body = b" " * start + secret.encode() + b" tail" * 8
    assert len(body) > _ERROR_BODY_CAP
    message = _message(provider, key, raises=_http_error(body))
    assert message.endswith("... (truncated)"), message
    assert_no_part_of(secret, message)


# --- A body under the cap, every place its text reaches a message ------------

def _under_cap_bodies(secret: str) -> dict[str, bytes]:
    text = " " * 150 + secret + " tail"
    return {
        "error-message": json.dumps({"error": {"message": text}}).encode(),
        "error-string": json.dumps({"error": text}).encode(),
        "message": json.dumps({"message": text}).encode(),
        "raw-text": text.encode(),
        # across the 200-character bound of the quoted text
        "across-the-bound": (" " * 0 + "x" * 180 + secret + " tail").encode(),
    }


UNDER_CAP_CELLS = [
    pytest.param(provider, which, form, id=f"{provider}-{which}-{form}")
    for provider in inference._PROVIDERS
    for which in SECRETS
    for form in _under_cap_bodies(KEY)
]


@pytest.mark.parametrize(("provider", "which", "form"), UNDER_CAP_CELLS)
def test_a_secret_in_an_error_body_under_the_cap(
    provider: str, which: str, form: str,
) -> None:
    secret, key = SECRETS[which]
    body = _under_cap_bodies(secret)[form]
    assert_no_part_of(secret, _message(provider, key, raises=_http_error(body)))


# --- A successful exchange's text: a body that is not JSON, a shape report --

def _ok_bodies(secret: str, style: str) -> dict[str, bytes]:
    if style == "anthropic":
        shaped = {
            "stop-reason": {"content": [], "stop_reason": secret},
            "keys": {"content": [{"type": "text", secret: 1}]},
            "types": {"content": [{"type": secret}]},
        }
    else:
        shaped = {
            # `content` null, so the reply is refused and the refusal
            # quotes `finish_reason`; an empty string is a completion, and
            # the message would be empty whatever redaction did.
            "finish-reason": {"choices": [{"message": {"content": None},
                                           "finish_reason": secret}]},
            "refusal": {"choices": [{"message": {"content": "",
                                                 "refusal": secret}}]},
            "keys": {"choices": [{secret: 1}]},
        }
    bodies = {name: json.dumps(v).encode() for name, v in shaped.items()}
    bodies["not-json"] = ("<html>" + secret + "</html>").encode()
    return bodies


OK_CELLS = [
    pytest.param(provider, which, form, id=f"{provider}-{which}-{form}")
    for provider, cfg in inference._PROVIDERS.items()
    for which in SECRETS
    for form in _ok_bodies(KEY, cfg.response_style)
]


@pytest.mark.parametrize(("provider", "which", "form"), OK_CELLS)
def test_a_secret_in_a_response_the_message_quotes(
    provider: str, which: str, form: str,
) -> None:
    secret, key = SECRETS[which]
    style = inference._PROVIDERS[provider].response_style
    message = _message(provider, key, body=_ok_bodies(secret, style)[form])
    # Each form is refused, so the message is one that quotes the field:
    # a completion would pass the assertion below with nothing checked.
    assert message.startswith(f"Inference provider '{provider}'"), message
    assert_no_part_of(secret, message)


# --- An exception's text, at the host boundary ------------------------------

_SOURCE = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference, IO>)
{
  let @Result<String, String> = Inference.complete("hi");
  match @Result<String, String>.0 {
    Ok(@String) -> {
      IO.print(@String.0);
      0
    },
    Err(@String) -> {
      IO.print(@String.0);
      1
    }
  }
}
"""


def _boundary(provider: str, key: str, exc: BaseException,
              *, debug: bool = False) -> str:
    """The `Err` the host gives when the exchange raises *exc*."""
    env = {inference._PROVIDERS[provider].env_key: key,
           "VERA_INFERENCE_PROVIDER": provider}
    with patch("urllib.request.urlopen", MagicMock(side_effect=exc)), \
            patch.dict("os.environ",
                       {"VERA_DEBUG_HOST_ERRORS": "1"} if debug else {}):
        ran = pipeline.run(_compile_ok(_SOURCE), env_vars=env,
                           capture_stderr=False)
    assert ran.ok, ran.trap
    return ran.stdout


def _exceptions(secret: str) -> dict[str, BaseException]:
    return {
        "quotes-it": RuntimeError(f"connection reset talking with {secret}"),
        "quotes-its-repr": ValueError(f"Invalid header value {secret!r}"),
        "quotes-its-bytes": ValueError(
            f"Invalid header value {secret.encode()!r}"),
    }


BOUNDARY_CELLS = [
    pytest.param(provider, which, form, debug,
                 id=f"{provider}-{which}-{form}{'-debug' if debug else ''}")
    for provider in inference._PROVIDERS
    for which in SECRETS
    for form in _exceptions(KEY)
    for debug in (False, True)
]


@pytest.mark.parametrize(("provider", "which", "form", "debug"),
                         BOUNDARY_CELLS)
def test_a_secret_an_exception_quotes(
    provider: str, which: str, form: str, debug: bool,
) -> None:
    """`VERA_DEBUG_HOST_ERRORS=1` changes nothing here: the binding turns
    every exception into the `Err` before any re-raise could see it."""
    secret, key = SECRETS[which]
    stdout = _boundary(provider, key, _exceptions(secret)[form], debug=debug)
    assert stdout.startswith(f"Inference provider '{provider}'"), stdout
    assert_no_part_of(secret, stdout)


@pytest.mark.parametrize("provider", list(inference._PROVIDERS))
@pytest.mark.parametrize("char", ["\\", "'"])
def test_a_key_an_exception_quotes_escaped(provider: str, char: str) -> None:
    """A key a header can carry may still hold a character `repr` escapes
    (a backslash, a quote), so an exception quoting its `repr` holds a
    spelling the exact match does not find; that spelling is redacted."""
    key = KEY[:20] + char + KEY[20:]
    stdout = _boundary(provider, key, ValueError(f"bad value {key!r}"))
    assert_no_part_of(KEY[:20], stdout)
    assert_no_part_of(KEY[20:], stdout)


# --- A key an HTTP header cannot carry ---------------------------------------

@pytest.fixture
def local_endpoints(monkeypatch: pytest.MonkeyPatch) -> None:
    """Every provider's endpoint on a local port nothing listens on, so a
    request the transport did build goes nowhere."""
    for name, cfg in list(inference._PROVIDERS.items()):
        monkeypatch.setitem(inference._PROVIDERS, name,
                            dataclasses.replace(cfg, url="http://127.0.0.1:9/"))


LINE_END_CELLS = [
    pytest.param(provider, end, id=f"{provider}-{name}")
    for provider in inference._PROVIDERS
    for name, end in (("crlf", "\r\n"), ("lf", "\n"), ("cr", "\r"),
                      ("tab", "\t"), ("non-ascii", "’"))
]


@pytest.mark.parametrize(("provider", "end"), LINE_END_CELLS)
def test_a_key_holding_a_line_end_is_refused_by_its_variable(
    provider: str, end: str, local_endpoints: None,
) -> None:
    """The refusal names the variable that holds the key and holds no part
    of it, for both authorisation styles (`x-api-key` and `Bearer`)."""
    key = KEY + end
    env_key = inference._PROVIDERS[provider].env_key
    for debug in (False, True):
        env = {env_key: key, "VERA_INFERENCE_PROVIDER": provider}
        with patch.dict("os.environ",
                        {"VERA_DEBUG_HOST_ERRORS": "1"} if debug else {}):
            ran = pipeline.run(_compile_ok(_SOURCE), env_vars=env,
                               capture_stderr=False)
        assert ran.ok, ran.trap
        assert env_key in ran.stdout, ran.stdout
        assert "cannot carry" in ran.stdout, ran.stdout
        assert_no_part_of(KEY, ran.stdout)


# --- Every rule on the original text, by key shape, spelling and split -------

#: The shapes a configured key takes: plain (no recognisable prefix); one
#: holding a credential-shaped part, which the pattern rule also matches;
#: one holding a backslash, which `repr` escapes, so it has two spellings;
#: and a short one.
KEY_SHAPES: dict[str, str] = {
    "plain": KEY,
    "credential-part": KEY[:12] + "-sk-" + KEY[12:20] + "-" + KEY[20:26],
    "backslash": KEY[:15] + "\\" + KEY[15:30],
    "short": KEY[30:36],
    "quote": KEY[:10] + '"' + KEY[10:24],
    "solidus": KEY[:8] + "/" + KEY[8:20],
    "markup": KEY[:6] + "&<>'" + KEY[6:16],
    # Each layer spells this one differently: `repr` escapes the
    # apostrophe, JSON the quote, and JSON may or may not escape the solidus.
    "every-quote": KEY[:4] + "'" + KEY[4:8] + '"' + KEY[8:12] + "/" + KEY[12:18],
}

#: A fragment of the key no longer than this may stand in a message: the
#: message's own words (`[redacted]`, `... (truncated)`, the provider's
#: name) share runs of a few characters with any key, so a shorter run
#: cannot be told from the key, and the cut rule takes even one character
#: at the cut, so nothing longer is left for this floor to excuse.
FLOOR = 3


def _spellings(key: str) -> dict[str, str]:
    """The key under each quoting layer that can stand between a provider
    and the message, each spelling once: as it is, Python's `repr` (an
    exception's text), a JSON string (an error body), with the solidus
    escaped too (JSON allows it), and an HTML page (a proxy's), with the
    apostrophe as `&#x27;` and as `&#39;`."""
    js = json.dumps(key)[1:-1]
    htm = html.escape(key, quote=True)
    named = {
        "raw": key, "repr": repr(key)[1:-1], "json": js,
        "json-solidus": js.replace("/", "\\/"), "html": htm,
        "html-decimal": htm.replace("&#x27;", "&#39;"),
    }
    seen: dict[str, str] = {}
    for name, text in named.items():
        if text not in seen.values():
            seen[name] = text
    return seen


def test_the_redaction_knows_every_spelling() -> None:
    """`_key_spellings` gives each spelling this file names, for every
    shape, and no other."""
    for key in KEY_SHAPES.values():
        assert set(inference._key_spellings(key)) == set(
            _spellings(key).values()), key


def _fragments(key: str) -> set[str]:
    """Every run of any spelling of *key* longer than :data:`FLOOR`."""
    return {
        spelling[i:i + FLOOR + 1]
        for spelling in _spellings(key).values()
        for i in range(len(spelling) - FLOOR)
    }


def _split_positions(spelling: str) -> list[tuple[str, int]]:
    n = len(spelling)
    return [("wholly-before", _ERROR_BODY_CAP - n - 1),
            ("ending-at-the-cap", _ERROR_BODY_CAP - n),
            *((f"{k}-before", _ERROR_BODY_CAP - k) for k in range(1, n)),
            ("wholly-after", _ERROR_BODY_CAP)]


SPLIT_CELLS = [
    pytest.param(shape, spelling, name, start,
                 id=f"{shape}-{spelling}-{name}")
    for shape, key in KEY_SHAPES.items()
    for spelling, text in _spellings(key).items()
    for name, start in _split_positions(text)
]


@pytest.mark.parametrize(("shape", "spelling", "name", "start"), SPLIT_CELLS)
def test_every_split_of_every_spelling_of_every_key_shape(
    shape: str, spelling: str, name: str, start: int,
) -> None:
    key = KEY_SHAPES[shape]
    text = _spellings(key)[spelling]
    body = b" " * start + text.encode() + b" tail" * 8
    message = _message("mistral", key, raises=_http_error(body))
    found = sorted(f for f in _fragments(key) if f in message)
    assert not found, (found, message)


def test_repro_a_key_holding_a_credential_shaped_part_cut_inside_it() -> None:
    """The pattern rule rewrote the `sk-` part first, and the cut rule then
    found no prefix of the key: `OpaqueCredentialPrefix-` was quoted."""
    key = "OpaqueCredentialPrefix-sk-12345678-END"
    text = key[:key.index("12345678") + 8]
    assert inference._redact_cut(" " + text, key) == " [redacted]"


def test_repro_an_escaped_key_cut_inside_it() -> None:
    """The cut rule tried prefixes of the key as it is, not as `repr`
    spells it, so a cut escaped spelling was quoted."""
    key = r"OpaquePrefix\RemainderSecret"
    escaped = repr(key)[1:-1]
    text = escaped[:escaped.index("Remainder") + len("Remainder")]
    assert inference._redact_cut(" " + text, key) == " [redacted]"


def test_repro_a_token_cut_where_the_key_s_first_character_ends_it() -> None:
    """The key-prefix rule matched the last `A` and returned before the
    credential-tail rule ran, leaving `sk-123456`."""
    assert inference._redact_cut("x sk-123456A", "ABCDEFGH") == "x [redacted]"


def test_spans_that_touch_are_one_redaction() -> None:
    """Two secrets side by side are replaced once, and text between two
    secrets stays."""
    assert inference._redact("ABCDEFGHABCDEFGH", "ABCDEFGH") == "[redacted]"
    assert inference._redact("ABCDEFGH ABCDEFGH", "ABCDEFGH") == (
        "[redacted] [redacted]")


def test_repro_1854_a_key_across_the_cap_leaves_nothing() -> None:
    """The issue's case: 20 of 40 characters before the cap."""
    key = "K" * 40
    body = b" " * (_ERROR_BODY_CAP - 20) + b"K" * 40 + b"tail"
    detail = inference._read_error_body(_http_error(body), key)
    assert "K" not in detail.replace("... (truncated)", ""), detail


def test_repro_1854_a_key_with_a_line_end_never_reaches_the_err(
    local_endpoints: None,
) -> None:
    for provider, model, var in (
            ("anthropic", "claude-opus-5", "VERA_ANTHROPIC_API_KEY"),
            ("openai", "gpt-5.6-sol", "VERA_OPENAI_API_KEY")):
        message = _message(provider, KEY + "\r\n")
        assert message.startswith(
            f"Inference provider '{provider}' ({model}): {var} holds a "
            f"character an HTTP header cannot carry"), message
        assert_no_part_of(KEY, message)


# --- Unparametrised: each rule's exact output, for the sampled gate --------

_BACKSLASH_KEY = KEY[:15] + "\\" + KEY[15:30]
_ESCAPED = repr(_BACKSLASH_KEY)[1:-1]


def test_repro_the_key_whole_is_replaced_once() -> None:
    assert inference._redact(f"x {KEY} y", KEY) == "x [redacted] y"
    assert inference._redact(f"x {_ESCAPED} y", _BACKSLASH_KEY) == (
        "x [redacted] y")
    assert inference._redact(f"x {_BACKSLASH_KEY} y", _BACKSLASH_KEY) == (
        "x [redacted] y")


def test_repro_a_credential_shaped_token_is_replaced() -> None:
    assert inference._redact("x sk-ABCDEFGH y", "") == "x [redacted] y"


def test_repro_no_key_redacts_nothing_but_tokens() -> None:
    assert inference._redact("plain text sk", "") == "plain text sk"
    assert inference._redact_cut("plain text", "") == "plain text"


def test_repro_every_proper_prefix_of_the_key_at_the_cut() -> None:
    """The longest (all but one character) and the shortest (one) prefix,
    in each spelling."""
    assert inference._redact_cut(" " + KEY[:-1], KEY) == " [redacted]"
    assert inference._redact_cut(" " + KEY[:1], KEY) == " [redacted]"
    assert inference._redact_cut(" " + KEY[:2], KEY) == " [redacted]"
    assert inference._redact_cut(" " + _ESCAPED[:-1], _BACKSLASH_KEY) == (
        " [redacted]")
    assert inference._redact_cut(" " + _ESCAPED[:17], _BACKSLASH_KEY) == (
        " [redacted]")


def test_repro_a_token_s_start_at_the_cut() -> None:
    assert inference._redact_cut(" ask-12", "") == " a[redacted]"
    assert inference._redact("x sk-12", "") == "x sk-12"


@pytest.mark.usefixtures("local_endpoints")
def test_repro_the_refusal_s_bounds() -> None:
    """A space and `~` (0x20 and 0x7E) are carried by a header and sent;
    DEL (0x7F) is a control character and refused."""
    for key in (KEY + " x", KEY + "~"):
        with patch("urllib.request.urlopen",
                   MagicMock(side_effect=urllib.error.URLError("sent"))):
            with pytest.raises(urllib.error.URLError):
                inference._call_inference_provider("anthropic", "hi", "", key)
    assert "cannot carry" in _message("anthropic", KEY + "\x7f")


def test_a_cut_text_with_no_secret_at_its_end_keeps_its_end() -> None:
    """Negative space: the end is redacted only where it could begin the
    key or a credential-shaped token."""
    body = b" " * (_ERROR_BODY_CAP - 9) + b"plain end" + b" tail"
    detail = inference._read_error_body(_http_error(body), KEY)
    assert detail == "plain end... (truncated)", detail


def test_a_key_of_printable_ascii_is_sent() -> None:
    """Negative space: a key the header can carry reaches the transport."""
    seen: list[object] = []

    def capture(req: object, timeout: float) -> None:
        seen.append(req)
        raise urllib.error.URLError("stop")

    with patch("urllib.request.urlopen", side_effect=capture):
        with pytest.raises(urllib.error.URLError):
            inference._call_inference_provider("anthropic", "hi", "", KEY)
    assert len(seen) == 1


def test_repro_a_json_quoted_key_cut_inside_it() -> None:
    """A key holding a double quote is `\\"` in a JSON error body, which
    neither the key as it is nor its `repr` spells."""
    key = 'Opaque"CredentialRemainder'
    assert inference._redact_cut(' Opaque\\"Credential', key) == " [redacted]"
    assert inference._redact(f'x {json.dumps(key)[1:-1]} y', key) == (
        "x [redacted] y")


def test_repro_an_html_quoted_key_cut_inside_it() -> None:
    key = "Opaque<Credential>Remainder"
    assert inference._redact_cut(" Opaque&lt;Crede", key) == " [redacted]"
    assert inference._redact_cut(" Opaque&l", key) == " [redacted]"
