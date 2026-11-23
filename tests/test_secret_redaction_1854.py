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
            return inference._call_inference_provider(provider, "hi", "", key, held=inference.HeldKeys((key,)))
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


# --- Every rule on the original text, by key shape, form and split ----------

#: The shapes a configured key takes: plain (no recognisable prefix); one
#: holding a credential-shaped part, which the pattern rule also matches;
#: a short one; and one holding every character a quoting layer re-spells
#: by a table of its own (`"`, `\`, `/`, `'`, `&`, `<`, `>`).
KEY_SHAPES: dict[str, str] = {
    "plain": KEY,
    "credential-part": KEY[:12] + "-sk-" + KEY[12:20] + "-" + KEY[20:26],
    "short": KEY[30:36],
    "special": KEY[:4] + '"' + KEY[4:7] + "\\" + KEY[7:10] + "/" + KEY[10:12]
               + "'" + KEY[12:14] + "&<>" + KEY[14:18],
}

#: A fragment of the key no longer than this may stand in a message: the
#: message's own words (`[redacted]`, `... (truncated)`, the provider's
#: name) share runs of a few characters with any key, so a shorter run
#: cannot be told from the key, and the cut rule takes even one character
#: at the cut, so nothing longer is left for this floor to excuse.
FLOOR = 3

_HTML_NAMES = {"&": "amp", "<": "lt", ">": "gt", '"': "quot", "'": "apos"}


def char_forms(char: str) -> list[str]:
    """Every form a quoting layer may give *char* on its own: the character;
    a backslash before it where JSON or `repr` writes one; JSON's `\\uXXXX`
    and `repr`'s `\\xXX`, hex digits in either case; HTML's decimal and hex
    entities, with and without leading zeros, and its named one."""
    code = ord(char)
    forms = [char]
    if char in "\"\\/'":
        forms.append("\\" + char)
    forms += [f"\\u{code:04x}", f"\\u{code:04X}", f"\\x{code:02x}",
              f"\\x{code:02X}", f"&#{code};", f"&#00{code};", f"&#x{code:x};",
              f"&#X{code:X};", f"&#x00{code:x};"]
    if char in _HTML_NAMES:
        forms.append(f"&{_HTML_NAMES[char]};")
    return forms


#: How a key is spelled, each occurrence of a character choosing its own
#: form: the two corners (no character quoted; every character as JSON's
#: `\uXXXX`), and three seeded draws, pinned by their seeds.
SPELLING_SEEDS = (1, 2, 3)


def spellings(key: str) -> dict[str, str]:
    named = {"none": key,
             "all": "".join(f"\\u{ord(c):04x}" for c in key)}
    for seed in SPELLING_SEEDS:
        rng = random.Random(f"{key}:{seed}")
        named[f"drawn{seed}"] = "".join(
            rng.choice(char_forms(c)) for c in key)
    return named


def _fragments(key: str, text: str) -> set[str]:
    """Every run longer than :data:`FLOOR` of the key, and of *text*, a
    spelling of it."""
    return {s[i:i + FLOOR + 1] for s in (key, text)
            for i in range(len(s) - FLOOR)}


def _split_positions(spelling: str) -> list[tuple[str, int]]:
    """Where the spelling stands against the cap: wholly before it, ending
    at it, across it at every split (inside a character's form among
    them), wholly after it."""
    n = len(spelling)
    return [("wholly-before", _ERROR_BODY_CAP - n - 1),
            ("ending-at-the-cap", _ERROR_BODY_CAP - n),
            *((f"{k}-before", _ERROR_BODY_CAP - k) for k in range(1, n)),
            ("wholly-after", _ERROR_BODY_CAP)]


SPLIT_CELLS = [
    pytest.param(shape, spelling, name, start,
                 id=f"{shape}-{spelling}-{name}")
    for shape, key in KEY_SHAPES.items()
    for spelling, text in spellings(key).items()
    for name, start in _split_positions(text)
]


@pytest.mark.parametrize(("shape", "spelling", "name", "start"), SPLIT_CELLS)
def test_every_split_of_every_spelling_of_every_key_shape(
    shape: str, spelling: str, name: str, start: int,
) -> None:
    key = KEY_SHAPES[shape]
    text = spellings(key)[spelling]
    body = b" " * start + text.encode() + b" tail" * 8
    message = _message("mistral", key, raises=_http_error(body))
    found = sorted(f for f in _fragments(key, text) if f in message)
    assert not found, (found, message)


def test_every_form_of_every_printable_character() -> None:
    """Each form of each character a key can hold (printable ASCII), on its
    own inside a key, is redacted whole."""
    for code in range(0x20, 0x7F):
        char = chr(code)
        key = "Qz" + char + "Zq"
        for form in char_forms(char):
            text = f" Qz{form}Zq "
            assert inference._redact(text, held=inference.HeldKeys((key,))) == " [redacted] ", (form, key)


def test_repro_a_mixed_solidus_escape() -> None:
    """One solidus escaped and the next not, as JSON allows."""
    key = "Opaque/First/Second"
    assert inference._redact("x Opaque\\/First/Second y", held=inference.HeldKeys((key,))) == (
        "x [redacted] y")


def test_repro_a_unicode_escape_of_a_printable_character() -> None:
    assert inference._redact("x Opaque\\u0026Second y", held=inference.HeldKeys(("Opaque&Second",))) == (
        "x [redacted] y")


def test_repro_a_unicode_escape_of_the_first_character_at_a_cut() -> None:
    """`\\u004F` for the key's first `O`, `\\"` for its quote, cut after
    `Credential`."""
    key = 'Opaque"CredentialRemainder'
    assert inference._redact_cut(' \\u004Fpaque\\"Credential', held=inference.HeldKeys((key,))) == (
        " [redacted]")


def test_repro_a_cut_inside_a_character_s_escape() -> None:
    """The cut ends inside the next character's form: `\\u002` goes with
    the prefix before it, and so does a form of the first character alone."""
    key = "Opaque&Second"
    assert inference._redact_cut(" Opaque\\u002", held=inference.HeldKeys((key,))) == " [redacted]"
    assert inference._redact_cut(" \\u00", held=inference.HeldKeys((key,))) == " [redacted]"
    assert inference._redact_cut(" Opaque&am", held=inference.HeldKeys((key,))) == " [redacted]"
    # Negative space: a form that is no start of the first character's
    # (`O` is `O`, never `\u01..`).
    assert inference._redact_cut(" plain end\\u01", held=inference.HeldKeys((key,))) == (
        " plain end\\u01")


def test_the_cost_is_bounded_by_the_text_and_the_key() -> None:
    """A 200-character key over 64 KiB bodies a hostile provider could
    choose, its own key among them: each redaction stays in milliseconds."""
    import time

    key = (KEY * 5)[:196] + '&/"\\'
    escaped = "".join(f"\\u{ord(c):04x}" for c in key)
    n = _ERROR_BODY_CAP
    bodies = ["\\" * n, "\\\\" * (n // 2), "&amp;" * (n // 5),
              "\\u0041" * (n // 6), "\\u00" * (n // 4),
              (key * (n // len(key) + 1))[:n],
              (key[:-1] * (n // len(key) + 1))[:n],
              (escaped * (n // len(escaped) + 1))[:n]]
    for body in bodies:
        started = time.perf_counter()
        inference._redact_cut(body, held=inference.HeldKeys((key,)))
        assert time.perf_counter() - started < 0.5, body[:20]


def test_repro_a_key_holding_a_credential_shaped_part_cut_inside_it() -> None:
    """The pattern rule rewrote the `sk-` part first, and the cut rule then
    found no prefix of the key: `OpaqueCredentialPrefix-` was quoted."""
    key = "OpaqueCredentialPrefix-sk-12345678-END"
    text = key[:key.index("12345678") + 8]
    assert inference._redact_cut(" " + text, held=inference.HeldKeys((key,))) == " [redacted]"


def test_repro_an_escaped_key_cut_inside_it() -> None:
    """The cut rule tried prefixes of the key as it is, not as `repr`
    spells it, so a cut escaped spelling was quoted."""
    key = r"OpaquePrefix\RemainderSecret"
    escaped = repr(key)[1:-1]
    text = escaped[:escaped.index("Remainder") + len("Remainder")]
    assert inference._redact_cut(" " + text, held=inference.HeldKeys((key,))) == " [redacted]"


def test_repro_a_token_cut_where_the_key_s_first_character_ends_it() -> None:
    """The key-prefix rule matched the last `A` and returned before the
    credential-tail rule ran, leaving `sk-123456`."""
    assert inference._redact_cut("x sk-123456A", held=inference.HeldKeys(("ABCDEFGH",))) == "x [redacted]"


def test_spans_that_touch_are_one_redaction() -> None:
    """Two secrets side by side are replaced once, and text between two
    secrets stays."""
    assert inference._redact("ABCDEFGHABCDEFGH", held=inference.HeldKeys(("ABCDEFGH",))) == "[redacted]"
    assert inference._redact("ABCDEFGH ABCDEFGH", held=inference.HeldKeys(("ABCDEFGH",))) == (
        "[redacted] [redacted]")


def test_repro_1854_a_key_across_the_cap_leaves_nothing() -> None:
    """The issue's case: 20 of 40 characters before the cap."""
    key = "K" * 40
    body = b" " * (_ERROR_BODY_CAP - 20) + b"K" * 40 + b"tail"
    detail = inference._read_error_body(_http_error(body), held=inference.HeldKeys((key,)))
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
    assert inference._redact(f"x {KEY} y", held=inference.HeldKeys((KEY,))) == "x [redacted] y"
    assert inference._redact(f"x {_ESCAPED} y", held=inference.HeldKeys((_BACKSLASH_KEY,))) == (
        "x [redacted] y")
    assert inference._redact(f"x {_BACKSLASH_KEY} y", held=inference.HeldKeys((_BACKSLASH_KEY,))) == (
        "x [redacted] y")


def test_repro_a_credential_shaped_token_is_replaced() -> None:
    assert inference._redact("x sk-ABCDEFGH y", held=inference.HeldKeys(("",))) == "x [redacted] y"


def test_repro_no_key_redacts_nothing_but_tokens() -> None:
    assert inference._redact("plain text sk", held=inference.HeldKeys(("",))) == "plain text sk"
    assert inference._redact_cut("plain text", held=inference.HeldKeys(("",))) == "plain text"


def test_repro_every_proper_prefix_of_the_key_at_the_cut() -> None:
    """The longest (all but one character) and the shortest (one) prefix,
    in each spelling."""
    assert inference._redact_cut(" " + KEY[:-1], held=inference.HeldKeys((KEY,))) == " [redacted]"
    assert inference._redact_cut(" " + KEY[:1], held=inference.HeldKeys((KEY,))) == " [redacted]"
    assert inference._redact_cut(" " + KEY[:2], held=inference.HeldKeys((KEY,))) == " [redacted]"
    assert inference._redact_cut(" " + _ESCAPED[:-1], held=inference.HeldKeys((_BACKSLASH_KEY,))) == (
        " [redacted]")
    assert inference._redact_cut(" " + _ESCAPED[:17], held=inference.HeldKeys((_BACKSLASH_KEY,))) == (
        " [redacted]")


def test_repro_a_token_s_start_at_the_cut() -> None:
    assert inference._redact_cut(" ask-12", held=inference.HeldKeys(("",))) == " a[redacted]"
    assert inference._redact("x sk-12", held=inference.HeldKeys(("",))) == "x sk-12"


@pytest.mark.usefixtures("local_endpoints")
def test_repro_the_refusal_s_bounds() -> None:
    """A space and `~` (0x20 and 0x7E) are carried by a header and sent;
    DEL (0x7F) is a control character and refused."""
    for key in (KEY + " x", KEY + "~"):
        with patch("urllib.request.urlopen",
                   MagicMock(side_effect=urllib.error.URLError("sent"))):
            with pytest.raises(urllib.error.URLError):
                inference._call_inference_provider("anthropic", "hi", "", key, held=inference.HeldKeys((key,)))
    assert "cannot carry" in _message("anthropic", KEY + "\x7f")


def test_a_cut_text_with_no_secret_at_its_end_keeps_its_end() -> None:
    """Negative space: the end is redacted only where it could begin the
    key or a credential-shaped token."""
    body = b" " * (_ERROR_BODY_CAP - 9) + b"plain end" + b" tail"
    detail = inference._read_error_body(_http_error(body), held=inference.HeldKeys((KEY,)))
    assert detail == "plain end... (truncated)", detail


def test_a_key_of_printable_ascii_is_sent() -> None:
    """Negative space: a key the header can carry reaches the transport."""
    seen: list[object] = []

    def capture(req: object, timeout: float) -> None:
        seen.append(req)
        raise urllib.error.URLError("stop")

    with patch("urllib.request.urlopen", side_effect=capture):
        with pytest.raises(urllib.error.URLError):
            inference._call_inference_provider("anthropic", "hi", "", KEY, held=inference.HeldKeys((KEY,)))
    assert len(seen) == 1


def test_repro_a_json_quoted_key_cut_inside_it() -> None:
    """A key holding a double quote is `\\"` in a JSON error body, which
    neither the key as it is nor its `repr` spells."""
    key = 'Opaque"CredentialRemainder'
    assert inference._redact_cut(' Opaque\\"Credential', held=inference.HeldKeys((key,))) == " [redacted]"
    assert inference._redact(f'x {json.dumps(key)[1:-1]} y', held=inference.HeldKeys((key,))) == (
        "x [redacted] y")


def test_repro_an_html_quoted_key_cut_inside_it() -> None:
    key = "Opaque<Credential>Remainder"
    assert inference._redact_cut(" Opaque&lt;Crede", held=inference.HeldKeys((key,))) == " [redacted]"
    assert inference._redact_cut(" Opaque&l", held=inference.HeldKeys((key,))) == " [redacted]"


# --- Which input carries the key, by which message route --------------------
#
# Every text that reaches the `Err` of `Inference.complete` leaves through
# one function, `_err` inside `host_inference_complete`, which redacts every
# key the host holds.  The matrix puts a held key in each input a message
# can quote, and runs each route a message can take: the key itself (a
# line end in it, so the host refuses it), the model name
# (`VERA_INFERENCE_MODEL`), the provider name (`VERA_INFERENCE_PROVIDER`,
# which the host reads lower-cased), a header value by way of an
# exception's text, and the provider's body.  The base URL is not an
# input: no variable configures it.

ROUTE_BODIES: dict[str, str] = {
    "http-error": '{{"error": {{"message": "rejected {k}"}}}}',
    "not-json": "<html>{k}</html>",
    "shape": '{{"{k}": 1}}',
}

#: A held key that mixes case, so a lower-cased quotation of it is not the
#: key as written.
MIXED_KEY = "Mx" + KEY[2:]


def _route_env(provider: str, carrier: str, route: str) -> dict[str, str]:
    key = MIXED_KEY + ("\n" if route == "refusal" else "")
    env = {inference._PROVIDERS[provider].env_key: key,
           "VERA_INFERENCE_PROVIDER": provider}
    if carrier == "model":
        env["VERA_INFERENCE_MODEL"] = key
    if carrier == "provider":
        env["VERA_INFERENCE_PROVIDER"] = MIXED_KEY
    return env


def _route_transport(carrier: str, route: str) -> MagicMock:
    quoted = MIXED_KEY if carrier in ("header", "body") else "nothing"
    if route == "transport":
        return MagicMock(side_effect=ValueError(
            f"Invalid header value {quoted.encode()!r}"))
    body = ROUTE_BODIES.get(route, "{{}}").format(k=quoted).encode()
    if route == "http-error":
        return MagicMock(side_effect=_http_error(body))
    resp = MagicMock()
    resp.read.return_value = body
    resp.__enter__ = lambda s: s
    resp.__exit__ = MagicMock(return_value=False)
    return MagicMock(return_value=resp)


#: (carrier, route): each route the carrier's text can reach a message by.
CARRIER_ROUTES: tuple[tuple[str, str], ...] = (
    ("key", "refusal"),
    *(("model", route) for route in
      ("transport", "http-error", "not-json", "shape", "refusal")),
    ("provider", "unknown-provider"),
    ("header", "transport"),
    *(("body", route) for route in ("http-error", "not-json", "shape")),
)

CARRIER_CELLS = [
    pytest.param(provider, carrier, route,
                 id=f"{provider}-{carrier}-{route}")
    for provider in inference._PROVIDERS
    for carrier, route in CARRIER_ROUTES
]


def _carried(provider: str, carrier: str, route: str) -> str:
    env = _route_env(provider, carrier, route)
    with patch("urllib.request.urlopen", _route_transport(carrier, route)):
        ran = pipeline.run(_compile_ok(_SOURCE), env_vars=env,
                           capture_stderr=False)
    assert ran.ok, ran.trap
    return ran.stdout


@pytest.mark.usefixtures("local_endpoints")
@pytest.mark.parametrize(("provider", "carrier", "route"), CARRIER_CELLS)
def test_a_held_key_in_every_input_by_every_route(
    provider: str, carrier: str, route: str,
) -> None:
    message = _carried(provider, carrier, route)
    assert message, message
    assert_no_part_of(MIXED_KEY, message)
    assert_no_part_of(MIXED_KEY.lower(), message.lower())


@pytest.mark.usefixtures("local_endpoints")
def test_repro_a_model_name_holding_the_key() -> None:
    """The fourth review's instance: the model name holds the key, which
    the key refusal and every provider message quoted."""
    for route in ("refusal", "transport", "shape"):
        message = _carried("anthropic", "model", route)
        assert "(Mx" not in message, message
        assert_no_part_of(MIXED_KEY, message)


@pytest.mark.usefixtures("local_endpoints")
def test_repro_a_provider_name_holding_the_key() -> None:
    message = _carried("mistral", "provider", "unknown-provider")
    assert message.startswith("Unknown inference provider '[redacted]'"), (
        message)


def test_repro_a_held_key_of_a_provider_not_selected() -> None:
    mixed = "AbCdEf" + "123456"
    var = inference._PROVIDERS["openai"].env_key
    held = inference._held_keys({var: mixed,
                                 "VERA_INFERENCE_PROVIDER": "anthropic"})
    assert held.keys == (mixed, mixed.lower())
    assert inference._redact(f"x {mixed.lower()} y", held=held) == (
        "x [redacted] y")


def _calls_by_function(name: str) -> set[str]:
    """The functions of `vera/runtime/inference.py` that call *name*."""
    import ast as pyast
    import inspect

    tree = pyast.parse(inspect.getsource(inference))
    owners: set[str] = set()

    def visit(node: pyast.AST, owner: str) -> None:
        for child in pyast.iter_child_nodes(node):
            here = (child.name if isinstance(child, pyast.FunctionDef)
                    else owner)
            if (isinstance(child, pyast.Call)
                    and isinstance(child.func, pyast.Name)
                    and child.func.id == name):
                owners.add(owner)
            visit(child, here)

    visit(tree, "<module>")
    return owners


def test_every_err_text_leaves_through_the_one_exit() -> None:
    """The `Err` of `Inference.complete` is built in one function, which
    redacts; a cut is made in one function, which redacts first."""
    assert _calls_by_function("_alloc_result_err_string") == {"_err"}
    assert "_err" in _calls_by_function("_redact")
    assert _calls_by_function("_truncate") == {"_safe"}


#: The functions that remove a secret from a text, or render a text that
#: may hold one: each takes the held set, and nothing else, as `held`.
REDACTIONS = frozenset({
    "_secret_spans", "_redact", "_redact_cut", "_safe", "_describe_keys",
    "_describe_types", "_reason_clause", "_empty_completion_error",
    "_missing_or_wrong", "_text_fragments", "_error_body_detail",
    "_read_error_body", "_call_inference_provider",
})


def test_every_redaction_takes_the_one_held_set() -> None:
    """One notion of the host's secrets (#1854): `_held_keys` builds it,
    once, in the host function; every redaction, cut or not, takes it as
    its keyword-only `held`, and no call passes anything but the name
    `held`.  The selected key is a parameter only where it is sent
    (`_call_inference_provider`, `_refuse_unsendable_key`) and of the one
    key's matcher (`_key_spans`, `_key_patterns`)."""
    import ast as pyast
    import inspect

    tree = pyast.parse(inspect.getsource(inference))
    defs = {n.name: n for n in pyast.walk(tree)
            if isinstance(n, pyast.FunctionDef)}
    assert REDACTIONS <= set(defs), REDACTIONS - set(defs)
    for name in REDACTIONS:
        args = defs[name].args
        held = [a for a in args.kwonlyargs if a.arg == "held"]
        assert held, name
        assert pyast.unparse(held[0].annotation) == "HeldKeys", name
        params = {a.arg for a in [*args.posonlyargs, *args.args]}
        assert not params & {"held", "key", "keys"}, (name, params)
    single_key = {name for name, node in defs.items()
                  if {"api_key", "key"} & {a.arg for a in [
                      *node.args.args, *node.args.kwonlyargs]}}
    assert single_key == {"_key_patterns", "_key_spans",
                          "_refuse_unsendable_key",
                          "_call_inference_provider"}, single_key
    for node in pyast.walk(tree):
        if (isinstance(node, pyast.Call) and isinstance(node.func, pyast.Name)
                and node.func.id in REDACTIONS):
            (kw,) = [k for k in node.keywords if k.arg == "held"]
            assert isinstance(kw.value, pyast.Name), pyast.unparse(node)
            assert kw.value.id == "held", pyast.unparse(node)
    assert _calls_by_function("_held_keys") == {"host_inference_complete"}


# --- The cost of every rule over a provider's text, by its worst body -------
#
# The redaction reads text a provider chooses, up to the 64 KiB cap.  Each
# rule is a pattern or a scan over that text: the whole-key matcher, the
# per-character first-form matcher and the cut matcher (`_key_patterns`),
# the credential pattern, and the credential tail at a cut.  Each rule's
# worst body is built for the way it searches, and each redaction over it
# is held to a bound.  The rules are linear in the body (the key's own
# length bounds the work at each place), and a linear pass over 64 KiB takes
# a few milliseconds here; the bound is half a second, two orders above
# that, so a slow runner passes, and a quadratic rule, which takes seconds
# over 64 KiB, does not.

COST_BOUND_S = 0.5


def _bodies_worst_for_each_rule(key: str) -> dict[str, str]:
    n = _ERROR_BODY_CAP
    run = "x" * (n - 1)

    def fill(unit: str) -> str:
        return (unit * (n // len(unit) + 1))[:n]

    return {
        # the credential tail: a token's prefix at every place of one long
        # run that a character outside the run ends, so no place reaches
        # the end of the text
        "tail-prefixes-then-a-space": fill("key-") + " ",
        "tail-one-prefix-a-long-run": "sk-" + run[:n - 4] + " ",
        "tail-many-short-runs": fill("sk-ab "),
        # the credential pattern: prefixes with runs one short of a token
        "pattern-short-runs": fill("sk-abcdefg "),
        "pattern-prefix-chain": fill("sk_"),
        # the whole-key and first-form matchers: the key's prefix repeated,
        # its first character in every form
        "key-prefix-repeated": fill(key[:-1]),
        "key-first-char-forms": fill(f"\\u{ord(key[0]):04x}"),
        # the cut matcher: the key's leading characters, escaped, at the end
        "cut-escaped-prefix": fill("\\u00") + "".join(
            f"\\u{ord(c):04x}" for c in key[:-1]),
    }


@pytest.mark.parametrize("cut", [False, True], ids=["whole", "cut"])
@pytest.mark.parametrize("body", sorted(_bodies_worst_for_each_rule(KEY)))
def test_every_rule_is_linear_in_the_body(body: str, cut: bool) -> None:
    import time

    text = _bodies_worst_for_each_rule(KEY)[body]
    held = _largest_held_set()
    started = time.perf_counter()
    if cut:
        inference._redact_cut(text, held=held)
    else:
        inference._redact(text, held=held)
    assert time.perf_counter() - started < COST_BOUND_S, body


def _largest_held_set() -> inference.HeldKeys:
    """Every provider's key set, each a mixed-case variant of `KEY` (the
    key the worst bodies are built from, first among them), so the held
    set is two forms of each: the largest set the host can hold."""
    env = {cfg.env_key: (KEY if i == 0 else KEY[i:] + KEY[:i])
           for i, cfg in enumerate(inference._PROVIDERS.values())}
    held = inference._held_keys(env)
    assert len(held.keys) == 2 * len(inference._PROVIDERS), held
    return held


def test_repro_the_credential_tail_over_a_body_at_the_cap() -> None:
    """The fourth review's instance: `key-` repeated to the cap, then a
    space.  The tail search tried every start and ran each to the space."""
    import time

    text = ("key-" * (_ERROR_BODY_CAP // 4)) + " "
    started = time.perf_counter()
    assert inference._redact_cut(text, held=inference.HeldKeys(("",))) == text.replace(
        text[:-1], "[redacted]")
    assert time.perf_counter() - started < COST_BOUND_S


def test_repro_the_credential_tail_is_the_trailing_run_s_leftmost_token() -> None:
    """The tail is found in the run of token characters at the text's end,
    and from its leftmost prefix: what precedes the run is kept."""
    assert inference._redact_cut("a b-sk-key-12", held=inference.HeldKeys(("",))) == "a b-[redacted]"
    assert inference._redact_cut("a sk-12 b", held=inference.HeldKeys(("",))) == "a sk-12 b"
    assert inference._redact_cut("tokens", held=inference.HeldKeys(("",))) == "tokens"
    assert inference._redact_cut("x xai_", held=inference.HeldKeys(("",))) == "x [redacted]"


def test_repro_a_key_at_the_start_of_a_short_cut_text() -> None:
    """A cut text that is only the key's start: the cut rule tries the
    text's first place too."""
    assert inference._redact_cut("AB", held=inference.HeldKeys(("ABCD",))) == "[redacted]"


def test_repro_a_key_start_in_its_longest_forms_at_the_cut() -> None:
    """The cut rule looks back far enough for the key's leading characters
    each in its longest form, and a cut inside the next one's: `A` as a
    hex entity with six leading zeros, then `B`'s form cut short."""
    text = "&#x00000041;&#x00000042"
    assert inference._redact_cut(text, held=inference.HeldKeys(("AB",))) == "[redacted]"


def test_repro_a_held_key_s_control_character_as_a_hex_entity() -> None:
    """A held key may hold a line end (the key refusal's case, and the
    exit redacts the model name that repeats it): its line end in HTML's
    hex entity, one digit wide, is a form of it."""
    assert inference._redact("x k&#xA;y z", held=inference.HeldKeys(("k\ny",))) == "x [redacted] z"


def test_repro_the_exit_reads_a_whole_text() -> None:
    """The exit's text is whole: its end is not read as a key's start, and
    a token's start at its end is not a token."""
    assert inference._redact("x A", held=inference.HeldKeys(tuple(("AB",)))) == "x A"
    assert inference._redact("x sk-1", held=inference.HeldKeys(tuple(("AB",)))) == "x sk-1"
    assert inference._redact("sk-12345678 AB.", held=inference.HeldKeys(tuple(("AB",)))) == (
        "[redacted] [redacted].")


def test_repro_a_credential_tail_that_is_the_whole_text() -> None:
    assert inference._redact_cut("sk-1", held=inference.HeldKeys(("",))) == "[redacted]"
    assert inference._redact_cut("a-sk-1", held=inference.HeldKeys(("",))) == "a-[redacted]"


# --- Which held key a text carries, by where a cut falls in it --------------
#
# The host holds every provider's key that is set, the selected one and the
# others, and every redaction takes that one held set (`HeldKeys`), at the
# exit and at each cut.  A redaction that knew the selected key alone left
# the start of another held key wherever a cut split it: the exit matches
# a held key whole, and the cut matched only the selected one.  The matrix
# carries the selected key, an unselected held key, or both, on each route
# a text takes, with no cut, and across the 200-character cut and the
# 64 KiB cut with the key ending one character past the cut, half past,
# and all but one character past.

#: The selected key and another held key, built at run time from disjoint
#: alphabets so a surviving run is the key's own.
SELECTED = "".join(_RNG.choice("ABCDEFGHJKLMN") for _ in range(40))
UNSELECTED = "".join(_RNG.choice("pqrstuvwxyz") for _ in range(40))
CARRIED = {
    "selected": (SELECTED,),
    "unselected": (UNSELECTED,),
    "both": (SELECTED, UNSELECTED),
}


def _two_key_env() -> dict[str, str]:
    return {inference._PROVIDERS["anthropic"].env_key: SELECTED,
            inference._PROVIDERS["openai"].env_key: UNSELECTED,
            "VERA_INFERENCE_PROVIDER": "anthropic"}


def _carrying(which: str, before_cut: int | None, width: int,
              fill: str = "x", *, redacted_first: bool = True) -> str:
    """A text carrying the keys *which* names; with *before_cut*, the last
    key has that many characters before position *width* (a cut there),
    any other wholly before it.  The 200-character cut is made after the
    redaction (*redacted_first*), where a key before the last one already
    reads `[redacted]`; the 64 KiB cut is made on the bytes as read.
    *fill* leads up to them: spaces where the text is stripped after the
    cut (the 64 KiB cut), so the cut's head reaches the message."""
    keys = CARRIED[which]
    text = " ".join(keys)
    if before_cut is None:
        return "a " + text + " b"
    others = len(keys) - 1
    ahead = (others * (len("[redacted]") + 1) if redacted_first
             else len(text) - len(keys[-1]))
    lead = width - ahead - before_cut
    return fill * lead + text + " tail"


#: What the fallback writes before an exception's text, inside the 200
#: characters `_safe` keeps.
_EXCEPTION_PREFIX = "ValueError: "


SPLITS = {"one-past": 39, "half-past": 20, "all-but-one-past": 1}


def _cut_cells() -> Iterator[tuple[str, str, str, int | None]]:
    for which in CARRIED:
        for route in ("not-json", "http-error", "exception"):
            yield which, route, "no-cut", None
            for split, before in SPLITS.items():
                yield which, route, f"200-{split}", before
        for split, before in SPLITS.items():
            yield which, "http-error", f"64k-{split}", before


HELD_CUT_CELLS = [
    pytest.param(which, route, where, before,
                 id=f"{which}-{route}-{where}")
    for which, route, where, before in _cut_cells()
]


def _held_transport(route: str, where: str, text: str) -> MagicMock:
    if route == "exception":
        return MagicMock(side_effect=ValueError(text))
    if route == "http-error":
        return MagicMock(side_effect=_http_error(text.encode()))
    resp = MagicMock()
    resp.read.return_value = text.encode()
    resp.__enter__ = lambda s: s
    resp.__exit__ = MagicMock(return_value=False)
    return MagicMock(return_value=resp)


@pytest.mark.usefixtures("local_endpoints")
@pytest.mark.parametrize(("which", "route", "where", "before"), HELD_CUT_CELLS)
def test_every_held_key_at_every_cut(
    which: str, route: str, where: str, before: int | None,
) -> None:
    if where.startswith("64k"):
        text = _carrying(which, before, _ERROR_BODY_CAP, fill=" ",
                         redacted_first=False)
    else:
        width = 200 - (len(_EXCEPTION_PREFIX) if route == "exception" else 0)
        text = _carrying(which, before, width)
    with patch("urllib.request.urlopen", _held_transport(route, where, text)):
        ran = pipeline.run(_compile_ok(_SOURCE), env_vars=_two_key_env(),
                           capture_stderr=False)
    assert ran.ok, ran.trap
    assert ran.stdout, ran.stdout
    for key in CARRIED[which]:
        assert_no_part_of(key, ran.stdout)


@pytest.mark.usefixtures("local_endpoints")
def test_repro_an_unselected_held_key_split_by_each_cut() -> None:
    """The fifth review's instance: another provider's key, held, across
    the 200-character cut of a body that is not JSON, and across the
    64 KiB cut of an error body, left its first half in the `Err`."""
    for route, width, fill in (("not-json", 200, "x"),
                               ("http-error", _ERROR_BODY_CAP, " ")):
        text = _carrying("unselected", 20, width, fill,
                         redacted_first=width == 200)
        with patch("urllib.request.urlopen",
                   _held_transport(route, "cut", text)):
            ran = pipeline.run(_compile_ok(_SOURCE),
                               env_vars=_two_key_env(), capture_stderr=False)
        assert ran.ok, ran.trap
        assert_no_part_of(UNSELECTED, ran.stdout)
