"""#1333 — `Inference.complete` must parse provider responses by SHAPE, not by position.

The reported failure: `examples/inference.vera` printed `'text'` and exited 1
against the Anthropic flagship.  `_call_inference_provider` read the Anthropic
Messages response as `data["content"][0]["text"]`, and `claude-opus-5` returns
`content` as a list of *typed* blocks that can lead with a non-text (thinking)
block.  `content[0]` therefore had no `"text"` key, the `KeyError('text')`
reached the host boundary's blanket `except Exception`, and `str(exc)` — the
bare repr of the missing key — became the whole `Result::Err` payload.

Three properties are pinned here, one per defect:

1. **Selection by type.**  The Anthropic branch collects every `type == "text"`
   block in order and joins them, so a leading thinking block is skipped rather
   than mis-read.  The OpenAI-style branch is hardened the same way: a
   `message.content` may be a string (the common case), a list of typed parts,
   or `null` on a reasoning/tool-call turn — the last of which previously
   returned the *string* `"None"` as a successful completion.

2. **Named failures.**  Every shape failure, and every HTTP rejection, names
   the provider AND the model that answered.  The maintainer's provider sweep
   for this issue misattributed the failure to xAI, because with
   `VERA_INFERENCE_PROVIDER` unset auto-detect takes the first configured key
   in registry insertion order and a still-exported Anthropic key won the
   "xAI run".  An error that names its own provider makes that class of
   misreading impossible.

3. **No bare Python spelling at the boundary.**  Only an `InferenceError` —
   the module's own class, raised at every site that has something to say —
   passes through verbatim; everything else is labelled `Inference provider
   '<p>' failed: <Type>: <msg>`, so a future shape surprise can never again
   surface as `'text'`.  The rule was originally "a plain `RuntimeError` or
   `ValueError`, by exact type", which the PR review refuted: those are the
   types an unforeseen transport failure raises too, so `RuntimeError("boom")`
   from below claimed the verbatim channel and reached the user as `boom`.

The headline cells run END TO END — a real Vera program through `execute()`
with `urllib.request.urlopen` mocked — because that is the path the maintainer
hit; `_call_inference_provider` unit cells cover the shape matrix beneath it.
No test here touches the network.
"""
from __future__ import annotations

import ast
import email.message
import io
import json
import re
from pathlib import Path
import urllib.error
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from vera.codegen import execute
from vera.runtime.inference import (
    _ERROR_BODY_CAP,
    _ERROR_BODY_CHARS,
    _PROVIDERS,
    _call_inference_provider,
    InferenceError,
)

from tests.codegen_helpers import _compile_ok
from tests import pipeline


# =====================================================================
# Fixtures: response bodies and a mock transport
# =====================================================================

#: A Vera program that prints whichever side of the Result it gets and
#: reports which side that was.  Ok -> 0, Err -> 1, exactly like
#: examples/inference.vera, so `stdout` carries the completion or the
#: Err string verbatim and `value` says which branch produced it.
_CLASSIFY_SOURCE = """
public fn main(-> @Int)
  requires(true) ensures(true) effects(<Inference, IO>)
{
  let @Result<String, String> = Inference.complete("Is this positive?");
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


#: A boundary label wrapping a deliberate message.  ANCHORED at the start:
#: the label can only ever be a prefix, whereas the same shape occurring
#: anywhere in the string is ordinary provider text — a 502 body reading
#: `upstream (svc) failed: TimeoutError: deadline exceeded` is quoted
#: verbatim inside a perfectly deliberate message, and an unanchored search
#: called that a boundary label and failed the cell.
_BOUNDARY_LABEL_RE = re.compile(
    r"Inference provider '[^']*' \([^)]*\) failed: \w+(?:Error|Exception): "
)


def _assert_deliberate(text: str, prefix: str) -> None:
    """*text* is a deliberate message starting with *prefix*, NOT a wrapped one.

    A bare `startswith(prefix)` stopped discriminating the moment the
    boundary label gained the model.  Under the plain-type mutation the
    label reads `Inference provider 'anthropic' (claude-opus-5) failed:
    InferenceError: <the deliberate message>` — which satisfies the
    prefix check while BEING the regression the cell exists to catch,
    because the prefix is now a prefix of the label too.  Eleven cells
    lost their discrimination that way and nothing went red.

    The label's absence is therefore asserted alongside the prefix, and
    it lives in one helper so the next cell cannot forget it.
    """
    assert text.startswith(prefix), f"expected prefix {prefix!r}, got {text!r}"
    assert not _BOUNDARY_LABEL_RE.match(text), (
        f"a deliberate message was wrapped in a boundary label, which the "
        f"prefix check alone cannot see: {text!r}"
    )


def _mock_response_bytes(raw: bytes) -> MagicMock:
    """A transport whose body is raw bytes — for shapes a `str` cannot express."""
    resp = MagicMock()
    resp.read.return_value = raw
    resp.__enter__ = lambda s: s
    resp.__exit__ = MagicMock(return_value=False)
    return resp


def _mock_response(body: str) -> MagicMock:
    """A minimal stand-in for the object `urlopen` returns."""
    return _mock_response_bytes(body.encode("utf-8"))


def _http_error(code: int, body: str, *, url: str = "https://example.invalid") -> urllib.error.HTTPError:
    """An `HTTPError` shaped the way `urlopen` raises one, body included."""
    return urllib.error.HTTPError(
        url=url,
        code=code,
        msg="Unauthorized",
        hdrs=email.message.Message(),
        fp=io.BytesIO(body.encode("utf-8")),
    )


def _anthropic_body_with(extra: dict[str, Any], *blocks: dict[str, Any]) -> str:
    """An Anthropic response carrying *extra* top-level fields."""
    return json.dumps(
        {"id": "msg_1", "type": "message", "content": list(blocks), **extra},
    )


def _anthropic_body(*blocks: dict[str, Any]) -> str:
    return _anthropic_body_with({}, *blocks)


def _openai_body_with(
    content: Any, *, message: dict[str, Any] | None = None,
    choice: dict[str, Any] | None = None, omit_content: bool = False,
) -> str:
    """An OpenAI-style response with extra `message` / `choice` fields."""
    msg: dict[str, Any] = {"role": "assistant", **(message or {})}
    if not omit_content:
        msg["content"] = content
    return json.dumps({"id": "c1", "choices": [{"message": msg, **(choice or {})}]})


def _openai_body(content: Any) -> str:
    return _openai_body_with(content)


#: The thinking-block-first shape that broke the example.  The text block
#: is NOT first, so a by-position read lands on the thinking block.
_THINKING_FIRST = _anthropic_body(
    {"type": "thinking", "thinking": "The sentence is cheerful.", "signature": "sig"},
    {"type": "text", "text": "Positive"},
)


def _call(provider: str, body: str, model: str = "") -> str:
    """Drive `_call_inference_provider` with a mocked transport."""
    with patch("urllib.request.urlopen", MagicMock(return_value=_mock_response(body))):
        return _call_inference_provider(provider, "prompt", model, "sk-test")


def _call_raising(
    provider: str, exc: BaseException, model: str = "", key: str = "sk-test",
) -> str:
    """Drive the provider call over a transport that raises *exc*.

    *key* is the configured credential, which the redaction cells vary:
    the exact-match rule and the pattern rule have to be separable.
    """
    with patch("urllib.request.urlopen", MagicMock(side_effect=exc)):
        return _call_inference_provider(provider, "prompt", model, key)


def _run_with_transport(
    body: str | None = None,
    *,
    env: dict[str, str] | None = None,
    raises: BaseException | None = None,
) -> tuple[int | float | None, str]:
    """Compile and run `_CLASSIFY_SOURCE` end to end over a mocked transport.

    Returns `(exit value, stdout)` — 0/completion on the Ok branch,
    1/Err-string on the Err branch.
    """
    result = _compile_ok(_CLASSIFY_SOURCE)
    transport = (
        MagicMock(side_effect=raises)
        if raises is not None
        else MagicMock(return_value=_mock_response(body or ""))
    )
    with patch("urllib.request.urlopen", transport):
        exec_result = pipeline.run(result, env_vars=env if env is not None else {"VERA_ANTHROPIC_API_KEY": "sk-ant-test"}, capture_stderr=False).execution
    return exec_result.value, exec_result.stdout


# =====================================================================
# 1. Anthropic content blocks — selection by type
# =====================================================================


class TestAnthropicContentBlocks1333:
    """The Anthropic branch selects text blocks by `type`, not by index."""

    def test_thinking_block_first_yields_the_text_block(self) -> None:
        """THE REGRESSION: a leading thinking block is skipped, not read.

        Under the by-position parse this raised `KeyError('text')`.
        """
        assert _call("anthropic", _THINKING_FIRST) == "Positive"

    def test_single_text_block(self) -> None:
        """The common case — one text block — is unchanged."""
        body = _anthropic_body({"type": "text", "text": "Positive"})
        assert _call("anthropic", body) == "Positive"

    def test_two_text_blocks_are_joined_in_order(self) -> None:
        """Multiple text blocks concatenate in response order.

        The two fragments are asymmetric and separator-free, so a reversed
        join or an interposed newline both fail rather than coincide with
        the right answer.
        """
        body = _anthropic_body(
            {"type": "text", "text": "Positive"},
            {"type": "text", "text": " indeed"},
        )
        assert _call("anthropic", body) == "Positive indeed"

    def test_text_block_after_tool_use_is_still_found(self) -> None:
        """Selection scans the whole list, not just the first two entries."""
        body = _anthropic_body(
            {"type": "thinking", "thinking": "..."},
            {"type": "tool_use", "id": "t1", "name": "search", "input": {}},
            {"type": "text", "text": "Neutral"},
        )
        assert _call("anthropic", body) == "Neutral"

    #: `text` values that are NOT strings.  `str()` turned every one of
    #: these into a SUCCESSFUL completion: `null` became the string
    #: "None", a number became its digits, and an object became a Python
    #: repr — the #1333 leak class one level deeper than the
    #: `content: null` case closed alongside it.  The repr row is the
    #: sharpest: `"{'a': 1}"` is Python's own spelling reaching a Vera
    #: program as the model's answer.
    _NON_STRING_TEXT = (
        (None, "NoneType"),
        (123, "int"),
        ({"a": 1}, "dict"),
    )

    @pytest.mark.parametrize(
        ("value", "type_name"),
        _NON_STRING_TEXT,
        ids=[row[1] for row in _NON_STRING_TEXT],
    )
    def test_non_string_text_block_is_a_named_error(
        self, value: Any, type_name: str,
    ) -> None:
        """A selected block whose `text` is not a string is refused, not coerced.

        `pytest.raises` is the load-bearing half: the defect was that this
        RETURNED, so any completion at all fails the cell before a single
        assertion on the message runs.
        """
        body = _anthropic_body({"type": "text", "text": value})
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert f"whose text is {type_name}, not a string" in message

    def test_bad_text_block_refuses_even_when_a_good_one_follows(self) -> None:
        """The refusal wins over the salvageable remainder — deliberately.

        Skipping the malformed block and joining the rest would return a
        completion the provider never sent as a whole, and the caller
        could not tell it was short.  A response with a `null` text is
        evidence something went wrong upstream, so it is reported rather
        than partially honoured.
        """
        body = _anthropic_body(
            {"type": "text", "text": None},
            {"type": "text", "text": "Positive"},
        )
        with pytest.raises(InferenceError, match=r"whose text is NoneType"):
            _call("anthropic", body)

    def test_text_block_with_no_text_key_is_refused(self) -> None:
        """THE CONSISTENCY FIX: a key-less text block refuses like a null one.

        It was SKIPPED, which made two malformed shapes behave differently
        for no reason a caller could see — `{"text": null}` refused while
        `{}` fell through to whatever came next. Both are a provider
        failing to fill in a block it typed as text.
        """
        body = _anthropic_body({"type": "text"})
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "with no 'text' field" in message
        assert "anthropic" in message
        assert "claude-opus-5" in message

    def test_key_less_text_block_refuses_even_before_a_good_one(self) -> None:
        """THE REPORTED SHAPE: `[{"type":"text"}, {"type":"text","text":"P"}]`.

        This returned `Ok('Positive')` — the malformed block silently
        dropped and the response reported as whole. It is the exact
        counterpart of the null-text pair, which refused, and the two now
        agree.
        """
        body = _anthropic_body(
            {"type": "text"}, {"type": "text", "text": "Positive"},
        )
        with pytest.raises(InferenceError, match=r"with no 'text' field"):
            _call("anthropic", body)

    def test_key_less_text_block_refuses_after_a_good_one(self) -> None:
        """The mirror: a good block first does not license a broken one after."""
        body = _anthropic_body(
            {"type": "text", "text": "Neg"}, {"type": "text"},
        )
        with pytest.raises(InferenceError, match=r"with no 'text' field"):
            _call("anthropic", body)

    def test_content_wrong_type_says_so_instead_of_absent(self) -> None:
        """`{"content": "Positive"}` no longer contradicts itself.

        It read "no 'content' list in the response; response keys:
        content" — naming, as a key it had, the key it had just called
        missing. Absent and present-but-wrong-typed are different faults.
        """
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", json.dumps({"content": "Positive"}))
        message = str(excinfo.value)
        assert "'content' is str, not a list" in message
        assert "no 'content'" not in message

    def test_content_absent_still_reports_absent(self) -> None:
        """The paired positive: a genuinely missing key still reads as missing."""
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", json.dumps({"stop_reason": "end_turn"}))
        message = str(excinfo.value)
        assert "no 'content' list in the response" in message
        assert "response keys: stop_reason" in message

    def test_stop_reason_reported_on_the_content_shape_branch_too(self) -> None:
        """`{"content": null, "stop_reason": "end_turn"}` kept its stop_reason.

        The clause was on the no-text-block branch only, so the shape
        failure that most needs explaining dropped the one field that
        explained it.
        """
        body = json.dumps({"content": None, "stop_reason": "end_turn"})
        with pytest.raises(InferenceError, match=r"stop_reason=end_turn"):
            _call("anthropic", body)

    def test_no_text_block_names_provider_model_and_block_types(self) -> None:
        """A text-free response is an error that says whose it was."""
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "thinking" in message
        # Not the bare Python key that #1333 reported.
        assert message != "'text'"

    def test_no_text_block_reports_stop_reason_when_present(self) -> None:
        """`stop_reason` separates a truncated reply from a silent model.

        A thinking-only reply that exhausts the request's token budget —
        the runtime pins `max_tokens` at 1024 — is the likeliest producer
        of a text-free response, and it is a budget problem rather than a
        malformed provider.  Without the field the message reads the same
        either way and the reader cannot tell which they have.
        """
        body = _anthropic_body_with(
            {"stop_reason": "max_tokens"},
            {"type": "thinking", "thinking": "..."},
        )
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "stop_reason=max_tokens" in message
        # Alongside, not instead of, everything the message already carried.
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "thinking" in message

    def test_no_text_block_omits_stop_reason_when_absent(self) -> None:
        """A provider that sends no `stop_reason` gets a clean message.

        The paired negative: an unconditional clause would render
        `stop_reason=None`, which reads as a value the provider sent.
        """
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "stop_reason" not in message
        assert message.endswith("(content block types: thinking).")

    def test_stop_reason_rides_the_end_to_end_err(self) -> None:
        """The clause reaches the Vera-level `Err`, not just the helper."""
        body = _anthropic_body_with(
            {"stop_reason": "max_tokens"},
            {"type": "thinking", "thinking": "..."},
        )
        value, stdout = _run_with_transport(body)
        assert value == 1
        _assert_deliberate(stdout, "Inference provider 'anthropic' (claude-opus-5)")
        assert "stop_reason=max_tokens" in stdout

    def test_no_text_block_reports_the_model_actually_used(self) -> None:
        """`VERA_INFERENCE_MODEL`'s value, not the registry default, is named.

        A message that always prints the default would be actively
        misleading on exactly the runs where the model is the variable.
        """
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        with pytest.raises(InferenceError, match=r"claude-opus-4-6"):
            _call("anthropic", body, model="claude-opus-4-6")

    def test_content_missing_is_a_named_error(self) -> None:
        """A response with no `content` key fails with the same named shape."""
        body = json.dumps({"type": "error", "error": {"message": "overloaded"}})
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "content" in message

    def test_content_not_a_list_is_a_named_error(self) -> None:
        """`content` as a bare string (a shape no provider sends today)."""
        body = json.dumps({"content": "Positive"})
        with pytest.raises(InferenceError, match=r"anthropic.*claude-opus-5"):
            _call("anthropic", body)

    def test_empty_content_list_is_a_named_error(self) -> None:
        body = _anthropic_body()
        with pytest.raises(InferenceError, match=r"anthropic.*claude-opus-5"):
            _call("anthropic", body)


# =====================================================================
# 2. OpenAI-style message content — string, parts, or null
# =====================================================================


class TestOpenAiStyleContent1333:
    """The five OpenAI-style providers get the same by-shape hardening."""

    def test_string_content(self) -> None:
        """The common case — `content` is a string — is unchanged."""
        assert _call("openai", _openai_body("Positive")) == "Positive"

    def test_parts_list_is_joined_in_order(self) -> None:
        """A typed-parts `content` joins its text parts, skipping the rest."""
        body = _openai_body([
            {"type": "reasoning", "reasoning": "..."},
            {"type": "text", "text": "Positive"},
            {"type": "text", "text": " indeed"},
        ])
        assert _call("openai", body) == "Positive indeed"

    @pytest.mark.parametrize(
        ("value", "type_name"),
        TestAnthropicContentBlocks1333._NON_STRING_TEXT,
        ids=[row[1] for row in TestAnthropicContentBlocks1333._NON_STRING_TEXT],
    )
    def test_non_string_text_part_is_a_named_error(
        self, value: Any, type_name: str,
    ) -> None:
        """The parts list gets the same refusal as the Anthropic blocks.

        Both families share one extractor, and the table is shared with
        it rather than retyped, so a row added on one side cannot be
        forgotten on the other.
        """
        body = _openai_body([{"type": "text", "text": value}])
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert f"whose text is {type_name}, not a string" in message

    def test_text_part_with_no_text_key_is_refused(self) -> None:
        """The parts list gets the same consistency fix as the blocks."""
        body = _openai_body([
            {"type": "text", "text": "A"},
            {"type": "text"},
            {"type": "text", "text": "B"},
        ])
        with pytest.raises(InferenceError, match=r"text part with no 'text' field"):
            _call("openai", body)

    def test_output_text_is_accepted_as_a_part_discriminator(self) -> None:
        """Responses-API-shaped gateways spell a text part `output_text`.

        They worked on v0.1.12 because the old code read `content`
        positionally and never looked at `type` at all; selecting by type
        alone regressed them, which is a regression this PR introduced
        rather than one it inherited.
        """
        body = _openai_body([{"type": "output_text", "text": "Positive"}])
        assert _call("openai", body) == "Positive"

    def test_shim_emitting_both_spellings_is_not_doubled(self) -> None:
        """A gateway mirroring the SAME reply under both spellings.

        Scanning the union of the discriminators concatenated each
        fragment twice and returned `PositivePositive` — a wrong answer
        delivered as a success, which is this family's original defect
        wearing the fix's own clothes. Written with one part of each
        type carrying identical text, because that is the shim shape;
        a union bug is invisible when the two texts differ.
        """
        body = _openai_body([
            {"type": "text", "text": "Positive"},
            {"type": "output_text", "text": "Positive"},
        ])
        assert _call("openai", body) == "Positive"

    def test_text_parts_win_over_output_text_parts(self) -> None:
        """Preference, not union: `text` wins and `output_text` is not read.

        Distinct texts, so the assertion says WHICH spelling was taken
        rather than merely that the length came out right.
        """
        body = _openai_body([
            {"type": "output_text", "text": "FROM-OUTPUT-TEXT"},
            {"type": "text", "text": "FROM-TEXT"},
        ])
        assert _call("openai", body) == "FROM-TEXT"

    def test_output_text_parts_join_in_order_when_alone(self) -> None:
        """The fallback still joins its own parts, order preserved."""
        body = _openai_body([
            {"type": "output_text", "text": "Pos"},
            {"type": "output_text", "text": "itive"},
        ])
        assert _call("openai", body) == "Positive"

    def test_output_text_is_not_accepted_on_the_anthropic_branch(self) -> None:
        """Scoped deliberately: the Messages API has no `output_text` block.

        Accepting it there would invent a shape the provider does not
        send, and mask a genuinely malformed response.
        """
        body = _anthropic_body({"type": "output_text", "text": "Positive"})
        with pytest.raises(InferenceError, match=r"no text block"):
            _call("anthropic", body)

    def test_empty_string_completion_stays_ok_without_a_refusal(self) -> None:
        """An empty completion is a VALUE, and stays one.

        A model may legitimately answer with nothing, and `Ok("")` has
        been the behaviour since v0.1.12. The review wanted every empty
        completion routed to an error; that half is declined, because it
        is a behaviour change with nothing to do with #1333 and it would
        turn a valid reply into a failure.
        """
        assert _call("openai", _openai_body("")) == ""
        assert _call("openai", _openai_body("   ")) == "   "
        assert _call("openai", _openai_body([{"type": "text", "text": ""}])) == ""

    def test_empty_string_completion_with_a_refusal_surfaces_the_refusal(self) -> None:
        """…but an empty completion BESIDE a refusal discards the answer.

        `Ok("")` tells the caller the model said nothing, when in fact it
        said why it would not. This is the scoped half of the finding: the
        refusal's presence is what distinguishes the two, not emptiness.
        """
        body = _openai_body_with("", message={"refusal": "I can't help with that."})
        with pytest.raises(InferenceError, match=r"refused the request: I can't help"):
            _call("openai", body)

    def test_empty_parts_list_with_a_refusal_surfaces_the_refusal(self) -> None:
        """The list form of the same rule."""
        body = _openai_body_with(
            [{"type": "text", "text": ""}],
            message={"refusal": "I can't help with that."},
        )
        with pytest.raises(InferenceError, match=r"refused the request: I can't help"):
            _call("openai", body)

    def test_empty_text_part_does_not_shadow_a_real_output_text_part(self) -> None:
        """THE REGRESSION: an empty `text` part hid a real `output_text` one.

        `if parts: break` treated `[""]` as a hit, so the loop stopped on
        the empty `text` fragment and never read the `output_text` part
        carrying the answer — `Ok("")` where 8c7a6e5e returned
        `Ok("Positive")`. Both orders, because the list order is the
        provider's to choose.
        """
        first = _openai_body([
            {"type": "text", "text": ""},
            {"type": "output_text", "text": "Positive"},
        ])
        second = _openai_body([
            {"type": "output_text", "text": "Positive"},
            {"type": "text", "text": ""},
        ])
        assert _call("openai", first) == "Positive"
        assert _call("openai", second) == "Positive"

    def test_malformed_part_under_the_unread_discriminator_is_not_reached(self) -> None:
        """Preference decides BEFORE the other discriminator is validated.

        `text` yields the answer, so the `output_text` part is never
        scanned and its missing `text` field never raises — which is the
        difference between preference and a union: scanning both would
        refuse a response the provider filled in correctly under the
        spelling we prefer. The mirror shows the same rule biting when the
        malformed part IS the one selected.
        """
        preferred_wins = _openai_body([
            {"type": "text", "text": "Positive"},
            {"type": "output_text"},
        ])
        assert _call("openai", preferred_wins) == "Positive"

        malformed_is_selected = _openai_body([
            {"type": "text"},
            {"type": "output_text", "text": "Positive"},
        ])
        with pytest.raises(
            InferenceError, match=r"text part with no 'text' field",
        ):
            _call("openai", malformed_is_selected)

    #: Blank fragments a shim plausibly emits.  `""` alone was the round-9
    #: fixture and passed while `"   "` and `"\n"` did not: the hit test
    #: was truthiness where the blank test downstream was `.strip()`, so a
    #: whitespace-only part counted as an answer.
    _BLANK_FRAGMENTS = ("", "   ", "\n")

    @pytest.mark.parametrize("blank", _BLANK_FRAGMENTS, ids=["empty", "spaces", "newline"])
    def test_blank_text_part_does_not_shadow_a_real_output_text_part(
        self, blank: str,
    ) -> None:
        """A BLANK `text` part, of any spelling, must not hide the answer.

        Truthiness let `"   "` short-circuit the loop and return itself,
        losing the `output_text` part carrying the completion. Both
        orders, since the list order is the provider's to choose.
        """
        first = _openai_body([
            {"type": "text", "text": blank},
            {"type": "output_text", "text": "Positive"},
        ])
        second = _openai_body([
            {"type": "output_text", "text": "Positive"},
            {"type": "text", "text": blank},
        ])
        assert _call("openai", first) == "Positive"
        assert _call("openai", second) == "Positive"

    @pytest.mark.parametrize("blank", _BLANK_FRAGMENTS, ids=["empty", "spaces", "newline"])
    def test_blank_parts_list_with_a_refusal_matches_the_string_form(
        self, blank: str,
    ) -> None:
        """The list form applies the refusal rule the string form applied.

        Round 9 claimed both forms; it held for the list form only when
        the fragment was exactly `""`. `"   "` returned `Ok("   ")` and
        discarded the refusal, while `content: "   "` with the same
        refusal raised — an asymmetry with no reason a caller could see.
        """
        body = _openai_body_with(
            [{"type": "text", "text": blank}],
            message={"refusal": "I decline."},
        )
        with pytest.raises(InferenceError, match=r"refused the request: I decline\."):
            _call("openai", body)
        # The string form, same input, same outcome — the point of the cell.
        string_form = _openai_body_with(blank, message={"refusal": "I decline."})
        with pytest.raises(InferenceError, match=r"refused the request: I decline\."):
            _call("openai", string_form)

    @pytest.mark.parametrize("blank", _BLANK_FRAGMENTS, ids=["empty", "spaces", "newline"])
    def test_blank_completion_without_a_reason_is_returned_unchanged(
        self, blank: str,
    ) -> None:
        """The paired negative: no refusal, no truncation, so it is a value."""
        assert _call("openai", _openai_body([{"type": "text", "text": blank}])) == blank
        assert _call("openai", _openai_body(blank)) == blank

    def test_all_empty_fragments_remain_an_empty_completion(self) -> None:
        """The paired negative: nothing to prefer means the answer is "".

        Distinguishes "an empty fragment is not a hit" from "an empty
        result is an error" — only the first is intended.
        """
        body = _openai_body([
            {"type": "text", "text": ""},
            {"type": "output_text", "text": ""},
        ])
        assert _call("openai", body) == ""

    def test_refusal_text_is_surfaced(self) -> None:
        """A refusal turn explains itself instead of describing null content.

        `message.refusal` is the answer; the shape of the empty `content`
        beside it is the symptom.
        """
        body = _openai_body_with(None, message={"refusal": "I can't help with that."})
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "refused the request: I can't help with that." in message
        assert "openai" in message
        assert "gpt-5.6-sol" in message

    def test_refusal_is_truncated_and_redacted(self) -> None:
        """Refusal text is provider-supplied like any other — bounded, cleaned."""
        body = _openai_body_with(
            None,
            message={"refusal": "no: sk-live-SECRETKEY123456 " + "q" * 5000},
        )
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert len(message) < 500
        assert "sk-live-SECRETKEY123456" not in message
        assert "[redacted]" in message

    def test_missing_message_names_the_choice_not_the_response(self) -> None:
        """`{"choices":[{"finish_reason":"length"}]}` reads coherently now.

        It said "message content is NoneType; message keys: (not an
        object: NoneType)" — describing a message that was not there at
        all, and listing the keys of nothing.
        """
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", json.dumps({"choices": [{"finish_reason": "length"}]}))
        message = str(excinfo.value)
        assert "no 'message' object in the choice" in message
        assert "choice keys: finish_reason" in message
        assert "(not an object: NoneType)" not in message

    def test_finish_reason_is_reported(self) -> None:
        """The OpenAI-style analogue of `stop_reason`, read off the choice."""
        body = _openai_body_with(None, choice={"finish_reason": "length"})
        with pytest.raises(InferenceError, match=r"finish_reason=length"):
            _call("openai", body)

    def test_null_content_is_a_named_error(self) -> None:
        """A reasoning/tool-call turn with `content: null`.

        Previously this returned the *string* `"None"` as a successful
        completion — a silent wrong answer, not merely a bad message.
        """
        body = _openai_body(None)
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert message != "None"

    def test_parts_list_without_text_parts_is_a_named_error(self) -> None:
        """The OpenAI half of the no-selected-type rule, in full.

        Spec 9.5.5 promises this `Err` names the part types present AND
        the provider's reason. Only the types half was asserted, so
        neutralising `finish` never reddened this cell — the promise held
        on the Anthropic branch and was untested here.
        """
        body = _openai_body_with(
            [{"type": "reasoning", "reasoning": "..."}],
            choice={"finish_reason": "length"},
        )
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert "part types: reasoning" in message
        assert "finish_reason=length" in message

    def test_empty_parts_list_names_no_types_and_the_reason(self) -> None:
        """`content: []` — no parts at all, as distinct from no CHOICES.

        The empty-list shape had no cell on this branch;
        `test_empty_choices_is_a_named_error` covers an empty `choices`,
        which is a different failure one level up.
        """
        body = _openai_body_with([], choice={"finish_reason": "content_filter"})
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert "part types: (none)" in message
        assert "finish_reason=content_filter" in message

    def test_missing_choices_is_a_named_error(self) -> None:
        body = json.dumps({"error": {"message": "model not found"}})
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert "choices" in message

    def test_empty_choices_is_a_named_error(self) -> None:
        body = json.dumps({"choices": []})
        with pytest.raises(InferenceError, match=r"openai.*gpt-5\.6-sol"):
            _call("openai", body)

    def test_missing_message_is_a_named_error(self) -> None:
        body = json.dumps({"choices": [{"finish_reason": "length"}]})
        with pytest.raises(InferenceError, match=r"openai.*gpt-5\.6-sol"):
            _call("openai", body)


# =====================================================================
# 3. HTTP rejections and non-JSON bodies
# =====================================================================


class TestHttpRejectionMessages1333:
    """`urlopen` raising `HTTPError` must not escape as `HTTP Error 401: …`."""

    def test_anthropic_error_body_message_is_surfaced(self) -> None:
        """Anthropic's `{"error": {"message": …}}` body is read and quoted."""
        body = json.dumps({
            "type": "error",
            "error": {"type": "authentication_error", "message": "invalid x-api-key"},
        })
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(401, body))
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "401" in message
        assert "invalid x-api-key" in message
        # The raw urllib spelling must not be what the user sees.
        assert message != "HTTP Error 401: Unauthorized"

    def test_openai_style_error_body_message_is_surfaced(self) -> None:
        """The OpenAI-shaped error body uses the same `error.message` path."""
        body = json.dumps({
            "error": {
                "message": "Incorrect API key provided: sk-xxx.",
                "type": "invalid_request_error",
                "code": "invalid_api_key",
            },
        })
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("openai", _http_error(401, body))
        message = str(excinfo.value)
        assert "openai" in message
        assert "gpt-5.6-sol" in message
        assert "401" in message
        assert "Incorrect API key provided" in message

    def test_non_json_error_body_falls_back_to_raw_text(self) -> None:
        """An HTML error page from a proxy still yields a named message."""
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(502, "<html>Bad Gateway</html>"))
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "502" in message
        assert "Bad Gateway" in message

    def test_long_error_body_is_truncated(self) -> None:
        """A megabyte of proxy HTML does not become the Err string."""
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(500, "x" * 5000))
        message = str(excinfo.value)
        assert len(message) < 500
        assert "500" in message

    def test_error_body_read_is_bounded(self) -> None:
        """The read asks for a SIZE — the body is never pulled in whole.

        The pre-existing oversized-body cell bounds the MESSAGE, which a
        bare `read()` satisfies too: it reads megabytes and then truncates
        to 200 characters. Only the call's argument distinguishes "bounded
        output" from "bounded memory", so it is asserted directly.
        """
        recorded: list[tuple[object, ...]] = []
        err = _http_error(502, "x" * 100)

        def _recording_read(*args: object) -> bytes:
            recorded.append(args)
            return b"x" * 100

        err.read = _recording_read  # type: ignore[method-assign]
        with pytest.raises(InferenceError):
            _call_raising("anthropic", err)
        assert recorded, "the error body was never read at all"
        assert len(recorded[0]) == 1, (
            f"read() was called with no size argument ({recorded[0]!r}) — the "
            f"whole body lands in memory before any truncation"
        )
        # One byte past the cap, so an exact-cap body stays distinguishable
        # from one that overran.
        assert recorded[0][0] == _ERROR_BODY_CAP + 1

    def test_oversized_error_body_is_bounded_and_marked(self) -> None:
        """A body past the cap yields a short, marked, still-named message."""
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(502, "x" * (_ERROR_BODY_CAP + 1000)))
        message = str(excinfo.value)
        assert len(message) < 500
        assert "(truncated)" in message
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "502" in message

    def test_overrun_body_is_never_presented_as_parsed(self) -> None:
        """An overrun body is reported raw — we do not claim to have parsed it.

        The discriminating shape, and it took finding: a body cut
        mid-structure is rejected by `json.loads` anyway, so almost any
        oversized input reaches the raw-text path with or without the
        overrun branch. Trailing WHITESPACE is the exception — `json.loads`
        accepts it — so a short envelope padded past the cap is the one
        input where "we read only part of it" and "we parsed what we read"
        disagree. Here the message must NOT be surfaced, because we did not
        see the whole body and cannot know the padding was all there was.

        This is why the branch is written explicitly rather than left to
        `json.loads` rejecting fragments: that is a property of today's
        parser, and a later switch to `raw_decode` — which parses a prefix
        happily — would silently start presenting fragments as complete.
        """
        payload = json.dumps({"error": {"message": "invalid x-api-key"}})
        payload += " " * (_ERROR_BODY_CAP + 500 - len(payload))
        assert len(payload.encode("utf-8")) > _ERROR_BODY_CAP
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(500, payload))
        message = str(excinfo.value)
        # The raw text CONTAINS the message — it is the body — so presence
        # of the phrase proves nothing either way. What separates the two
        # paths is the envelope: the parsed path yields the bare message,
        # the raw path yields the JSON around it.
        assert '{"error"' in message, (
            "an overrun body was parsed and its message surfaced bare, as "
            "though the whole body had been read"
        )
        assert "(truncated)" in message
        assert len(message) < 500

    def test_error_body_under_the_cap_is_still_parsed(self) -> None:
        """The cap does not cost the ordinary case its parsed message.

        Sits just under the boundary rather than at a token size, so a cap
        applied off-by-one — or applied to the wrong side of the
        comparison — fails here instead of passing on a tiny body.
        """
        filler = "z" * (_ERROR_BODY_CAP - 200)
        body = json.dumps({"error": {"message": f"invalid x-api-key {filler}"}})
        assert len(body.encode("utf-8")) < _ERROR_BODY_CAP
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(401, body))
        message = str(excinfo.value)
        assert "invalid x-api-key" in message
        assert "(truncated)" in message  # the MESSAGE bound, not the read cap

    def test_missing_body_keeps_the_empty_fallback(self) -> None:
        """An `HTTPError` carrying no stream reports the documented phrase."""
        err = _http_error(503, "")
        err.fp = None  # type: ignore[assignment]
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", err)
        message = str(excinfo.value)
        assert "(empty response body)" in message
        assert "503" in message
        assert "anthropic" in message

    def test_unreadable_body_still_names_provider_and_code(self) -> None:
        """A read that RAISES must not cost us the status line.

        Reachable, not hypothetical: a stream already closed under us —
        which is what a dropped connection looks like at this point —
        raises `ValueError` from `read`. Losing the detail is a far
        smaller loss than replacing a described rejection with an
        unrelated exception.
        """
        closed = io.BytesIO(b"never read")
        closed.close()
        err = _http_error(502, "")
        err.fp = closed  # type: ignore[assignment]
        err.read = closed.read  # type: ignore[method-assign]
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", err)
        message = str(excinfo.value)
        assert "(unreadable response body)" in message
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "502" in message

    def test_non_json_success_body_is_a_named_error(self) -> None:
        """A 200 whose body is not JSON names the provider too.

        Without this the `json.JSONDecodeError` (a `ValueError` subclass)
        would reach the boundary and — under an `isinstance` pass-through —
        surface as the bare `Expecting value: line 1 column 1 (char 0)`.
        """
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", "<html>gateway timeout</html>")
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "claude-opus-5" in message
        assert "Expecting value" not in message

    def test_non_utf8_success_body_is_a_named_error(self) -> None:
        """A 200 whose body is not valid UTF-8 names the provider and the byte.

        The #591 handler is guarded in `tests/test_runtime_traps.py` by a
        SOURCE regex, which proves the `except UnicodeDecodeError` block
        exists but can say nothing about what it produces — and #1333 moved
        that decode inside a new outer `try` / `except HTTPError`, so the
        behaviour is pinned here as well.  A strict `.decode("utf-8")`
        published the raw codec text — byte offsets and Python-internals
        jargon — as the whole Err string.
        """
        # The bad bytes sit mid-body, so the reported position is a real
        # offset rather than the 0 a truncated or empty body would also give.
        with patch(
            "urllib.request.urlopen",
            MagicMock(return_value=_mock_response_bytes(b"hello \xff\xfe world")),
        ), pytest.raises(InferenceError) as excinfo:
            _call_inference_provider("anthropic", "prompt", "", "sk-test")
        message = str(excinfo.value)
        assert "anthropic" in message
        assert "not valid UTF-8" in message
        assert "position 6" in message  # len(b"hello ") — the first bad byte
        # The #591 property proper: none of Python's own codec spelling
        # survives into a value a Vera program can print or match on.  These
        # two guard a different regression from the assertions above — a
        # bare strict decode fails this cell at `pytest.raises`, before any
        # message is read, whereas a handler that keeps the catch and
        # interpolates the exception (`RuntimeError(f"... {ude}")`) would
        # satisfy every positive assertion and re-leak the codec text.
        assert "codec can't decode" not in message
        assert "invalid start byte" not in message


# =====================================================================
# 4. The host boundary — end to end, the path the maintainer hit
# =====================================================================


class TestInferenceBoundaryEndToEnd1333:
    """`vera run` over a mocked transport: the product path, not the helper."""

    def test_thinking_first_prints_the_completion(self) -> None:
        """THE REGRESSION, end to end: the example's shape now succeeds.

        Before the fix this printed `'text'` and returned 1.
        """
        value, stdout = _run_with_transport(_THINKING_FIRST)
        assert value == 0
        assert stdout == "Positive"

    def test_no_text_block_err_names_provider_and_model(self) -> None:
        """The Err string is self-diagnosing, and is never the bare key."""
        body = _anthropic_body({"type": "thinking", "thinking": "..."})
        value, stdout = _run_with_transport(body)
        assert value == 1
        assert stdout != "'text'"
        _assert_deliberate(stdout, "Inference provider 'anthropic' (claude-opus-5)")
        assert "thinking" in stdout

    def test_non_string_text_block_err_reaches_the_program(self) -> None:
        """End to end: `text: null` is an Err, never `Ok("None")`.

        The unit cells prove the extractor refuses; this proves the
        refusal survives to the value a Vera program matches on — which
        is where the silent wrong answer would have been observed.
        """
        body = _anthropic_body({"type": "text", "text": None})
        value, stdout = _run_with_transport(body)
        assert value == 1
        assert stdout != "None"
        assert stdout == (
            "Inference provider 'anthropic' (claude-opus-5) returned a "
            "text block whose text is NoneType, not a string."
        )

    def test_http_rejection_err_names_provider_and_code(self) -> None:
        body = json.dumps({"error": {"message": "invalid x-api-key"}})
        value, stdout = _run_with_transport(raises=_http_error(401, body))
        assert value == 1
        _assert_deliberate(stdout, "Inference provider 'anthropic' (claude-opus-5)")
        assert "401" in stdout
        assert "invalid x-api-key" in stdout

    #: Exception types that must NOT reach the user as their own bare
    #: message.  `RuntimeError` and `ValueError` are the load-bearing pair:
    #: the boundary used to test for exactly those two, so each of them
    #: claimed the verbatim channel while carrying a message written for
    #: nobody.  `JSONDecodeError` is the third because it is a `ValueError`
    #: SUBCLASS, which is what made the exact-type test necessary before a
    #: dedicated class made the question moot.
    _UNFORESEEN = (
        (RuntimeError("boom"), "RuntimeError", "boom"),
        (ValueError("boom"), "ValueError", "boom"),
        (KeyError("text"), "KeyError", "'text'"),
        (
            json.JSONDecodeError("Expecting value", "<html>", 0),
            "JSONDecodeError",
            "Expecting value",
        ),
    )

    @pytest.mark.parametrize(
        ("exc", "type_name", "fragment"),
        _UNFORESEEN,
        ids=[row[1] for row in _UNFORESEEN],
    )
    def test_unforeseen_exception_is_labelled_with_its_type(
        self, exc: BaseException, type_name: str, fragment: str,
    ) -> None:
        """Anything that is not an `InferenceError` is labelled, whatever its type.

        THE PR-REVIEW FINDING, in the `RuntimeError`/`ValueError` rows: the
        boundary's old rule handed the verbatim channel to those two types
        by name, so a `RuntimeError("boom")` raised anywhere below us — the
        transport, a dependency, a future edit — surfaced as the single word
        `boom`.  That is #1333's own defect one level up, and it is why the
        rule is now a dedicated class nothing else can raise by accident.

        `_call_inference_provider` is patched rather than driven through a
        response shape, so this measures the boundary's formatting and not a
        parse that no longer fails.
        """
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider", side_effect=exc,
        ):
            exec_result = execute(
                result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
            )
        assert exec_result.value == 1
        assert exec_result.stdout.startswith(
            f"Inference provider 'anthropic' (claude-opus-5) failed: "
            f"{type_name}: "
        )
        assert fragment in exec_result.stdout
        # The whole point: the exception's own spelling is never the whole
        # message.  `!= fragment` is the assertion the old rule failed.
        assert exec_result.stdout != fragment

    def test_provider_text_quoting_a_failure_is_still_deliberate(self) -> None:
        """A 502 body may contain the label's own shape — anywhere but the front.

        `upstream (svc) failed: TimeoutError: deadline exceeded` is
        ordinary provider text, and an UNANCHORED label search called the
        deliberate message that quotes it a wrapped one, failing a cell
        for a message that was never wrapped. The label can only be a
        prefix, so the check is anchored.
        """
        body = json.dumps({"error": {"message":
            "upstream (svc) failed: TimeoutError: deadline exceeded"}})
        value, stdout = _run_with_transport(raises=_http_error(502, body))
        assert value == 1
        assert "failed: TimeoutError: deadline exceeded" in stdout
        _assert_deliberate(stdout, "Inference provider 'anthropic' (claude-opus-5)")

    def test_deliberate_inference_error_passes_through_verbatim(self) -> None:
        """An `InferenceError` is a message written for a user — unlabelled."""
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=InferenceError("Inference provider 'anthropic' (m) says so."),
        ):
            exec_result = execute(
                result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
            )
        assert exec_result.value == 1
        assert exec_result.stdout == "Inference provider 'anthropic' (m) says so."

    def test_inference_error_is_a_runtime_error_but_not_a_value_error(self) -> None:
        """The class's shape, pinned where the reasoning for it lives.

        `RuntimeError` keeps `except RuntimeError` callers working.  NOT
        also `ValueError`, deliberately: this module wraps `json.loads` in
        `except ValueError` twice, and a subclass of both would let a future
        edit that moved a deliberate raise inside one of those blocks be
        swallowed by its own handler, with no test able to see it.
        """
        assert issubclass(InferenceError, RuntimeError)
        assert not issubclass(InferenceError, ValueError)

    def test_unknown_provider_error_passes_through_verbatim(self) -> None:
        """The registry's own refusal keeps its wording and its list."""
        value, stdout = _run_with_transport(
            _THINKING_FIRST,
            env={
                "VERA_INFERENCE_PROVIDER": "nope",
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
            },
        )
        assert value == 1
        _assert_deliberate(stdout, "Unknown inference provider 'nope'.")

    def test_json_decode_failure_is_named_not_python_spelled(self) -> None:
        """A `JSONDecodeError` is a `ValueError` *subclass* — it must not
        take the verbatim pass-through an `isinstance` check would grant."""
        value, stdout = _run_with_transport("<html>gateway timeout</html>")
        assert value == 1
        _assert_deliberate(stdout, "Inference provider 'anthropic' (claude-opus-5)")
        assert "Expecting value" not in stdout


# =====================================================================
# 5. The provider sweep, as a regression
# =====================================================================


# =====================================================================
# An empty completion the provider itself explained
# =====================================================================


class TestEmptyCompletionWithAReason1333:
    """`Ok("")` is right until the provider says why the answer is empty.

    Round 9 closed this on the OpenAI branch for `message.refusal` only.
    The Anthropic branch had no such rule at all: a response whose sole
    text block was `""` under `stop_reason: "refusal"` came back as a
    successful empty completion with the reason discarded — and under
    `max_tokens`, which is #1333's own species, a thinking block having
    eaten the budget before any text was emitted.

    The rule is symmetric and narrow. An EMPTY (or whitespace-only)
    completion is an error when the provider marked the turn a refusal or
    a truncation; under `end_turn` / `stop` / no reason at all it stays
    `Ok("")`, and a NON-empty reply under `max_tokens` / `length` is
    returned unchanged, truncated-but-present output still being the
    model's answer.
    """

    #: (label, provider, body, expected reason token in the message)
    _FAILING = (
        ("anthropic refusal", "anthropic",
         _anthropic_body_with({"stop_reason": "refusal"},
                              {"type": "text", "text": ""}),
         "stop_reason=refusal"),
        ("anthropic refusal, whitespace", "anthropic",
         _anthropic_body_with({"stop_reason": "refusal"},
                              {"type": "text", "text": "   "}),
         "stop_reason=refusal"),
        ("anthropic max_tokens", "anthropic",
         _anthropic_body_with({"stop_reason": "max_tokens"},
                              {"type": "text", "text": ""}),
         "stop_reason=max_tokens"),
        ("anthropic max_tokens, whitespace", "anthropic",
         _anthropic_body_with({"stop_reason": "max_tokens"},
                              {"type": "text", "text": " \n "}),
         "stop_reason=max_tokens"),
        ("openai length, string", "openai",
         _openai_body_with("", choice={"finish_reason": "length"}),
         "finish_reason=length"),
        ("openai length, whitespace string", "openai",
         _openai_body_with("   ", choice={"finish_reason": "length"}),
         "finish_reason=length"),
        ("openai length, parts list", "openai",
         _openai_body_with([{"type": "text", "text": ""}],
                           choice={"finish_reason": "length"}),
         "finish_reason=length"),
    )

    @pytest.mark.parametrize(
        ("label", "provider", "body", "token"),
        _FAILING,
        ids=[row[0] for row in _FAILING],
    )
    def test_empty_completion_with_a_reason_is_an_error(
        self, label: str, provider: str, body: str, token: str,
    ) -> None:
        """The Err names the provider, the model, and the reason token.

        The literal `stop_reason=refusal` / `finish_reason=length` is
        asserted rather than merely "some reason": it is the token a
        downstream consumer greps for to tell a refusal from a truncation
        from an ordinary failure.
        """
        with pytest.raises(InferenceError) as excinfo:
            _call(provider, body)
        message = str(excinfo.value)
        assert "returned an empty completion" in message
        assert token in message
        assert _PROVIDERS[provider].default_model in message
        assert provider in message

    #: The same shapes under a reason that does NOT explain emptiness, and
    #: the non-empty counterparts. These are the cells that keep the rule
    #: narrow — without them "empty is an error" would pass just as well.
    _UNCHANGED = (
        ("anthropic end_turn empty", "anthropic",
         _anthropic_body_with({"stop_reason": "end_turn"},
                              {"type": "text", "text": ""}), ""),
        ("anthropic no reason empty", "anthropic",
         _anthropic_body({"type": "text", "text": ""}), ""),
        ("anthropic max_tokens non-empty", "anthropic",
         _anthropic_body_with({"stop_reason": "max_tokens"},
                              {"type": "text", "text": "Yes"}), "Yes"),
        ("anthropic end_turn whitespace", "anthropic",
         _anthropic_body_with({"stop_reason": "end_turn"},
                              {"type": "text", "text": "   "}), "   "),
        ("openai stop empty", "openai",
         _openai_body_with("", choice={"finish_reason": "stop"}), ""),
        ("openai no reason empty", "openai", _openai_body(""), ""),
        ("openai length non-empty", "openai",
         _openai_body_with("Yes", choice={"finish_reason": "length"}), "Yes"),
        ("openai stop, empty parts list", "openai",
         _openai_body_with([{"type": "text", "text": ""}],
                           choice={"finish_reason": "stop"}), ""),
    )

    #: The same reasons in spellings a gateway might normalise to.  Every
    #: registered provider emits these lowercase today, so this is
    #: hardening rather than a reported failure — but an exact match sent
    #: `MAX_TOKENS` straight to `Ok("")`, losing the answer over a
    #: spelling difference.
    _CASE_VARIANTS = (
        ("anthropic MAX_TOKENS", "anthropic",
         _anthropic_body_with({"stop_reason": "MAX_TOKENS"},
                              {"type": "text", "text": ""}),
         "stop_reason=MAX_TOKENS"),
        ("anthropic Refusal", "anthropic",
         _anthropic_body_with({"stop_reason": "Refusal"},
                              {"type": "text", "text": ""}),
         "stop_reason=Refusal"),
        ("openai Length", "openai",
         _openai_body_with("", choice={"finish_reason": "Length"}),
         "finish_reason=Length"),
    )

    @pytest.mark.parametrize(
        ("label", "provider", "body", "token"),
        _CASE_VARIANTS,
        ids=[row[0] for row in _CASE_VARIANTS],
    )
    def test_the_reason_is_matched_case_insensitively(
        self, label: str, provider: str, body: str, token: str,
    ) -> None:
        """The comparison folds case; the rendered token does not.

        Both halves matter. Folding only the comparison keeps the
        diagnostic honest about what the provider actually sent, which is
        the whole point of quoting the token — a consumer grepping for
        `max_tokens` should not be told the provider said that when it
        said `MAX_TOKENS`.
        """
        with pytest.raises(InferenceError) as excinfo:
            _call(provider, body)
        message = str(excinfo.value)
        assert "returned an empty completion" in message
        assert token in message, (
            f"the token must be rendered as received, not normalised: "
            f"expected {token!r} in {message!r}"
        )

    def test_case_folding_does_not_widen_the_reason_set(self) -> None:
        """The paired negative: folding case must not admit other reasons.

        `End_Turn` and `Stop` differ from the failing set in more than
        case, so they stay `Ok("")` — otherwise "case-insensitive" would
        have quietly become "any reason at all".
        """
        assert _call("anthropic", _anthropic_body_with(
            {"stop_reason": "End_Turn"}, {"type": "text", "text": ""},
        )) == ""
        assert _call("openai", _openai_body_with(
            "", choice={"finish_reason": "Stop"},
        )) == ""
        # And a non-empty reply under a folded failing reason is untouched.
        assert _call("anthropic", _anthropic_body_with(
            {"stop_reason": "MAX_TOKENS"}, {"type": "text", "text": "Yes"},
        )) == "Yes"

    @pytest.mark.parametrize(
        ("label", "provider", "body", "expected"),
        _UNCHANGED,
        ids=[row[0] for row in _UNCHANGED],
    )
    def test_everything_else_is_returned_unchanged(
        self, label: str, provider: str, body: str, expected: str,
    ) -> None:
        """Exactly as v0.1.12 returned it."""
        assert _call(provider, body) == expected


# =====================================================================
# Every message is bounded, whatever the provider sends
# =====================================================================


class TestMessageBounds1333:
    """No provider-supplied value reaches a Vera `Err` at its own size.

    The 200-character bound lived on the error-BODY path only. Every
    field interpolated into a shape message — `stop_reason`, the block
    types, the response keys — bypassed it, so a 64 MB `stop_reason`
    produced a 67 MB `Err` string: a value the Vera program then holds,
    prints and may concatenate.
    """

    #: Deliberately megabytes rather than kilobytes. A bound that clips
    #: at some larger figure would pass a 20,000-character assertion.
    _HUGE = "z" * (4 * 1024 * 1024)

    def _err(self, body: str) -> str:
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", body)
        return str(excinfo.value)

    def test_huge_stop_reason_is_bounded(self) -> None:
        message = self._err(
            _anthropic_body_with(
                {"stop_reason": self._HUGE}, {"type": "thinking"},
            ),
        )
        assert len(message) < 1000
        assert "stop_reason=zzz" in message
        assert "(truncated)" in message

    def test_huge_finish_reason_is_bounded(self) -> None:
        body = _openai_body_with(None, choice={"finish_reason": self._HUGE})
        with pytest.raises(InferenceError) as excinfo:
            _call("openai", body)
        assert len(str(excinfo.value)) < 1000

    def test_many_block_types_are_bounded(self) -> None:
        """3,000 distinct types was a ~20,000-character message."""
        blocks = [{"type": f"kind{i}"} for i in range(3000)]
        assert len(self._err(_anthropic_body(*blocks))) < 1000

    def test_many_response_keys_are_bounded(self) -> None:
        """The key list is attacker-shaped too."""
        assert len(self._err(json.dumps({f"k{i}": 1 for i in range(3000)}))) < 1000

    def test_huge_text_block_type_is_bounded(self) -> None:
        """A single enormous `type` value, not merely many small ones."""
        assert len(self._err(_anthropic_body({"type": self._HUGE}))) < 1000

    def test_leading_whitespace_does_not_eat_the_message(self) -> None:
        """Bounding must not become deleting.

        The window was sliced from position 0, so its size was an
        implicit bet on how much leading whitespace a body would carry.
        900 spaces before real text filled the whole window with
        whitespace and the value rendered as the empty string — the one
        part carrying information dropped, for a body a proxy can
        produce trivially. The window now starts at the first non-space.
        """
        from vera.runtime.inference import _truncate

        assert _truncate(" " * 900 + "REAL TEXT") == "REAL TEXT"
        # Longer than the window itself, so the fix cannot be a bigger window.
        assert _truncate("\n" * 20_000 + "REAL TEXT") == "REAL TEXT"

    def test_blank_keys_are_not_reported_as_no_keys(self) -> None:
        """"(no keys)" must mean there were none, not that they printed as none.

        Derived from the rendered string, it stated something false: an
        object with one key — 900 spaces — was reported as having none.
        A reader cannot act on a message that denies the thing it is
        describing.
        """
        from vera.runtime.inference import _describe_keys, _describe_types

        assert _describe_keys({" " * 900 + "realkey": 1}) == "realkey"
        assert _describe_keys({}) == "(no keys)"
        assert _describe_keys({" " * 900: 1}) == "(keys are blank)"
        assert _describe_types([]) == "(none)"
        assert _describe_types([{"type": " " * 900}]) == "(types are blank)"

    def test_blank_reason_and_body_say_blank(self) -> None:
        """A present-but-blank value must not render as dangling text.

        A whitespace-only `stop_reason` produced `; stop_reason=).` and a
        whitespace-only body `is not JSON: ` with nothing after the
        colon. Present-and-blank is not the same as absent, so the clause
        stays and says which it was.
        """
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", _anthropic_body_with(
                {"stop_reason": "   "}, {"type": "thinking"},
            ))
        assert "stop_reason=(blank)" in str(excinfo.value)

        with pytest.raises(InferenceError) as excinfo:
            _call("openai", _openai_body_with(None, choice={"finish_reason": "  "}))
        assert "finish_reason=(blank)" in str(excinfo.value)

        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", "   ")
        assert str(excinfo.value).endswith("is not JSON: (blank)")

    def test_the_bound_is_the_documented_one(self) -> None:
        """Pinned against the constant, so a widened bound is a decision.

        Each cell above allows 1000 characters — envelope plus detail —
        rather than the raw constant, so this cell keeps the real figure
        honest instead of letting the slack absorb a regression.
        """
        assert _ERROR_BODY_CHARS == 200


# =====================================================================
# Credentials never reach a Vera value
# =====================================================================


class TestCredentialRedaction1333:
    """A provider's 401 body quotes the key it rejected.

    `Incorrect API key provided: sk-ant-…` is what OpenAI-style providers
    actually return, and this module lifts that body into a
    `Result::Err` — which the program prints, logs, or ships to CI. The
    fix that surfaced the provider's own message is what created the
    exposure, so the redaction ships with it.
    """

    _KEY = "sk-ant-api03-REALKEYVALUE1234567890"

    def _err_for(self, body: str, key: str = _KEY) -> str:
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(401, body), key=key)
        return str(excinfo.value)

    def test_the_configured_key_is_redacted(self) -> None:
        message = self._err_for(json.dumps({
            "error": {"message": f"Incorrect API key provided: {self._KEY}."},
        }))
        assert self._KEY not in message
        assert "[redacted]" in message
        # The rest of the message survives — redaction, not suppression.
        assert "Incorrect API key provided" in message
        assert "401" in message
        assert "anthropic" in message

    def test_a_credential_shaped_token_we_never_configured_is_redacted(self) -> None:
        """A proxy quoting ANOTHER tenant's key is still a leak.

        The exact-match rule cannot see this one, which is why the
        pattern exists beside it rather than instead of it.
        """
        other = "sk-proj-SOMEONEELSESKEY99887766"
        message = self._err_for(
            json.dumps({"error": {"message": f"rejected upstream key {other}"}}),
            key="sk-ant-unrelated-value-here",
        )
        assert other not in message
        assert "[redacted]" in message

    @pytest.mark.parametrize(
        "token",
        [
            "sk-ABCDEFGH12345678",
            "sk_ABCDEFGH12345678",
            "key-ABCDEFGH12345678",
            "key_ABCDEFGH12345678",
            "token-ABCDEFGH12345678",
            "token_ABCDEFGH12345678",
            # xAI issues `xai-…`, which no other prefix covers.  Repeated
            # blocks rather than an alphabet run so the fixture stays
            # uninteresting to a secret scanner (1.70 bits/character).
            "xai-abababababababab",
            "xai_abababababababab",
        ],
    )
    def test_each_documented_prefix_is_redacted(self, token: str) -> None:
        """Every prefix the spec promises, one cell each.

        A single case would stay green while five of the six silently
        stopped matching.
        """
        message = self._err_for(f"upstream said: {token}", key="")
        assert token not in message
        assert "[redacted]" in message

    def test_a_foreign_xai_token_is_redacted(self) -> None:
        """An `xai-…` token that is NOT the configured key must still go.

        The configured key here is the opaque hex fixture, which shares no
        characters with the token, so only the PATTERN rule can catch it —
        the exact-key rule is out of the picture by construction. This is
        the shape a gateway produces when it echoes a different tenant's
        credential back in a 401.
        """
        token = "xai-abababababababab"
        message = self._err_for(
            f"upstream rejected {token}", key=self._OPAQUE_KEY,
        )
        assert token not in message
        assert "xai-" not in message
        assert "[redacted]" in message

    #: Every route by which provider-supplied text reaches an `Err`, each
    #: with the canary key planted in it.  The reported leak was the
    #: non-JSON 200 body; sweeping the module for message-building sites
    #: that rendered provider text without redacting found six more, so
    #: the table IS the invariant — a new message that quotes the
    #: provider and is not listed here is the next leak.
    _LEAK_ROUTES: tuple[tuple[str, str, str], ...] = (
        ("non-JSON 200 body", "anthropic", "<html>proxy said {key}</html>"),
        ("stop_reason", "anthropic",
         '{{"content": [{{"type": "thinking"}}], "stop_reason": "{key}"}}'),
        ("finish_reason", "openai",
         '{{"choices": [{{"message": {{"content": null}}, '
         '"finish_reason": "{key}"}}]}}'),
        ("response key name", "anthropic", '{{"{key}": 1}}'),
        ("content block type", "anthropic",
         '{{"content": [{{"type": "{key}"}}]}}'),
        ("text block keys", "anthropic",
         '{{"content": [{{"type": "text", "{key}": 1}}]}}'),
        ("message keys", "openai",
         '{{"choices": [{{"message": {{"role": "a", "{key}": 1}}}}]}}'),
        ("refusal", "openai",
         '{{"choices": [{{"message": {{"content": null, '
         '"refusal": "{key}"}}}}]}}'),
        # The four the sweep missed first time: every one renders provider
        # text through a helper that takes `api_key`, and dropping the
        # argument at any of them turned nothing red.
        ("openai part types", "openai",
         '{{"choices": [{{"message": {{"content": '
         '[{{"type": "{key}"}}]}}}}]}}'),
        ("openai text part keys", "openai",
         '{{"choices": [{{"message": {{"content": '
         '[{{"type": "text", "{key}": 1}}]}}}}]}}'),
        ("choices-level response keys", "openai", '{{"{key}": 1}}'),
        ("choice keys", "openai", '{{"choices": [{{"{key}": 1}}]}}'),
    )

    #: Helpers that render provider-supplied text and therefore take the
    #: key.  Listed literally: deriving them from the source would grow to
    #: match whatever the source does and could never report a new one.
    _RENDERERS = (
        "_safe", "_describe_keys", "_describe_types",
        "_reason_clause", "_missing_or_wrong", "_text_fragments",
    )

    #: How many call sites hand `api_key` to one of those helpers today.
    #: A literal, so ADDING a render site fails this cell and forces the
    #: author to decide whether it needs a route row above.  Measured by
    #: the AST walk below: 23 at 157ae167 and 24 here, the difference
    #: being this round's `_reason_clause` call inside
    #: `_empty_completion_error`.
    _API_KEY_RENDER_SITES = 24

    #: Rows in the route table, pinned separately from the site count: the
    #: two answer different questions, and a deleted row is invisible to
    #: the other.
    _LEAK_ROUTE_COUNT = 12

    def test_every_api_key_render_site_is_accounted_for(self) -> None:
        """A new render site must be classified, not silently uncovered.

        This does NOT claim a one-to-one map: several sites share a route
        (`_error_body_detail` alone calls `_safe` five times for the single
        rejection-body route), so asserting count equality between sites
        and rows would be false by construction. What it pins is the thing
        that went wrong — four render sites were added over three rounds,
        none got a row, and nothing failed.

        Counted by parsing the module rather than by regex, because the
        regex was WRONG: it read 22 where the true count was 23, missing a
        positional `api_key` in a call spread over enough lines, so the
        tripwire was weaker than it advertised. Its cost was not the
        problem — review raised catastrophic backtracking, and that does
        not apply here: the alternation's two branches are
        first-character disjoint, so the star is unambiguous, and an
        independent reviewer measured it linear across nine adversarial
        shapes from n=1,000 to n=16,000 (×14.7-16.1 per ×16 of input,
        worst case 3.64 ms). The walk reads each renderer's own signature
        for the parameter's position, so positional and keyword sites both
        count and a `def` line is a signature rather than a call by
        construction.
        """
        source = (
            Path(__file__).resolve().parent.parent
            / "vera" / "runtime" / "inference.py"
        ).read_text(encoding="utf-8")
        tree = ast.parse(source)

        api_key_index: dict[str, int] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name in self._RENDERERS:
                names = [a.arg for a in node.args.args]
                if "api_key" in names:
                    api_key_index[node.name] = names.index("api_key")
        assert set(api_key_index) == set(self._RENDERERS), (
            f"renderers without an `api_key` parameter: "
            f"{sorted(set(self._RENDERERS) - set(api_key_index))} — the "
            f"list is stale, or a helper stopped taking the key"
        )

        sites = 0
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            name = func.id if isinstance(func, ast.Name) else None
            if name not in api_key_index:
                continue
            if any(kw.arg == "api_key" for kw in node.keywords) or (
                len(node.args) > api_key_index[name]
            ):
                sites += 1

        assert sites == self._API_KEY_RENDER_SITES, (
            f"{sites} render sites take `api_key`, expected "
            f"{self._API_KEY_RENDER_SITES}. A site was added or removed: "
            f"decide whether it needs a row in _LEAK_ROUTES (which has "
            f"{len(self._LEAK_ROUTES)}), then update this count."
        )
        # The second tripwire, and it is not redundant: the site count is
        # blind to the TABLE, so deleting a route row left the suite green
        # and one cell lighter. A literal here makes that fail loud.
        assert len(self._LEAK_ROUTES) == self._LEAK_ROUTE_COUNT, (
            f"_LEAK_ROUTES has {len(self._LEAK_ROUTES)} rows, expected "
            f"{self._LEAK_ROUTE_COUNT}. A row was added or deleted; the "
            f"table IS the redaction invariant, so removing one silently "
            f"drops a route from cover."
        )

    @pytest.mark.parametrize(
        ("label", "provider", "template"),
        _LEAK_ROUTES,
        ids=[row[0] for row in _LEAK_ROUTES],
    )
    def test_no_route_leaks_the_configured_key(
        self, label: str, provider: str, template: str,
    ) -> None:
        """The invariant: no provider-supplied text reaches an `Err` unredacted.

        Driven through `_call_inference_provider` with the key configured,
        exactly as a real run has it, so each row measures the production
        path rather than a helper in isolation.
        """
        body = template.format(key=self._KEY)
        with patch(
            "urllib.request.urlopen",
            MagicMock(return_value=_mock_response_bytes(body.encode("utf-8"))),
        ), pytest.raises(InferenceError) as excinfo:
            _call_inference_provider(provider, "prompt", "", self._KEY)
        message = str(excinfo.value)
        assert self._KEY not in message, f"{label} leaked the configured key"
        # A prefix is most of what makes a leaked key useful, so the
        # assertion is not satisfied by clipping the tail off.
        assert self._KEY[:20] not in message
        assert "[redacted]" in message

    def test_non_json_success_body_redacts_the_key(self) -> None:
        """THE REPORTED LEAK, on its own: a 200 whose body is not JSON.

        `_truncate(decoded)` built this message with no redaction at all,
        so a gateway page echoing the credential put it straight into a
        Vera value.  Kept as its own cell beside the table because it is
        the one the review named.
        """
        body = f"<html>Bad gateway. Upstream key {self._KEY} rejected.</html>"
        with patch(
            "urllib.request.urlopen",
            MagicMock(return_value=_mock_response_bytes(body.encode("utf-8"))),
        ), pytest.raises(InferenceError) as excinfo:
            _call_inference_provider("anthropic", "prompt", "", self._KEY)
        message = str(excinfo.value)
        assert self._KEY not in message
        assert self._KEY[:20] not in message
        assert "[redacted]" in message
        assert "not JSON" in message

    #: A configured key the credential PATTERN cannot see: no `sk-`/`key-`/
    #: `token-` prefix at all.  Every other redaction fixture uses a
    #: `sk-ant-…` key, which both rules match — so the exact-key rule was
    #: covered only incidentally, and deleting it left the suite green.
    #:
    #: Repeated `deadbeef` rather than an arbitrary hex string, and the
    #: choice is the scanner's: 32 hex characters drawn evenly measure
    #: 4.0 bits per character, which is above the 3.5 that Gitleaks'
    #: `generic-api-key` rule treats as secret-like, and CI flagged the
    #: previous fixture on exactly that basis.  This value measures
    #: 2.1556 bits per character over five distinct characters, and reads
    #: to a human as the placeholder it is.  That is a synthetic key
    #: chosen to be scanner-neutral, NOT a secret hidden from the
    #: scanner: no allowlist, no per-line suppression pragma, no
    #: scanner config.  (Spelled out rather than quoted, because the
    #: literal directive string suppresses whatever line it appears
    #: on — writing it here, one line above the fixture, would be the
    #: very thing this comment disclaims.)
    _OPAQUE_KEY = "deadbeefdeadbeefdeadbeefdeadbeef"

    def test_the_opaque_fixture_stays_below_the_scanner_threshold(self) -> None:
        """Keep the fixture uninteresting to a secret scanner, by measurement.

        The constraint is enforced here rather than left to CI, so raising
        the fixture's entropy fails locally with the reason attached
        instead of surfacing as a security-job failure two pushes later.
        """
        import math
        from collections import Counter

        counts = Counter(self._OPAQUE_KEY)
        n = len(self._OPAQUE_KEY)
        entropy = -sum((c / n) * math.log2(c / n) for c in counts.values())
        assert entropy < 3.5, (
            f"the opaque-key fixture measures {entropy:.4f} bits per "
            f"character, at or above the 3.5 that Gitleaks' "
            f"generic-api-key rule treats as secret-like"
        )

    def test_a_key_the_pattern_cannot_match_is_still_redacted(self) -> None:
        """The exact-key rule, pinned where the pattern cannot stand in.

        Providers issue credentials in shapes the pattern was never
        written for — a bare hex string here, `xai-…` elsewhere — which
        is exactly why the configured value is matched literally beside
        the pattern rather than instead of it.
        """
        assert not re.search(r"(?:sk|key|token)[-_]", self._OPAQUE_KEY), (
            "the fixture key must NOT match the credential pattern, or "
            "this cell measures the pattern rule again"
        )
        message = self._err_for(
            json.dumps({
                "error": {"message": f"rejected key {self._OPAQUE_KEY}"},
            }),
            key=self._OPAQUE_KEY,
        )
        assert self._OPAQUE_KEY not in message
        assert "[redacted]" in message
        assert "rejected key" in message

    def test_a_one_character_key_is_still_redacted(self) -> None:
        """No minimum-length floor on the exact-key rule — deliberately.

        A pathologically short key redacts incidental text too: with the
        key `a`, `stop_reason=max_tokens` renders as
        `stop_reason=m[redacted]x_tokens`. That is accepted rather than
        fixed: the damage is cosmetic and lands only on an `Err` that
        still carries provider, model and status, whereas a length floor
        would stop redacting short REAL tokens, which gateways and
        proxies do issue. Redaction does not trade coverage for
        tidiness.
        """
        message = self._err_for("upstream rejected a", key="a")
        assert "[redacted]" in message
        # The rest of the Err survives, which is what makes the trade sound.
        assert "401" in message
        assert "anthropic" in message

    def test_ordinary_words_are_not_redacted(self) -> None:
        """The paired negative: redaction that eats prose is a different bug.

        `token-` needs 8+ opaque characters after it, so an English
        sentence about tokens survives intact.
        """
        message = self._err_for(
            "the token-based flow needs a key-holder from an xai-ish gateway",
            key="",
        )
        assert "token-based" in message
        assert "key-holder" in message
        # `xai` joined the alternation in round 12, so it needs the same
        # negative: without it, widening the rule would red the two words
        # above and say nothing about the prefix that was just added.
        assert "xai-ish" in message
        assert "[redacted]" not in message

    def test_redaction_precedes_truncation(self) -> None:
        """A key clipped by the bound must not leave a usable fragment.

        The fixture puts the key across the 200-character boundary, so
        under the reversed order (truncate, then redact) only about nine
        characters of it survive — `sk-ant-ap`. That is too short for the
        credential pattern's eight-character tail to match, so the
        fragment sails through unredacted.

        The assertions matter more than the position here. `_KEY not in
        message` and `_KEY[:20] not in message` were BOTH satisfied by
        that nine-character leak, which is how this cell passed while
        testing nothing: reversing the order left it green. The live
        assertion is that no `sk-` fragment survives at all.
        """
        body = "x" * (_ERROR_BODY_CHARS - 10) + f" {self._KEY} " + "y" * 500
        message = self._err_for(body)
        assert self._KEY not in message
        assert "sk-" not in message, (
            "a clipped credential fragment survived — the pattern needs "
            "eight characters after the prefix, so a short tail escapes "
            "unless redaction runs first"
        )


# =====================================================================
# Spec 9.5.5's promise: every provider-backed Err names provider AND model
# =====================================================================


class TestProviderAndModelNaming1333:
    """The claim in spec 9.5.5 is a contract; these cells are its test.

    It was false for two whole kinds when written: the UTF-8 failure
    named no model, and a transport failure reached the boundary — which
    knew the provider but had never resolved the model — so
    `URLError`/`TimeoutError`/`ConnectionRefusedError` were labelled with
    the provider alone.
    """

    #: ORDERED, not two presence checks: `provider` and `model` swapped
    #: into each other's placeholders satisfies `"anthropic" in message`
    #: and `"claude-opus-5" in message` both, and reads as nonsense.
    _NAMED = re.compile(r"Inference provider 'anthropic' \(claude-opus-5\)")

    def test_shape_failure_names_both_in_order(self) -> None:
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", _anthropic_body({"type": "thinking"}))
        assert self._NAMED.search(str(excinfo.value))

    def test_utf8_failure_names_both_in_order(self) -> None:
        """Was `Inference provider 'anthropic' returned a response body…`."""
        with patch(
            "urllib.request.urlopen",
            MagicMock(return_value=_mock_response_bytes(b"hi \xff\xfe there")),
        ), pytest.raises(InferenceError) as excinfo:
            _call_inference_provider("anthropic", "prompt", "", "sk-test")
        assert self._NAMED.search(str(excinfo.value))

    def test_http_rejection_names_both_in_order(self) -> None:
        with pytest.raises(InferenceError) as excinfo:
            _call_raising("anthropic", _http_error(401, "{}"))
        assert self._NAMED.search(str(excinfo.value))

    def test_non_json_body_names_both_in_order(self) -> None:
        with pytest.raises(InferenceError) as excinfo:
            _call("anthropic", "<html>nope</html>")
        assert self._NAMED.search(str(excinfo.value))

    #: The transport failures that never reach the parse at all, so the
    #: boundary is the only place that can name the model.
    _TRANSPORT = (
        ("URLError", urllib.error.URLError("dns")),
        ("TimeoutError", TimeoutError("timed out")),
        ("ConnectionRefusedError", ConnectionRefusedError(61, "Connection refused")),
    )

    @pytest.mark.parametrize(
        ("label", "exc"), _TRANSPORT, ids=[row[0] for row in _TRANSPORT],
    )
    def test_transport_failure_names_both_in_order(
        self, label: str, exc: BaseException,
    ) -> None:
        """The boundary label, end to end — the kind that had no model at all."""
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider", side_effect=exc,
        ):
            exec_result = execute(
                result, env_vars={"VERA_ANTHROPIC_API_KEY": "sk-ant-test"},
            )
        assert exec_result.value == 1
        assert self._NAMED.search(exec_result.stdout)
        assert label in exec_result.stdout

    def test_boundary_names_the_overriding_model_not_the_default(self) -> None:
        """`VERA_INFERENCE_MODEL` is the model the request selected, so it is named.

        A label hardcoding the registry default would satisfy every cell
        above and be actively misleading on exactly the runs where the
        model is the variable under test.
        """
        result = _compile_ok(_CLASSIFY_SOURCE)
        with patch(
            "vera.runtime.inference._call_inference_provider",
            side_effect=TimeoutError("timed out"),
        ):
            exec_result = execute(result, env_vars={
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
                "VERA_INFERENCE_MODEL": "claude-opus-4-6",
            })
        assert exec_result.stdout.startswith(
            "Inference provider 'anthropic' (claude-opus-4-6) failed: "
        )


#: The maintainer's six-provider sweep, in registry order, each row carrying
#: the response shape that provider actually returns and its flagship model
#: spelled LITERALLY — deriving the model from `_PROVIDERS` would pin the
#: assertion to itself and stay green through any edit to the row.
_SWEEP: tuple[tuple[str, str, str, str], ...] = (
    ("anthropic", "VERA_ANTHROPIC_API_KEY", "claude-opus-5", _THINKING_FIRST),
    ("openai", "VERA_OPENAI_API_KEY", "gpt-5.6-sol", _openai_body("Positive")),
    ("moonshot", "VERA_MOONSHOT_API_KEY", "kimi-k3", _openai_body("Positive")),
    ("mistral", "VERA_MISTRAL_API_KEY", "mistral-large-latest", _openai_body("Positive")),
    ("xai", "VERA_XAI_API_KEY", "grok-4.6", _openai_body("Positive")),
    ("deepseek", "VERA_DEEPSEEK_API_KEY", "deepseek-v4-pro", _openai_body("Positive")),
)


class TestProviderSweep1333:
    """All six providers answer `Positive`, which is what the sweep showed
    for five of them and must now show for the sixth."""

    def test_sweep_covers_every_registered_provider(self) -> None:
        """A row added to `_PROVIDERS` without a sweep row fails here.

        Otherwise the sweep silently stops being a sweep.
        """
        assert [row[0] for row in _SWEEP] == list(_PROVIDERS)
        for name, env_key, _model, _body in _SWEEP:
            assert _PROVIDERS[name].env_key == env_key

    @pytest.mark.parametrize(
        ("provider", "env_key", "model", "body"),
        _SWEEP,
        ids=[row[0] for row in _SWEEP],
    )
    def test_provider_returns_its_completion(
        self, provider: str, env_key: str, model: str, body: str,
    ) -> None:
        """End to end, with the provider pinned — as the sweep should have run."""
        value, stdout = _run_with_transport(
            body,
            env={"VERA_INFERENCE_PROVIDER": provider, env_key: "sk-test"},
        )
        assert value == 0
        assert stdout == "Positive"

    @pytest.mark.parametrize(
        ("provider", "env_key", "model", "body"),
        _SWEEP,
        ids=[row[0] for row in _SWEEP],
    )
    def test_provider_names_itself_when_the_shape_fails(
        self, provider: str, env_key: str, model: str, body: str,
    ) -> None:
        """Every branch's shape failure names its own provider and model.

        A message hardcoding one provider's name would satisfy a
        single-row test; running the whole registry through it cannot be.
        """
        value, stdout = _run_with_transport(
            json.dumps({"unexpected": "shape"}),
            env={"VERA_INFERENCE_PROVIDER": provider, env_key: "sk-test"},
        )
        assert value == 1
        _assert_deliberate(stdout, f"Inference provider '{provider}' ({model})")

    def test_an_empty_key_is_skipped_by_auto_detect(self) -> None:
        """A variable exported as "" is skipped, exactly as if unset.

        The loop tests each key for TRUTHINESS, so `export
        VERA_ANTHROPIC_API_KEY=` leaves anthropic out of the running and
        the next configured provider wins. Spec 9.5.5 said "whose key is
        present", which reads as covering the empty string — a shell
        variable set to "" is present by any ordinary meaning of the
        word, and this cell is what the corrected wording rests on.

        Asserted through the routed request's own `Err`, so it measures
        the provider the runtime actually selected rather than a mock's
        bookkeeping.
        """
        value, stdout = _run_with_transport(
            json.dumps({"unexpected": "shape"}),
            env={
                "VERA_ANTHROPIC_API_KEY": "",
                "VERA_OPENAI_API_KEY": "sk-abababababab",
            },
        )
        assert value == 1
        _assert_deliberate(stdout, "Inference provider 'openai' (gpt-5.6-sol)")
        assert "anthropic" not in stdout

    def test_auto_detect_misattribution_is_self_diagnosing(self) -> None:
        """The sweep's own trap: an exported Anthropic key wins the "xAI run".

        With `VERA_INFERENCE_PROVIDER` unset, auto-detect takes the first
        key set to a non-empty value in registry insertion order, so a
        cumulative shell
        runs anthropic while the operator believes they are testing xAI.
        The Err must name the provider that actually answered.
        """
        value, stdout = _run_with_transport(
            json.dumps({"unexpected": "shape"}),
            env={
                "VERA_ANTHROPIC_API_KEY": "sk-ant-test",
                "VERA_XAI_API_KEY": "sk-xai-test",
            },
        )
        assert value == 1
        _assert_deliberate(stdout, "Inference provider 'anthropic' (claude-opus-5)")
        assert "xai" not in stdout
