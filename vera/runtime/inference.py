"""Inference effect host bindings.

Extracted from `execute()` in `vera/codegen/api.py` (#421).  Includes the LLM
provider registry and HTTP call helper, which are used only by this family.
"""

from __future__ import annotations

import functools
import re
from dataclasses import dataclass
from typing import TYPE_CHECKING

import wasmtime

from vera.runtime.heap import (
    _alloc_result_err_string,
    _alloc_result_ok_string,
    _read_wasm_string,
)
from vera.runtime.http import _HTTP_TIMEOUT

if TYPE_CHECKING:  # pragma: no cover — annotations only
    from collections.abc import Mapping
    from urllib.error import HTTPError


class InferenceError(RuntimeError):
    """A failure this module DESCRIBED, rather than one it merely hit.

    Every message raised as an `InferenceError` was written for the
    person reading a `Result::Err` in a Vera program: it names the
    provider, the model that answered, and what about the response was
    wrong.  The host boundary publishes those verbatim and labels
    everything else with its Python type, so the class is the whole of
    the distinction between "we have something to say about this" and
    "something went wrong that we did not anticipate".

    A dedicated class rather than the plain `RuntimeError` / `ValueError`
    pair the boundary used to test for (#1333 review): those are the
    types an unforeseen failure deep in the transport raises too, so
    `RuntimeError("boom")` from anywhere below us claimed the verbatim
    channel and reached the user as the bare word `boom` — the defect
    class this family exists to close, one level up.

    `RuntimeError` alone, deliberately not also `ValueError`: this module
    wraps `json.loads` in `except ValueError` in two places, and a
    subclass of both would let a future edit that moved a deliberate
    raise inside one of those blocks be swallowed by its own handler.
    """


@dataclass(frozen=True)
class _ProviderConfig:
    """Configuration for a single LLM inference provider."""

    env_key: str         # environment variable holding the API key
    url: str             # chat completions endpoint URL
    default_model: str   # provider's flagship model when VERA_INFERENCE_MODEL is unset
    auth_style: str      # "anthropic" | "bearer"
    response_style: str  # "anthropic" | "openai"


#: Registry of supported inference providers.
#: Adding a new OpenAI-compatible provider is a one-row change here.
#:
#: Each row's ``default_model`` is that provider's flagship general-chat
#: model, verified against the vendor's own live documentation when set.
#: A vendor's cheap tier is reachable through ``VERA_INFERENCE_MODEL``;
#: the default is not the place to trade capability for price, because a
#: program's contracts are written against what the default can do.
_PROVIDERS: dict[str, _ProviderConfig] = {
    "anthropic": _ProviderConfig(
        env_key="VERA_ANTHROPIC_API_KEY",
        url="https://api.anthropic.com/v1/messages",
        default_model="claude-opus-5",
        auth_style="anthropic",
        response_style="anthropic",
    ),
    "openai": _ProviderConfig(
        env_key="VERA_OPENAI_API_KEY",
        url="https://api.openai.com/v1/chat/completions",
        default_model="gpt-5.6-sol",
        auth_style="bearer",
        response_style="openai",
    ),
    "moonshot": _ProviderConfig(
        env_key="VERA_MOONSHOT_API_KEY",
        url="https://api.moonshot.ai/v1/chat/completions",
        default_model="kimi-k3",
        auth_style="bearer",
        response_style="openai",
    ),
    "mistral": _ProviderConfig(
        env_key="VERA_MISTRAL_API_KEY",
        url="https://api.mistral.ai/v1/chat/completions",
        default_model="mistral-large-latest",
        auth_style="bearer",
        response_style="openai",
    ),
    # New providers append here: insertion order is the auto-detect
    # precedence, so prepending would change which key wins when
    # several are set.
    "xai": _ProviderConfig(
        env_key="VERA_XAI_API_KEY",
        url="https://api.x.ai/v1/chat/completions",
        default_model="grok-4.6",
        auth_style="bearer",
        response_style="openai",
    ),
    "deepseek": _ProviderConfig(
        env_key="VERA_DEEPSEEK_API_KEY",
        url="https://api.deepseek.com/v1/chat/completions",
        default_model="deepseek-v4-pro",
        auth_style="bearer",
        response_style="openai",
    ),
}


#: Longest provider-supplied error text we quote back into a Vera-level
#: `Result::Err`.  A misconfigured proxy answers with a whole HTML page;
#: the useful signal is in its first line, and the Err string is a value
#: a Vera program may go on to concatenate, print, or match against.
_ERROR_BODY_CHARS = 200

#: Most of an HTTP error body we will read into memory, in BYTES.  Sized
#: far above `_ERROR_BODY_CHARS` so a legitimate JSON error envelope
#: always arrives whole and is parsed, while a hostile or misconfigured
#: endpoint answering a rejection with megabytes cannot make us hold
#: them: the message we build out of it is 200 characters either way.
_ERROR_BODY_CAP = 64 * 1024


def _truncate(text: str) -> str:
    """*text*, clipped to `_ERROR_BODY_CHARS` with the clipping made visible.

    A bounded WINDOW is sliced before stripping.  Every caller feeds this
    values that came from a remote server, and `strip()` on a 64 MB
    `stop_reason` would copy the whole thing in order to discard all but
    200 characters of it.

    The window starts at the first non-space character rather than at
    position 0.  Taking it from the front made "four times the bound" a
    guess about how much leading whitespace a hostile body would use:
    900 spaces followed by a sentence filled the whole window with
    whitespace and rendered as the empty string, losing the only part of
    the value that carried information — and `_describe_keys` then
    reported "(no keys)" for an object that had one, which is not a
    truncated statement but a false one.  Finding the first non-space is
    linear and copies nothing.
    """
    if len(text) <= _ERROR_BODY_CHARS:
        return text.strip()
    leading = re.match(r"\s*", text)
    start = leading.end() if leading else 0
    head = text[start : start + _ERROR_BODY_CHARS * 4].strip()
    if len(head) <= _ERROR_BODY_CHARS:
        return head
    return head[:_ERROR_BODY_CHARS] + "... (truncated)"


#: Credential-shaped tokens: a recognised prefix, then enough opaque
#: characters to be a secret rather than a word.  A provider's 401 body
#: quotes the key it rejected ("Incorrect API key provided: sk-ant-…"),
#: and this module lifts that body into a Vera-level `Result::Err` — a
#: value the program goes on to print, log, or ship to CI.
#:
#: `xai` is here because xAI issues `xai-…`, which none of the other
#: prefixes match; it was uncovered until a review pass caught it.  The
#: pattern cannot cover every registered provider and is not meant to:
#: Mistral issues a bare alphanumeric key with no prefix at all, which no
#: prefix rule could recognise without also redacting ordinary words.
#: That is precisely why the exact-configured-key rule sits beside this
#: one — the two are complements, not alternatives.
_CREDENTIAL_RE = re.compile(r"(?:sk|key|token|xai)[-_][A-Za-z0-9_-]{8,}")


#: The characters a quoting layer may write with a backslash before them:
#: JSON's `\"`, `\\` and `\/`, and `repr`'s `\'` and `\\`.
_BACKSLASHED = frozenset("\"\\/'")

#: The characters HTML names: `&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`.
_HTML_NAMED = {"&": "amp", "<": "lt", ">": "gt", '"': "quot", "'": "apos"}

#: How many leading zeros an HTML numeric entity may carry here.  A bound,
#: so every form has a bounded length and the cut rule a bounded window.
_ENTITY_ZEROS = 6

#: The longest any one form of a character can be: `&#x`, the zeros, the
#: digits, `;`.
_LONGEST_FORM = 3 + _ENTITY_ZEROS + 6 + 1


def _hex_atoms(code: int, width: int) -> list[str]:
    """One atom per hex digit of *code*, written to *width* digits, each
    digit in either case."""
    atoms = []
    for digit in f"{code:0{width}x}":
        atoms.append(f"[{digit}{digit.upper()}]" if digit.isalpha() else digit)  # pragma: no mutate — equivalent: a digit's class `[00]` matches what `0` does
    return atoms


def _char_forms(char: str) -> list[list[str]]:
    r"""Every form a quoting layer may give *char*, each a list of atoms (a
    regex matching one character of text, or a bounded run of zeros).

    The forms: the character itself; a backslash before it where JSON or
    `repr` writes one (`\"`, `\\`, `\/`, `\'`); JSON's `\uXXXX` and `repr`'s
    `\xXX`, hex digits in either case; and HTML's numeric entities, decimal
    and hex, with up to :data:`_ENTITY_ZEROS` leading zeros, and its named
    one where the character has one.
    """
    code = ord(char)
    forms: list[list[str]] = [[re.escape(char)]]
    if char in _BACKSLASHED:
        forms.append([r"\\", re.escape(char)])
    forms.append([r"\\", "u", *_hex_atoms(code, 4)])
    forms.append([r"\\", "x", *_hex_atoms(code, 2)])
    zeros = f"0{{0,{_ENTITY_ZEROS}}}"
    forms.append(["&", "\\#", zeros, *str(code), ";"])
    forms.append(["&", "\\#", "[xX]", zeros, *_hex_atoms(code, 1), ";"])
    if char in _HTML_NAMED:
        forms.append(["&", *_HTML_NAMED[char], ";"])
    return forms


@functools.lru_cache(maxsize=32)
def _key_patterns(
    key: str,
) -> tuple[re.Pattern[str], re.Pattern[str], re.Pattern[str]]:
    r"""The configured key as patterns over the text a message quotes: the
    key whole; a form of its first character; and the start of the key at
    the end of a text a cut ended (#1854).

    A quoting layer between the provider and the message re-spells a
    character at a time, by a fixed table, and may choose for each
    occurrence of a character on its own: an encoder that escapes one
    solidus and not the next, or writes `\u004F` for the first `O` only,
    is still quoting the key.  So the key is matched character by
    character, each character in any form a quoting layer may give that
    one character (:func:`_char_forms`): JSON (an error body), Python's
    `repr` (an exception's text) and HTML (a proxy's error page).

    A transformation of the whole key is not a quoting, and is not
    matched: percent-encoding, base64, a hash or a mask is a value the
    provider computed from the key, not the key under a layer that quotes
    it, and none of it is what a reader could use as the key.

    At a cut the text may end inside the key: after a run of its leading
    characters, each in any form, and even inside the next character's
    form (`...\u002`).  The cut pattern matches such an end, anchored at
    the end of the text; it is tried where a form of the first character
    begins, leftmost (longest) first.

    A form that begins with a backslash or an ampersand shares its first
    character with the bare `\` or `&`, so a pattern backtracks only at a
    key's own `\` and `&`: the work a text can cause is bounded by the
    configured key, which the text does not choose.
    """
    forms = [_char_forms(c) for c in key]
    whole = "".join(
        "(?:" + "|".join("".join(f) for f in fs) + ")" for fs in forms)

    def partial(fs: list[list[str]]) -> str:
        parts = {"".join(f[:j]) for f in fs for j in range(1, len(f))}
        return "|".join(sorted(parts))

    tail = ""
    for fs in reversed(forms):
        full = "(?:" + "|".join("".join(f) for f in fs) + ")"
        part = partial(fs)
        inner = full + (f"(?:{tail})?" if tail else "")
        tail = inner + (f"|{part}" if part else "")
    first = "|".join(sorted({"".join(f) for f in forms[0]}
                              | {"".join(f[:1]) for f in forms[0]}))
    return (re.compile(whole), re.compile(f"(?:{first})"),
            re.compile(f"(?:{tail})\\Z"))


@dataclass(frozen=True)
class HeldKeys:
    """The keys the host holds (#1854), which every redaction removes:
    built by :func:`_held_keys` alone, once per call of the host function.
    No redaction takes a single key, so no redaction chooses which of the
    host's keys a text may carry; the selected provider's key is passed on
    its own only where it is sent (the request's header)."""

    keys: tuple[str, ...] = ()


#: The held set of a host that holds no key.
NO_KEYS = HeldKeys()


def _key_spans(text: str, key: str, *, cut: bool) -> list[tuple[int, int]]:
    """The spans of *text* that hold *key*, one key the host holds, in any of its
    forms (:func:`_key_patterns`): every whole occurrence, and, at the end
    of a text a cut ended, the key's start."""
    if not key:
        return []
    whole, first, at_cut = _key_patterns(key)
    spans = [m.span() for m in whole.finditer(text)]
    if cut:
        # The start of the key at the end of the text begins with a form
        # of its first character, within the longest a proper prefix of
        # the key can be written (fewer than its length in characters,
        # each in its longest form): each such place is tried, leftmost
        # (longest) first.
        window = max(0, len(text) - len(key) * _LONGEST_FORM)
        for begin in first.finditer(text, window):  # pragma: no mutate — equivalent: the cut pattern is anchored at the text's end, so no place before the window can begin a match; the window bounds the places tried
            m = at_cut.match(text, begin.start())
            if m is not None:
                spans.append(m.span())
                break
    return spans


#: A credential-shaped token's prefix, and the characters a token holds.
_CREDENTIAL_PREFIX_RE = re.compile(r"(?:sk|key|token|xai)[-_]")
_TOKEN_CHARS = frozenset(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_-")


def _credential_tail(text: str) -> tuple[int, int] | None:
    """The span of a credential-shaped token's start at the end of *text*,
    which a cut ended: the cut may have taken the rest, so its length says
    nothing (#1854).

    Such a start lies in the run of token characters that ends the text,
    so the run is found by a scan back from the end, and the token begins
    at the run's leftmost prefix.  Searching the whole text for a prefix
    followed by token characters to its end tried every start and ran each
    to the first character outside a run: quadratic in a run, seconds over
    a body at the cap of `key-` repeated."""
    start = len(text)
    while start and text[start - 1] in _TOKEN_CHARS:
        start -= 1
    prefix = _CREDENTIAL_PREFIX_RE.search(text, start)
    return None if prefix is None else (prefix.start(), len(text))


def _secret_spans(
    text: str, *, held: HeldKeys, cut: bool,
) -> list[tuple[int, int]]:
    """Where a secret stands in *text*, each rule's spans found on *text*
    as it is (#1854).

    Every rule reads the original text, so no rule reads what another has
    already replaced, and none can stop another from running: each key
    the host holds whole, in any of its forms (`_key_spans`); a
    credential-shaped token; and, at the end of a text a cut ended (*cut*),
    each held key's start in any of its forms and a credential-shaped
    token's start, since the cut may have taken the rest of either.
    """
    spans: list[tuple[int, int]] = []
    for key in held.keys:
        spans.extend(_key_spans(text, key, cut=cut))
    spans.extend(m.span() for m in _CREDENTIAL_RE.finditer(text))
    if cut:
        tail = _credential_tail(text)
        if tail is not None:
            spans.append(tail)
    return spans


def _replace_spans(text: str, spans: list[tuple[int, int]]) -> str:
    """*text* with each run of overlapping or touching *spans* replaced,
    once, by `[redacted]`."""
    merged: list[tuple[int, int]] = []
    for start, stop in sorted(spans):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], stop))
        else:
            merged.append((start, stop))
    out: list[str] = []
    pos = 0  # pragma: no mutate — equivalent: `text[None:start]` is `text[0:start]`
    for start, stop in merged:
        out.append(text[pos:start])
        out.append("[redacted]")
        pos = stop
    out.append(text[pos:])
    return "".join(out)


def _redact(text: str, *, held: HeldKeys) -> str:
    """*text* with the configured key and credential-shaped tokens removed.

    Two rules, because neither covers the other: the configured key is
    matched exactly (it may have any shape at all, including one the
    pattern would miss), and the pattern catches keys this process was
    never given — a proxy quoting a DIFFERENT tenant's credential, or the
    same key in a form the exact match cannot see.
    """
    return _replace_spans(text, _secret_spans(text, held=held, cut=False))  # pragma: no mutate — equivalent: `cut` is read only as a truth value, and `None` is false


def _held_keys(env: Mapping[str, str]) -> HeldKeys:
    """Every key the host holds, the one source of :class:`HeldKeys`: the
    value of each provider's key variable that is set, whichever provider
    is selected, and each as the host reads the provider variable
    (lower-cased), since a key written there is quoted back in that form
    (#1854).  The host computes it once per call, and every redaction,
    cut or not, takes it."""
    held: list[str] = []
    for cfg in _PROVIDERS.values():
        key = env.get(cfg.env_key)
        if not key:
            continue
        for form in (key, key.lower()):
            if form not in held:
                held.append(form)
    return HeldKeys(tuple(held))


def _redact_cut(text: str, *, held: HeldKeys) -> str:
    """*text*, which a cut ended, redacted so the cut leaves no part of a
    secret (#1854).

    Redaction after a cut matches only what the cut left whole: a
    configured key the cut split is present as its first part, which
    matches nothing, and a credential-shaped token cut before its eighth
    character after the prefix is too short for the pattern.  So beside
    `_redact`'s two rules, the end of the text is read as the start of a
    secret the cut may have split: a proper prefix of any spelling of the
    configured key, or a credential-shaped prefix of any length, is
    redacted there.  The text is marked as truncated by its caller either
    way, so what this drops is at most part of a word the cut had already
    split.
    """
    return _replace_spans(text, _secret_spans(text, held=held, cut=True))


def _or_blank(rendered: str) -> str:
    """*rendered*, or `(blank)` when it came out empty.

    A provider-supplied value that is present but renders to nothing —
    a whitespace-only `stop_reason`, a body of three spaces — is not the
    same as an absent one, and a message must not imply it was.  Left
    bare it produced dangling text: `; stop_reason=).` and `is not
    JSON: ` with nothing after the colon.
    """
    return rendered or "(blank)"


def _safe(text: str, *, held: HeldKeys) -> str:
    """Provider-supplied text, made fit for a Vera value: redacted, then bounded.

    Both, in that order, at every point where text we did not write enters
    a message.  The order matters — truncating first can cut a credential
    in half and leave a usable prefix — and the single helper is what
    makes the rule checkable: any message-building site that renders
    provider text and does NOT go through here is a leak, which is how
    the six paths beyond the reported one were found.
    """
    return _truncate(_redact(text, held=held))


def _describe_keys(value: object, *, held: HeldKeys) -> str:
    """The keys of *value* if it is an object, else what it actually is.

    Used only inside error messages: when a response does not have the
    shape the branch expects, naming what it DID have is the difference
    between a report the user can act on and one they have to reproduce
    under a debugger.  Bounded, because the key list is attacker-shaped
    too — 3,000 keys is a 20,000-character message otherwise.
    """
    if isinstance(value, dict):
        # "(no keys)" is said only when there are none.  Deriving it from
        # the RENDERED string made it a false statement for an object
        # whose keys render as nothing — a key of 900 spaces reported an
        # object with one key as having none.
        if not value:
            return "(no keys)"
        return (
            _safe(", ".join(str(k) for k in value), held=held)
            or "(keys are blank)"
        )
    return f"(not an object: {type(value).__name__})"


def _describe_types(items: list[object], *, held: HeldKeys) -> str:
    """The distinct `type` discriminators in *items*, in first-seen order.

    This is what turns #1333's failure into a self-explaining one: an
    Anthropic response with no text block reports `thinking` rather than
    an unqualified "no text".  Bounded for the same reason as
    `_describe_keys`.
    """
    seen: list[str] = []
    for item in items:
        kind = (
            str(item.get("type", "(untyped)"))
            if isinstance(item, dict)
            else f"(not an object: {type(item).__name__})"
        )
        if kind not in seen:
            seen.append(kind)
    # Same rule as `_describe_keys`: "(none)" means there were none, not
    # that they rendered as nothing.
    if not seen:
        return "(none)"
    return _safe(", ".join(seen), held=held) or "(types are blank)"


def _reason_clause(
    container: object, field: str, *, held: HeldKeys,
) -> str:
    """`; <field>=<value>` when *container* carries one, else "".

    `stop_reason` (Anthropic) and `finish_reason` (OpenAI-style) are what
    distinguish "the model chose to say nothing" from "the reply was cut
    off before it got to the text" — a thinking-only response that hits
    the request's max_tokens is a budget problem, not a malformed
    provider, and the reader cannot act without knowing which they have.

    Returns "" when the field is absent so a provider that omits it
    produces a clean message rather than a dangling `=None`.  The value
    is bounded: it is provider-supplied text like any other.
    """
    if not isinstance(container, dict):
        return ""
    value = container.get(field)
    if value is None or value == "":
        return ""
    # Rendered first: a whitespace-only value is PRESENT, so the clause
    # stays and says the value was blank, rather than being dropped (which
    # would read as absent) or left dangling as `; stop_reason=`.
    return f"; {field}={_or_blank(_safe(str(value), held=held))}"


#: Reason values under which an EMPTY completion is a failure rather than a
#: value the model produced.  `refusal` says the model declined; `max_tokens`
#: (Anthropic) and `length` (OpenAI-style) say the provider cut the reply off
#: before it reached any text — the #1333 species exactly, a thinking block
#: exhausting the request's budget.  Under `end_turn` / `stop` / no reason at
#: all an empty completion is a value the model chose to give, and stays
#: `Ok("")`.
_EMPTY_COMPLETION_FAILURES = ("refusal", "max_tokens", "length")


def _empty_completion_error(
    text: str,
    container: object,
    field: str,
    provider: str,
    model: str,
    *,
    held: HeldKeys,
) -> InferenceError | None:
    """The error for an empty completion the provider itself explained, or None.

    Returning `Ok("")` for a reply the provider says it truncated hands the
    caller an answer the model never finished, with the one field that said
    so discarded — the same shape as #1333's original defect, one turn
    later.  Symmetric across both branches, since both spell the signal
    differently and neither is more authoritative than the other.

    Scoped deliberately: only an EMPTY (or whitespace-only) completion is
    affected.  A non-empty reply under `max_tokens` / `length` is returned
    unchanged — truncated-but-present output is still the model's answer,
    and refusing it would be a behaviour change well beyond this fix.
    """
    if text.strip():
        return None
    reason = container.get(field) if isinstance(container, dict) else None
    # Case-insensitive on the COMPARISON only: every registered provider
    # emits these lowercase today, but the value is a wire field and a
    # gateway is free to normalise it differently — `MAX_TOKENS` falling
    # through to `Ok("")` would lose the answer for a spelling difference.
    # The token is still rendered exactly as received, so the diagnostic
    # reports what the provider actually sent.
    if (
        not isinstance(reason, str)
        or reason.lower() not in _EMPTY_COMPLETION_FAILURES
    ):
        return None
    return InferenceError(
        f"Inference provider '{provider}' ({model}) returned an empty "
        f"completion{_reason_clause(container, field, held=held)}.",
    )


def _missing_or_wrong(
    container: object,
    field: str,
    expected: str,
    where: str = "response",
    *,
    held: HeldKeys,
) -> str:
    """Why *field* is unusable on *container*: absent, or the wrong type.

    Collapsing the two produced messages that contradicted themselves —
    `{"content": "Positive"}` reported "no 'content' list in the
    response; response keys: content", naming the key it had just said
    was missing.  Absent and present-but-wrong-typed are different
    faults with different fixes, so they read differently.

    *where* names the object being described, because these fields do not
    all hang off the response: `message` hangs off a CHOICE, and a
    message saying "in the response" while listing the choice's keys is
    the same self-contradiction one level down.
    """
    if not isinstance(container, dict):
        return f"the {where} is {type(container).__name__}, not an object"
    if field not in container:
        return (
            f"no '{field}' {expected} in the {where}; "
            f"{where} keys: {_describe_keys(container, held=held)}"
        )
    article = "an" if expected[:1].lower() in "aeiou" else "a"
    return (
        f"'{field}' is {type(container[field]).__name__}, "
        f"not {article} {expected}"
    )


#: The part discriminators the OpenAI-style branch accepts.  The
#: Responses API and the gateways that mirror it spell a text part
#: `output_text`; those worked on v0.1.12 because the old code read
#: `content` positionally and never looked at `type` at all, so selecting
#: by type alone would have regressed them.
_OPENAI_TEXT_TYPES = ("text", "output_text")


def _text_fragments(
    items: list[object],
    provider: str,
    model: str,
    kind: str,
    discriminators: tuple[str, ...] = ("text",),
    *,
    held: HeldKeys,
) -> list[str]:
    """Every text entry's text, in order, as strings.

    The `str()` this replaced was a silent-wrong-answer generator of
    exactly the kind #1333 exists to close, one level deeper than the
    `content: null` case fixed with it: a selected text block whose
    `text` is `null` coerced to the string `"None"` and reached the Vera
    program as a SUCCESSFUL completion, and a `text` holding an object
    reached it as a Python repr.  A response the provider did not fill
    in is a refusal to report, never a value to stringify.

    A selected entry with NO `text` key is refused on the same footing.
    It was skipped once, which made two malformed shapes behave
    differently for no reason a caller could see: `[{"type": "text"},
    {"type": "text", "text": "Positive"}]` returned `Ok("Positive")`
    while the same pair with `"text": null` refused.  Both are a
    provider failing to fill in a block it typed as text.
    """
    fragments: list[str] = []
    for item in items:
        if not isinstance(item, dict) or item.get("type") not in discriminators:
            continue
        if "text" not in item:
            raise InferenceError(
                f"Inference provider '{provider}' ({model}) returned a "
                f"{kind} with no 'text' field "
                f"(keys: {_describe_keys(item, held=held)}).",
            )
        value = item["text"]
        if not isinstance(value, str):
            raise InferenceError(
                f"Inference provider '{provider}' ({model}) returned a "
                f"{kind} whose text is {type(value).__name__}, not a "
                f"string.",
            )
        fragments.append(value)
    return fragments


def _error_body_detail(raw: bytes, *, held: HeldKeys) -> str:
    """The provider's own message out of an HTTP error body.

    Anthropic and every OpenAI-compatible provider spell a rejection as
    ``{"error": {"message": ...}}``, so one extraction serves both
    families.  Anything else — an HTML proxy page, an empty body — falls
    back to the raw text, truncated.  Decoded with ``errors="replace"``
    because a non-UTF-8 error body must still produce an error message
    rather than a second, unrelated failure.

    Everything returned is redacted BEFORE it is truncated: a key clipped
    in half would leave a recognisable prefix in the message, which is
    most of what makes a leaked credential useful to a reader.
    """
    import json as _json

    text = raw.decode("utf-8", errors="replace")
    if not text.strip():
        return "(empty response body)"

    try:
        parsed = _json.loads(text)
    except ValueError:
        return _safe(text, held=held)
    if isinstance(parsed, dict):
        err = parsed.get("error")
        if isinstance(err, dict) and isinstance(err.get("message"), str):
            return _safe(str(err["message"]), held=held)
        if isinstance(err, str) and err:
            return _safe(err, held=held)
        if isinstance(parsed.get("message"), str):
            return _safe(str(parsed["message"]), held=held)
    return _safe(text, held=held)


def _character_cut(raw: bytes, cap: int) -> int:
    """Where to cut *raw*, which holds a byte past *cap*, so that the cap
    does not split a UTF-8 character (#1526).

    The cut moves only for a character the cap leaves incomplete: walk back
    from the cap over at most two continuation bytes to the byte that
    begins the sequence, read the length it declares (``C0``-``DF`` two,
    ``E0``-``EF`` three, ``F0``-``F7`` four), and cut at that byte when the
    sequence ends past the cap.  Every other case stays at the cap, as it
    was: a character that ends at the cap, a stray continuation byte (a
    configured key that ends just before it stays whole), no beginning
    within three bytes, a byte that begins no sequence.
    """
    if raw[cap] & 0xC0 != 0x80:
        return cap
    lead = cap - 1
    for _ in range(2):  # pragma: no mutate — equivalent: a fourth byte back is the start of a sequence that ends at or before the cap
        if raw[lead] & 0xC0 == 0x80:
            lead -= 1
    first = raw[lead]
    if 0xC0 <= first <= 0xDF:
        length = 2
    elif 0xE0 <= first <= 0xEF:
        length = 3
    elif 0xF0 <= first <= 0xF7:
        length = 4  # pragma: no mutate — equivalent: a four-byte lead within three bytes of the cap is always cut by it
    else:
        return cap
    return lead if lead + length > cap else cap


def _read_error_body(http_err: HTTPError, *, held: HeldKeys) -> str:
    """The provider's error detail, read under a cap and never fatally.

    A bare `http_err.read()` pulls the WHOLE body into memory before
    `_truncate` ever sees it, so the 200-character bound on the message
    bounded only what we printed, never what we held.  One byte past the
    cap is requested so that "the body overran" stays distinguishable
    from "the body was exactly the cap".

    An overrun body is deliberately NOT parsed.  Today `json.loads`
    would reject nearly every cut body on its own — the exception is a
    short envelope padded past the cap with whitespace, which parses
    cleanly and would surface a message extracted from a body we only
    partly read.  The rule is therefore stated rather than inherited:
    having read part of a body, we do not claim to have parsed it.  That
    also survives a later switch to a prefix-tolerant parser such as
    `raw_decode`, which would otherwise start presenting fragments as
    complete with nothing to notice it.  The raw-text path is the honest
    report, and it is marked as truncated unconditionally: the marker
    records that the read stopped at the cap, which stays true however
    short the retained text turns out to be.

    The read itself can fail: a socket already closed raises rather than
    returning bytes.  Losing the detail is a much smaller loss than
    losing the provider name and the status code to a second, unrelated
    exception, so it is guarded and degrades to a stated placeholder.
    """
    if getattr(http_err, "fp", None) is None:
        return "(empty response body)"
    try:
        raw = http_err.read(_ERROR_BODY_CAP + 1)
    except Exception:  # noqa: BLE001 — the detail is optional; the provider and status code are not
        return "(unreadable response body)"
    if len(raw) > _ERROR_BODY_CAP:
        cut = _character_cut(raw, _ERROR_BODY_CAP)
        head =raw[:cut].decode("utf-8", errors="replace")  # pragma: no mutate — equivalent: utf-8 is the default codec, and codec names are case-insensitive
        # #1854: redacted at the cut, before it is stripped, so a secret the
        # cap split is read where it was split.  Marked unconditionally,
        # because the marker states a fact about the READ — we stopped at
        # the cap — and not about the length of whatever survived
        # stripping.  `_truncate` marks on length alone, so a short envelope
        # padded past the cap with whitespace strips back under the bound
        # and would be reported as if complete.
        redacted = _redact_cut(head, held=held).strip()
        return redacted[:_ERROR_BODY_CHARS] + "... (truncated)"
    return _error_body_detail(raw, held=held)


def _refuse_unsendable_key(
    provider: str, model: str, cfg: _ProviderConfig, api_key: str,
) -> None:
    """Refuse a key an HTTP header cannot carry, by the variable that holds
    it (#1854).

    A line end (as a key read from a file written with CRLF line ends
    holds), another control character, or a character outside ASCII.  Sent
    on, `http.client` refused the header with an exception whose message
    quotes the whole header value, key and all, and that message reached
    the `Err`.  The refusal names the variable and quotes nothing of the
    key.
    """
    if any(not 0x20 <= ord(ch) < 0x7F for ch in api_key):
        raise InferenceError(
            f"Inference provider '{provider}' ({model}): {cfg.env_key} "
            f"holds a character an HTTP header cannot carry (a line end, "
            f"another control character, or one outside ASCII). Set it to "
            f"the key alone.",
        )


def _call_inference_provider(
    provider: str,
    prompt: str,
    model: str,
    api_key: str,
    *,
    held: HeldKeys,
) -> str:
    """Dispatch a completion request to the configured LLM provider.

    Looks up *provider* in ``_PROVIDERS``, builds the appropriate request,
    and returns the completion string.  Raises on network or API errors;
    the caller wraps the result in Ok/Err and writes it to WASM memory.
    """
    import json as _json
    import urllib.error as _urlerr
    import urllib.request as _urlreq

    cfg = _PROVIDERS.get(provider)
    if cfg is None:
        valid = ", ".join(sorted(_PROVIDERS))
        raise InferenceError(
            f"Unknown inference provider '{provider}'. "
            f"Valid values: {valid}."
        )

    chosen_model = model or cfg.default_model

    _refuse_unsendable_key(provider, chosen_model, cfg, api_key)

    if cfg.auth_style == "anthropic":
        headers = {
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        }
        body = _json.dumps({
            "model": chosen_model,
            "max_tokens": 1024,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")
    else:  # bearer
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        }
        body = _json.dumps({
            "model": chosen_model,
            "messages": [{"role": "user", "content": prompt}],
        }).encode("utf-8")

    req = _urlreq.Request(cfg.url, data=body, headers=headers, method="POST")  # noqa: S310
    try:
        with _urlreq.urlopen(req, timeout=_HTTP_TIMEOUT) as resp:  # noqa: S310
            raw = resp.read()
            # #591 — strict-mode `.decode("utf-8")` previously leaked
            # the raw `UnicodeDecodeError` message (including byte
            # offsets and Python-internals jargon) into the
            # `Result::Err` string the user sees from
            # `Inference.complete`.  An LLM-API response that isn't
            # valid UTF-8 is genuinely broken — we want to fail loudly
            # but with a Vera-native message, not Python noise.
            try:
                decoded = raw.decode("utf-8")
            except UnicodeDecodeError as ude:
                raise InferenceError(
                    f"Inference provider '{provider}' ({chosen_model}) "
                    f"returned a response body that is not valid UTF-8 "
                    f"(invalid byte at position {ude.start}).",
                ) from None
    except _urlerr.HTTPError as http_err:
        # #1333 — an unhandled HTTPError escaped as urllib's own
        # `HTTP Error 401: Unauthorized`, which names neither the
        # provider that rejected the request nor the reason it gave.
        # The status line is the least useful half of what the API
        # actually sent back.
        detail = _read_error_body(http_err, held=held)
        raise InferenceError(
            f"Inference provider '{provider}' ({chosen_model}) rejected "
            f"the request: HTTP {http_err.code}: {detail}",
        ) from None

    try:
        data = _json.loads(decoded)
    except ValueError:
        # A gateway or proxy answering 200 with an HTML page.  Caught
        # here rather than at the host boundary because
        # `json.JSONDecodeError` is a `ValueError` SUBCLASS, and the
        # boundary's pass-through is what keeps this module's own
        # messages verbatim — see `register_inference`.
        raise InferenceError(
            f"Inference provider '{provider}' ({chosen_model}) returned a "
            f"response body that is not JSON: "
            f"{_or_blank(_safe(decoded, held=held))}",
        ) from None

    # #1333 — select the completion by SHAPE, never by position.  The
    # Anthropic Messages API returns `content` as a list of *typed*
    # blocks, and a reasoning-capable flagship can lead with a
    # `thinking` block; `content[0]["text"]` therefore raised
    # `KeyError('text')`, which the host boundary stringified into the
    # Err payload `'text'`.  The OpenAI-style branch gets the same
    # treatment: `message.content` is a string on an ordinary turn, a
    # list of typed parts on some multimodal ones, and `null` on a
    # reasoning/tool-call turn — where the old `str(...)` produced the
    # literal completion `"None"`, a silent wrong answer.
    if cfg.response_style == "anthropic":
        content = data.get("content") if isinstance(data, dict) else None
        if not isinstance(content, list):
            # `stop_reason` on THIS branch too: a response whose content
            # is null but which stopped at `end_turn` was dropping the one
            # field that explained it.
            raise InferenceError(
                f"Inference provider '{provider}' ({chosen_model}) returned "
                f"no text block ({_missing_or_wrong(data, 'content', 'list', held=held)}"
                f"{_reason_clause(data, 'stop_reason', held=held)}).",
            )
        texts = _text_fragments(
            content, provider, chosen_model, "text block", held=held,
        )
        if not texts:
            raise InferenceError(
                f"Inference provider '{provider}' ({chosen_model}) returned "
                f"no text block (content block types: "
                f"{_describe_types(content, held=held)}"
                f"{_reason_clause(data, 'stop_reason', held=held)}).",
            )
        # Joined without a separator: consecutive text blocks are
        # fragments of one message, so concatenation reconstructs
        # exactly what the model emitted.
        joined = "".join(texts)
        empty_error = _empty_completion_error(
            joined, data, "stop_reason", provider, chosen_model, held=held,
        )
        if empty_error is not None:
            raise empty_error
        return joined

    # openai-style
    choices = data.get("choices") if isinstance(data, dict) else None
    if not isinstance(choices, list) or not choices:
        detail = (
            "the 'choices' list is empty"
            if isinstance(choices, list)
            else _missing_or_wrong(data, "choices", "list", held=held)
        )
        raise InferenceError(
            f"Inference provider '{provider}' ({chosen_model}) returned no "
            f"completion text ({detail}).",
        )

    first = choices[0]
    # Read off the choice, not the response: `finish_reason` is the
    # OpenAI-style analogue of `stop_reason`, and it is what says a reply
    # was cut at the token budget rather than withheld.
    finish = _reason_clause(first, "finish_reason", held=held)
    if not isinstance(first, dict):
        raise InferenceError(
            f"Inference provider '{provider}' ({chosen_model}) returned no "
            f"completion text (the first choice is "
            f"{type(first).__name__}, not an object).",
        )
    message = first.get("message")
    if not isinstance(message, dict):
        raise InferenceError(
            f"Inference provider '{provider}' ({chosen_model}) returned no "
            f"completion text ("
            f"{_missing_or_wrong(first, 'message', 'object', 'choice', held=held)}"
            f"{finish}).",
        )

    def _refusal_or(detail: str) -> InferenceError:
        """A refusal turn explains itself; anything else reports the shape.

        `message.refusal` is the OpenAI-style spelling of "the model
        declined", and it is the ANSWER — surfacing the shape of an empty
        content field instead would describe the symptom and discard the
        cause.  Truncated and redacted like any other provider text.
        """
        refusal = message.get("refusal")
        if isinstance(refusal, str) and refusal.strip():
            return InferenceError(
                f"Inference provider '{provider}' ({chosen_model}) refused "
                f"the request: {_safe(refusal, held=held)}{finish}",
            )
        return InferenceError(
            f"Inference provider '{provider}' ({chosen_model}) returned no "
            f"completion text ({detail}{finish}).",
        )

    def _completion_or_refusal(text: str) -> str:
        """An empty completion is a VALUE — unless the turn also refused.

        A model may legitimately answer with the empty string, and that
        has been `Ok("")` since v0.1.12; changing it would be a
        behaviour change with nothing to do with #1333.  But when the
        turn carries a `refusal` beside empty content, the refusal is
        the answer and `Ok("")` discards it — the caller is told the
        model said nothing when it said why it would not.
        """
        if text.strip():
            return text
        refusal = message.get("refusal")
        if isinstance(refusal, str) and refusal.strip():
            raise _refusal_or("the completion was empty")
        # `finish_reason` is the other half of the same rule, and lives on
        # the CHOICE rather than the message.
        empty_error = _empty_completion_error(
            text, first, "finish_reason", provider, chosen_model, held=held,
        )
        if empty_error is not None:
            raise empty_error
        return text

    content = message.get("content")
    if isinstance(content, str):
        return _completion_or_refusal(content)
    if isinstance(content, list):
        # One discriminator at a time, in preference order.  A gateway
        # that mirrors BOTH spellings of the same reply — the shim shape
        # — has each fragment twice, and scanning the union concatenated
        # them into `PositivePositive`: a wrong answer returned as a
        # success, which is this family's defect once more.  The first
        # discriminator that yields anything wins, so the other spelling
        # is never consulted rather than merged.
        parts: list[str] = []
        joined = ""
        # The FIRST discriminator that produced fragments at all, which
        # `parts` cannot answer: it holds only the last discriminator's
        # result, so a hit under `text` was erased by the empty list under
        # `output_text` and a legitimate blank answer became an error.
        first_result: str | None = None
        for _discriminator in _OPENAI_TEXT_TYPES:
            parts = _text_fragments(
                content, provider, chosen_model, "text part",
                (_discriminator,), held=held,
            )
            if parts and first_result is None:
                first_result = "".join(parts)
            joined = "".join(parts)
            # A hit is a result with TEXT in it, tested the same way
            # `_completion_or_refusal` tests it.  Truthiness was the
            # wrong test twice over: `[""]` counted as a hit, and so did
            # `["   "]`, so a whitespace-only `text` part short-circuited
            # the loop and both shadowed a real `output_text` part and
            # skipped the refusal check the string form applied.
            if joined.strip():
                break
        if joined.strip():
            return joined
        if first_result is not None:
            # Every discriminator yielded only blank fragments.  That may
            # be a genuinely blank completion — `_completion_or_refusal`
            # applies the refusal and truncation rules and otherwise
            # returns it unchanged.
            return _completion_or_refusal(first_result)
        raise _refusal_or(
            f"no text parts in the message content; "
            f"part types: {_describe_types(content, held=held)}"
        )
    raise _refusal_or(
        _missing_or_wrong(
            message, "content", "string or list of parts", "message", held=held,
        )
    )


def register_inference(
    linker: wasmtime.Linker,
    ops_used: set[str],
    env_vars: dict[str, str] | None,
) -> None:
    """Register the requested Inference host functions on `linker`."""
    if "inference_complete" in ops_used:
        def host_inference_complete(
            caller: wasmtime.Caller, ptr: int, length: int,
        ) -> int:
            import os as _os

            prompt = _read_wasm_string(caller, ptr, length)
            _env = env_vars if env_vars is not None else _os.environ
            held = _held_keys(_env)

            def _err(text: str) -> int:
                """The `Err` of `Inference.complete`: the one exit of its
                text, redacted of every key the host holds (#1854).

                Every message leaves here, whichever input put the key in
                it: the model name, the provider name, an exception's text,
                a provider's body.  The redaction before each cut (`_safe`,
                `_read_error_body`) stays as well, because the two catch
                different texts: a cut can leave a fragment of a key that
                no longer reads as the key here, and this catches a text
                that never passed a cut."""
                return _alloc_result_err_string(
                    caller, _redact(text, held=held))

            provider = _env.get("VERA_INFERENCE_PROVIDER", "").lower()

            # Auto-detect provider from whichever key holds a NON-EMPTY
            # value — the truthiness test below skips a variable exported
            # as the empty string, as if it were unset — respecting
            # registry insertion order (anthropic first).
            if not provider:
                for _pname, _pcfg in _PROVIDERS.items():
                    if _env.get(_pcfg.env_key, ""):
                        provider = _pname
                        break

            if not provider:
                key_vars = ", ".join(
                    c.env_key for c in _PROVIDERS.values()
                )
                return _err(
                    f"No inference provider configured. "
                    f"Set {key_vars}.",
                )

            cfg = _PROVIDERS.get(provider)
            api_key = _env.get(cfg.env_key, "") if cfg else ""

            if cfg is not None and not api_key:
                return _err(
                    f"Inference provider '{provider}' selected but "
                    f"{cfg.env_key} is not set.",
                )

            model = _env.get("VERA_INFERENCE_MODEL", "")
            # Resolved here, not inside the call, so the label below can
            # name it: spec 9.5.5 promises every provider-backed Err names
            # the provider AND the model, and a transport failure
            # (URLError, TimeoutError, ConnectionRefusedError) never
            # reaches the code that knew which model was asked for.
            resolved_model = model or (cfg.default_model if cfg else "unknown")
            try:
                completion = _call_inference_provider(
                    provider, prompt, model, api_key, held=held,
                )
                return _alloc_result_ok_string(caller, completion)
            except Exception as exc:  # noqa: BLE001 — host boundary; any failure becomes Result.Err
                # #1333 — the Err payload is a Vera-level value, so a
                # bare `str(exc)` publishes whatever Python spelling the
                # failure happened to have: a `KeyError('text')` from the
                # response parse reached the user as the entire message
                # `'text'`, naming neither the operation nor the provider.
                #
                # The verbatim channel belongs to `InferenceError` and
                # nothing else.  Testing for plain `RuntimeError` /
                # `ValueError` (the #1333 review's finding) let ANY
                # failure of those types claim it — a `RuntimeError`
                # raised deep in the transport reached the user as its
                # own bare message, which is this family's defect one
                # level up.  A dedicated class cannot be raised by
                # accident.
                #
                # `isinstance` rather than an exact-type test: the hazard
                # that forced exactness was the stdlib subclassing the
                # types we checked for (`json.JSONDecodeError` IS a
                # `ValueError`).  Nothing outside this module subclasses
                # `InferenceError`, so any subclass is by construction one
                # of ours and carries a message written for a user.
                if isinstance(exc, InferenceError):
                    return _err(str(exc))
                # #1854: an exception's text is text from outside, as a
                # provider's is: the transport's own messages quote what
                # they were handed (a header value, a URL), so it is
                # redacted and bounded like any other.
                return _err(
                    f"Inference provider '{provider}' ({resolved_model}) "
                    f"failed: "
                    f"{_safe(f'{type(exc).__name__}: {exc}', held=held)}",
                )

        linker.define_func(
            "vera", "inference_complete",
            wasmtime.FuncType(
                [wasmtime.ValType.i32(), wasmtime.ValType.i32()],
                [wasmtime.ValType.i32()],
            ),
            host_inference_complete, access_caller=True,
        )
