"""An HTTP error body cut at the read cap is cut at a character (#1526).

`vera.runtime.inference._read_error_body` reads at most `_ERROR_BODY_CAP`
bytes of a provider's error body and quotes the head of what it read.  The
cut is a byte count, so a multi-byte character straddling the cap ended the
quoted text in U+FFFD.  The cut backs up to a character boundary (at most
three bytes) before the text is decoded; bytes that are not UTF-8 elsewhere
in the body are still replaced.

The class (with the entry-point boundary's 64-byte cut, tests/
test_exn_boundary_cut_1526.py): every cut of UTF-8 text by a byte count.
This matrix crosses the character's width (2, 3, 4 bytes) with how many of
its bytes lie before the cap (every straddling count, and all of them).
"""
from __future__ import annotations

import email.message
import io
import urllib.error

import pytest

from vera.runtime.inference import (
    _ERROR_BODY_CAP,
    _character_cut,
    _read_error_body,
)

pytestmark = pytest.mark.matrix(decides=["vera/runtime/inference.py"])

CHARACTERS = {2: "é", 3: "€", 4: "😀"}
MARKER = "... (truncated)"


def _error(body: bytes) -> urllib.error.HTTPError:
    return urllib.error.HTTPError(
        url="https://example.invalid", code=500, msg="x",
        hdrs=email.message.Message(), fp=io.BytesIO(body))


def _body(char: str, before_cap: int, tail: bytes = b"") -> bytes:
    """Spaces, then *char* with *before_cap* of its bytes before the cap,
    then *tail*; the spaces strip away, so the quoted head is the
    character's."""
    raw = char.encode("utf-8")
    return b" " * (_ERROR_BODY_CAP - before_cap - 3) + b"xyz" + raw + tail


CELLS = [(w, j) for w in CHARACTERS for j in range(1, w + 1)]


@pytest.mark.parametrize("cell", CELLS, ids=lambda c: f"{c[0]}byte-{c[1]}before")
def test_the_cut_never_leaves_half_a_character(cell: tuple[int, int]) -> None:
    width, before = cell
    char = CHARACTERS[width]
    detail = _read_error_body(_error(_body(char, before, b"tail" * 4)))
    assert "�" not in detail, detail
    assert detail.endswith(MARKER), detail
    # The character is quoted when all of its bytes fit under the cap and
    # not at all when the cut would split it.
    assert (char in detail) == (before >= width), detail
    # Nothing before the character is lost: the back-up stops at its first byte.
    assert detail.startswith("xyz"), detail


def test_repro_a_two_byte_character_straddling_the_cap() -> None:
    detail = _read_error_body(_error(_body("é", 1, b"abc")))
    assert "�" not in detail, detail


def test_a_body_exactly_at_the_cap_is_whole() -> None:
    """Negative space: nothing is cut, so nothing is backed up."""
    body = _body("é", 2)
    assert len(body) == _ERROR_BODY_CAP
    detail = _read_error_body(_error(body))
    assert detail == "xyzé", detail


@pytest.mark.parametrize("cell", CELLS, ids=lambda c: f"{c[0]}byte-{c[1]}before")
def test_a_configured_key_before_the_cut_stays_redacted(
    cell: tuple[int, int],
) -> None:
    """The text the back-up leaves is still redacted: with `xyz` the
    configured key and sitting just before the straddling character, the
    quoted detail holds no `xyz`."""
    width, before = cell
    body = _body(CHARACTERS[width], before, b"tail" * 4)
    detail = _read_error_body(_error(body), "xyz")
    assert "xyz" not in detail, detail
    assert detail.endswith(MARKER), detail


def test_no_key_configured_redacts_nothing() -> None:
    """The default `api_key` is empty: a capped body that holds `XXXX` is
    quoted as it is."""
    body = b"XXXX abc" + b" " * _ERROR_BODY_CAP + b"tail"
    detail = _read_error_body(_error(body))
    assert detail == "XXXX abc" + MARKER, detail


def test_an_unreadable_body_is_stated() -> None:
    class Unreadable(io.BytesIO):
        def read(self, size: int | None = -1) -> bytes:
            raise OSError("closed")

    err = urllib.error.HTTPError(
        url="https://example.invalid", code=500, msg="x",
        hdrs=email.message.Message(), fp=Unreadable(b""))
    assert _read_error_body(err) == "(unreadable response body)"


def test_a_byte_that_is_not_utf_8_is_still_replaced() -> None:
    """Negative space: the back-up moves the cut, it does not change what
    the decoder does with bytes that are not UTF-8."""
    body = b"\xff abc" + b" " * _ERROR_BODY_CAP + b"tail"
    detail = _read_error_body(_error(body))
    assert detail.startswith("� abc"), detail
    assert detail.endswith(MARKER), detail



# --- The rule: only a character the cap leaves incomplete moves the cut ----

CAP = _ERROR_BODY_CAP


def _at_cap(before: bytes, after: bytes) -> bytes:
    """Spaces, then *before*, ending at the cap, then *after* (from the cap
    on)."""
    return b" " * (CAP - len(before)) + before + after


def _kept(body: bytes) -> bytes:
    """The bytes of *body* the cut keeps."""
    return body[:_character_cut(body, CAP)]


@pytest.mark.parametrize(("lead", "length"), [
    (0xC0, 2), (0xDF, 2), (0xE0, 3), (0xEF, 3), (0xF0, 4), (0xF7, 4),
], ids=hex)
def test_a_sequence_the_cap_leaves_incomplete_is_cut_at_its_lead(
    lead: int, length: int,
) -> None:
    """The lead sits `length - 1` bytes before the cap: the sequence ends
    one byte past it, so the cut moves to the lead."""
    start = CAP - (length - 1)
    body = (b" " * start + bytes([lead]) + b"\x80" * (length - 1)
            + b"tail")
    assert _character_cut(body, CAP) == start


@pytest.mark.parametrize(("lead", "length"), [
    (0xC0, 2), (0xDF, 2), (0xE0, 3), (0xEF, 3), (0xF0, 4), (0xF7, 4),
], ids=hex)
def test_a_sequence_that_ends_at_the_cap_stays_whole(
    lead: int, length: int,
) -> None:
    """The lead sits `length` bytes before the cap, so the sequence is
    complete at the cap and a stray continuation byte after it moves
    nothing."""
    body = (b" " * (CAP - length) + bytes([lead]) + b"\x80" * (length - 1)
            + b"\x80tail")
    assert _character_cut(body, CAP) == CAP


@pytest.mark.parametrize("byte", [0x00, 0x41, 0x7F, 0xC0, 0xE2, 0xFF],
                         ids=hex)
def test_a_cap_that_falls_on_a_non_continuation_byte_stays(byte: int) -> None:
    body = b" " * (CAP - 1) + b"\xc3" + bytes([byte]) + b"tail"
    assert _character_cut(body, CAP) == CAP


@pytest.mark.parametrize("byte", [0x7F, 0xF8, 0xFF, 0x41], ids=hex)
def test_a_byte_that_begins_no_sequence_is_not_a_lead(byte: int) -> None:
    body = b" " * (CAP - 1) + bytes([byte]) + b"\x80tail"
    assert _character_cut(body, CAP) == CAP


def test_a_stray_run_of_continuation_bytes_stays_at_the_cap() -> None:
    body = _at_cap(b"xyz" + b"\x80" * 4, b"\x80\x80tail")
    assert _character_cut(body, CAP) == CAP
    detail = _read_error_body(_error(body))
    assert detail.startswith("xyz�"), detail


def test_a_lead_four_bytes_back_is_out_of_reach() -> None:
    """A four-byte sequence's last continuation byte is at lead + 3, so a
    lead four bytes before the cap has ended: it is not looked for."""
    body = (b" " * (CAP - 4) + b"\xf0\x80\x80\x80" + b"\x80tail")
    assert _character_cut(body, CAP) == CAP


KEY = "A" * 40


def test_a_key_before_a_stray_continuation_byte_is_redacted_whole() -> None:
    """CodeRabbit's case: the key ends at the cap and a stray `0x80`
    follows.  The cut stays, the key is redacted, and no fragment of it
    reaches the message (the cut dropped its last character before)."""
    body = _at_cap(KEY.encode("utf-8"), b"\x80tail")
    assert _kept(body).endswith(KEY.encode("utf-8"))
    detail = _read_error_body(_error(body), KEY)
    assert "AAAA" not in detail, detail


def test_a_complete_character_before_a_stray_byte_is_kept() -> None:
    body = _at_cap("xyzé".encode("utf-8"), b"\x80tail")
    assert _kept(body).endswith("é".encode("utf-8"))
    assert _read_error_body(_error(body)) == "xyzé" + MARKER


def test_a_key_ending_in_a_character_at_the_cap_is_redacted_whole() -> None:
    key = "kéy-é"
    body = _at_cap(("xyz" + key).encode("utf-8"), b"\x80tail")
    detail = _read_error_body(_error(body), key)
    assert key not in detail and "é" not in detail, detail
    assert detail.startswith("xyz"), detail


def test_the_cut_keeps_what_base_keeps_less_one_incomplete_character() -> None:
    """The property over the matrix's cells: the bytes kept are the first
    `cap` bytes, or those before the lead of a sequence the cap cuts."""
    for char in CHARACTERS.values():
        raw = char.encode("utf-8")
        for before in range(0, len(raw) + 1):
            body = (b" " * (CAP - 3 - before) + b"xyz" + raw + b"tail")
            lead = CAP - before
            kept = _kept(body)
            incomplete = 0 < before < len(raw)
            assert kept == (body[:lead] if incomplete else body[:CAP]), (
                char, before)


def test_find_a_key_straddling_the_cap_leaves_its_first_half() -> None:
    """A FIND, not a fix: at base a configured key whose first half sits
    before the cap and whose second half is past it is cut in two, and the
    first half is quoted.  Exact-key redaction cannot match half a key."""
    key = "K" * 40
    body = _at_cap(b"K" * 20, b"K" * 20 + b"tail")
    detail = _read_error_body(_error(body), key)
    assert "K" * 20 in detail, detail
