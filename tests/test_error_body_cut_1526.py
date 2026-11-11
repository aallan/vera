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

from vera.runtime.inference import _ERROR_BODY_CAP, _read_error_body

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


def test_a_byte_that_is_not_utf_8_is_still_replaced() -> None:
    """Negative space: the back-up moves the cut, it does not change what
    the decoder does with bytes that are not UTF-8."""
    body = b"\xff abc" + b" " * _ERROR_BODY_CAP + b"tail"
    detail = _read_error_body(_error(body))
    assert detail.startswith("� abc"), detail
    assert detail.endswith(MARKER), detail


@pytest.mark.parametrize(("byte", "backs_up"), [
    (0x41, False), (0x7F, False), (0x80, True), (0xBF, True), (0xC0, False),
    (0xE2, False),
], ids=lambda v: hex(v) if isinstance(v, int) else str(v))
def test_only_a_continuation_byte_moves_the_cut(
    byte: int, backs_up: bool,
) -> None:
    """The byte at the cut decides: 0x80 to 0xBF backs the cut up one byte
    (dropping the `z` before it), any other byte leaves it."""
    body = b" " * (_ERROR_BODY_CAP - 3) + b"xyz" + bytes([byte]) + b"tail"
    detail = _read_error_body(_error(body))
    assert detail == ("xy" if backs_up else "xyz") + MARKER, detail


def test_the_cut_backs_up_three_bytes_and_no_further() -> None:
    """A run of stray continuation bytes (not UTF-8 at all) across the cap:
    the back-up is bounded by the longest character, so it stops three
    bytes up and the text before the run is kept."""
    body = (b" " * (_ERROR_BODY_CAP - 6) + b"xyz" + b"\x80" * 6 + b"tail")
    assert body[_ERROR_BODY_CAP - 3] == 0x80
    detail = _read_error_body(_error(body))
    assert detail == "xyz" + MARKER, detail
